module Logic
  ( logicEntry,
    AnalysisError (..),
    PureExp (..),
  )
where

import AST
import Control.Lens (has, hasn't)
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable (traverse_)
import Data.List (tails)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust, isNothing)
import Data.SBV.Dynamic (SVal)
import Data.SBV.Internals (SBV (SBV), unSBV)
import Data.SBV.String ((.++))
import Data.SBV.Trans

-- import Debug.Trace (trace)

data SVar
  = Boolean SBool
  | Numeric SInteger
  | Str SString
  | Flt SFloat
  | Rational SReal
  | Lst [SVar]
  | Custom String
  | Future SVar
  | WhileBound SBool
  | Null
  | FnRet
  deriving (Show, Eq)

type VarTable = Map String (Map String SVar)

type Constraint = ExceptT AnalysisError (State VarTable)

type Model = SymbolicT (ExceptT AnalysisError IO)

data AnalysisError
  = AwaitError String
  | SyncError String
  | UnsupportedType String
  | Other String
  deriving (Show)

-- | General logic
-- decs are only class decls
logicEntry :: [Decl] -> [(String, Method, Method, IO (Either AnalysisError ThmResult))]
logicEntry decs = do
  dec <- decs
  -- Could the map of variables and fields be created here?
  met <- pairs $ classMethods dec
  pure $ generate dec met

-- >>> pairs ["a", "b", "c"]
-- [("a","a"),("a","b"),("a","c"),("b","b"),("b","c"),("c","c")]
--
pairs :: [a] -> [(a, a)]
pairs xs = do
  (t : ts) <- tails xs
  r <- t : ts -- Will also pair each method with itself
  pure (t, r)

-- | Initialize the state -> Set each field to its respective
-- symbolic variable. The fields in a class are shared between
-- all methods in the class.
--
-- Need to differentiate between datatypes and interface references
initialize :: Decl -> Model (Map String SVar)
initialize (ClassDecl _ params fields _) =
  initParams $ filter (hasn't _Custom . paramType) (params <> map fieldToParam fields)
  where
    fieldToParam (FieldDecl name ty _) = Param name ty

initParams :: [Param] -> Model (Map String SVar)
initParams = go Map.empty
  where
    go mp [] = pure mp
    go mp (Param name ty : rest) =
      case ty of
        Bool -> do
          sb <- sBool name
          go (Map.insert name (Boolean sb) mp) rest
        Int -> do
          si <- sInteger name
          go (Map.insert name (Numeric si) mp) rest
        AST.Custom s -> do
          let new = Logic.Custom s
          go (Map.insert name new mp) rest
        Rat -> do
          sr <- sReal name
          [r, q] <- sIntegers ["r", "q"]
          constrain $ q .> 0
          constrain $ sRealToSInteger sr .== sDiv r q
          go (Map.insert name (Rational sr) mp) rest
        String -> do
          ss <- sString name
          go (Map.insert name (Str ss) mp) rest
        v -> go mp rest

-- | Run the state through two methods, in both orders,
-- and see if the set of possible vales for each variable is
-- identical.
generate :: Decl -> (Method, Method) -> (String, Method, Method, IO (Either AnalysisError ThmResult))
generate dec met@(a, b) = (info, a, b, runExceptT $ proveWith (z3 {verbose = False}) exp)
  where
    info = "\nClass: " <> className dec <> " | (" <> methodName (fst met) <> ", " <> methodName (snd met) <> ")\n\t -> "
    exp :: Model SBool
    exp = do
      start <- Map.singleton "fields" <$> initialize dec
      amap <- initializeParams "1_" (fst met)
      bmap <- initializeParams "2_" (snd met)
      let final = start <> amap <> bmap
      run final met
    run :: VarTable -> (Method, Method) -> Model SBool
    run mp (a, b) = do
      let as = map ("1_" <> methodName a,) (statements a)
          bs = map ("2_" <> methodName b,) (statements b)
          (errA, abe) = runState (runExceptT (traverse_ generateStatement $ as <> bs)) mp
          (errB, bae) = runState (runExceptT (traverse_ generateStatement $ bs <> as)) mp
      case (errA, errB) of
        (Right (), Right ()) ->
          let about = abe Map.! "fields"
              baout = bae Map.! "fields"
           in pure . sAnd . map getBoolean . Map.elems $ Map.unionWith chkEq about baout
        (Left e, _) -> lift $ throwError e

-- | Find the parameters passed to each of the two methods, and add them into the
-- map so that they can be accessed from within the analysis.
--
-- Maybe this method should initialize a lot more:
--  - Possible return values of functions
--  - The return value of `get`-calls
initializeParams :: String -> Method -> Model VarTable
initializeParams s a = do
  stmtModel <- initStatements nameA Map.empty (statements a)
  model <- initParams (params a)
  let final = Map.union model stmtModel
  pure $ Map.singleton nameA final
  where
    nameA = s <> methodName a

mkNewVar :: String -> Type -> Model SVar
mkNewVar name ty =
  case ty of
    Int -> do
      ret <- sInteger name
      pure $ Numeric ret
    Unit -> pure . Boolean $ literal True
    Bool -> do
      sb <- sBool name
      pure . Boolean $ sb
    AST.Custom s -> do
      let new = Logic.Custom s
      pure new
    Rat -> do
      sr <- sReal name
      [r, q] <- sIntegers ["r", "q"]
      constrain $ q .> 0
      constrain $ sRealToSInteger sr .== sDiv r q
      pure $ Rational sr
    String -> do
      ss <- sString name
      pure . Str $ ss

-- | Need a new function that will traverse all the statements
-- in each method and create all the necessary free variables
initStatements :: String -> Map String SVar -> [Statement] -> Model (Map String SVar)
initStatements name mp [] = pure mp
initStatements name mp (st : rest) =
  case st of
    SkipStmt -> initStatements name mp rest
    (VarDeclStmt s t (Just (PureExp (FnApp fnName exprs)))) -> do
      let mpName = mkName mp ("FnApp" <> fnName)
      v <- mkNewVar mpName t
      initStatements name (Map.insert mpName v mp) rest
    (VarDeclStmt s t (Just (EffExp (GetExp _)))) -> do
      let mpName = "fut" <> s <> name
      v <- mkNewVar mpName t
      initStatements name (Map.insert mpName v mp) rest
    (VarDeclStmt s (Fut xs) e) -> do
      when (length xs /= 1) $ throwError $ Other "Unsupported compound type"
      unless (head xs `elem` [Unit, Int, Rat, String]) $ throwError $ Other "Unsupported compound type"
      let mpName = "fut" <> s <> name
      v <- mkNewVar s (head xs)
      initStatements name (Map.insert mpName v mp) rest
    (VarDeclStmt s t (Just exp)) -> initStatements name mp rest
    (AssignStmt (PureExp (VarUse v)) exp) -> initStatements name mp rest
    (ExprStmt ((PureExp (FnApp fnName args)))) -> do
      let argString = show args
          mapName = "FnApp" <> fnName <> argString
          t = Map.lookup fnName stdlibTypes
      when (isNothing t) $ throwError $ Other "Unsupported function"
      v <- mkNewVar mapName (fromJust t)
      initStatements name (Map.insert mapName v mp) rest
    (ExprStmt e) -> initStatements name mp rest
    AssertStmt -> initStatements name mp rest
    (AwaitStmt v) -> initStatements name mp rest
    SuspendStmt -> initStatements name mp rest
    ThrowStmt -> initStatements name mp rest
    (ReturnStmt e) -> initStatements name mp rest
    (Block st) -> do
      mp' <- initStatements name mp st
      initStatements name mp' rest
    (IfStmt co th Nothing) -> do
      mp' <- initStatements name mp th
      initStatements name mp' rest
    (IfStmt co th (Just el)) -> do
      mp' <- initStatements name mp th
      mp'' <- initStatements name mp el
      initStatements name mp'' rest
    (WhileStmt test body) -> do
      res <- initStatements name mp body
      initStatements name res rest
    _ -> initStatements name mp rest

-- There are only six functions in the Standard library?
stdlibTypes :: Map String Type
stdlibTypes =
  Map.fromList
    [ ("toString", String),
      ("substr", String),
      ("strlen", Int),
      ("println", Unit),
      ("print", Unit)
    ]

getBoolean :: SVar -> SBool
getBoolean (Boolean x) = x

chkEq :: SVar -> SVar -> SVar
chkEq (Boolean a) (Boolean b) = Boolean (a .== b)
chkEq (Numeric a) (Numeric b) = Boolean (a .== b)
chkEq (Str a) (Str b) = Boolean (a .== b)
chkEq Null Null = Boolean $ literal True
chkEq (Lst a) (Lst b) = Boolean . sAnd . map getBoolean $ zipWith chkEq a b
chkEq (WhileBound a) (WhileBound b) = Boolean $ a .|| b
-- If we cannot compare types, say false and the solver will return `Non-commuting`.
chkEq a b = Boolean $ literal False

merge :: SBool -> SVar -> SVar -> SVar
merge cond (Numeric x) (Numeric y) = Numeric $ ite cond x y
merge cond (Rational x) (Rational y) = Rational $ ite cond x y
merge cond (Boolean x) (Boolean y) = Boolean $ ite cond x y
merge cond (Logic.Custom x) (Logic.Custom _) = Logic.Custom x
merge cond (WhileBound a) (WhileBound b) = WhileBound $ ite cond a b
merge cond a b = error ("Unknown types: " <> show a <> " and " <> show b)

generateStatement :: (String, Statement) -> Constraint ()
generateStatement (name, s) = do
  case s of
    SkipStmt -> pure ()
    -- Only custom datatypes can be declared without an initial value.
    (VarDeclStmt s t Nothing) -> pure ()
    (VarDeclStmt s _ (Just exp)) -> do
      ret <- generateExp (name, exp)
      mp <- lift get
      let fs = mp Map.! name
      lift $ put $ Map.insert name (Map.insert s ret fs) mp
    (AssignStmt (PureExp (VarUse v)) exp) -> do
      ret <- generateExp (name, exp)
      mp <- lift get
      let localMap = mp Map.! name
      lift $ put $ Map.insert name (Map.insert v ret localMap) mp
    (AssignStmt (PureExp (FieldUse v)) exp) -> do
      ret' <- generateExp (name, exp)
      let ret = case ret' of
            Future (Logic.Custom v) -> Logic.Custom v
            Future v -> v
            other -> other
      mp <- lift get
      let fs = mp Map.! "fields"
      lift $ put $ Map.insert "fields" (Map.insert v ret fs) mp
    (ExprStmt e) -> do
      generateExp (name, e)
      pure ()
    AssertStmt -> throwError $ Other "AssertStmt not supported"
    (AwaitStmt v) -> throwError $ AwaitError ("AwaitStmt not supported as it breaks atomicity: " <> show v)
    SuspendStmt -> throwError $ SyncError "Suspend statements are not supported: The method is no longer atomic"
    ThrowStmt -> throwError $ SyncError "Throw statements are not supported"
    (ReturnStmt e) -> pure ()
    (Block st) -> traverse_ (generateStatement . (name,)) st
    (IfStmt co th Nothing) -> do
      cond' <- generatePureExp (name, co)
      let Boolean cond = cond'
      preIf <- lift get
      traverse_ (generateStatement . (name,)) th
      postThen <- lift get
      lift $ put $ Map.unionWith (Map.unionWith (merge cond)) postThen preIf
    (IfStmt co th (Just el)) -> do
      cond' <- generatePureExp (name, co)
      let Boolean cond = cond'
      preIf <- lift get
      traverse_ (generateStatement . (name,)) th
      postThen <- lift get
      lift $ put preIf
      traverse_ (generateStatement . (name,)) el
      postElse <- lift get
      lift $ put $ Map.unionWith (Map.unionWith (merge cond)) postThen postElse
    (WhileStmt test body) -> do
      mp <- get
      let fs = mp Map.! "fields"
          whileName = mkName fs "boundedWhileNo"
      put $ Map.insert "fields" (Map.insert whileName (WhileBound $ literal False) fs) mp
      st <- boundedWhile 10 whileName name (WhileStmt test body)
      lift $ put st
    SwitchStmt -> throwError $ Other "Not supported feature: SwitchStmt"
    ForeachStmt -> throwError $ Other "Not supported feature: ForeachStmt"
    TryCatchFinallyStmt -> throwError $ Other "Not supported feature: TryCatch"
    (NotImplementedStmt s) -> throwError $ Other ("Not implemented: " <> show s)

-- | To deal with loops, this function will
--    perform the loop *n* number of times.
--
--    If the bound is hit during symbolic execution, a state
--    is produced that causes the commutativity analysis
--    to fail everytime.
boundedWhile :: Int -> String -> String -> Statement -> Constraint VarTable
boundedWhile 0 whileName name _ = do
  mp <- lift get
  let fs = mp Map.! name
  -- This state will cause a failing analysis every time if chosen
  let val = WhileBound . literal $ True
  pure $ Map.insert name (Map.insert whileName val fs) mp
boundedWhile n whileName name st@(WhileStmt test body) = do
  cond' <- generatePureExp (name, test)
  let Boolean cond = cond'
  pre <- lift get
  traverse_ (generateStatement . (name,)) body
  -- post <- lift get
  res <- boundedWhile (n - 1) whileName name st
  pure $ Map.unionWith (Map.unionWith (merge cond)) res pre

generateExp :: (String, Exp) -> Constraint SVar
generateExp (name, PureExp p) = generatePureExp (name, p)
generateExp (name, EffExp e) = generateEffExp (name, e)

-- Function that will add a unique suffix to the String-argument
-- depending on if that name already exists in the map.
mkName :: Map String SVar -> String -> String
mkName mp str = go 0
  where
    go n =
      if Map.member (str <> show n) mp
        then go (n + 1)
        else str <> show n

generateEffExp :: (String, EffExp) -> Constraint SVar
generateEffExp (name, e) = do
  case e of
    (NewExp isLocal ty params) -> do
      svars <- traverse (generatePureExp . (name,)) params
      mp <- lift get
      let fs = mp Map.! "fields"
          newName = mkName fs ("NewExp" <> show ty)
          fs' = Map.insert newName (Lst svars) fs
      lift $ put $ Map.insert "fields" fs' mp
      pure $ Logic.Custom ("New" <> ty) -- Should be a ref to a datatype
    (SyncCall ThisExp method params) -> throwError $ UnsupportedType "generateEffExp: SyncCall not supported"
    (SyncCall obj method params) -> pure $ Future (Logic.Custom "Unknown")
    (AsyncCall ThisExp method params) -> pure $ Future (Logic.Custom "Unknown")
    -- The future is unknowable because we do not have any knowledge about the types at
    -- the current point
    --
    -- -- Does this even make sense?
    -- throwError $ SyncError "generateEffExp: AsyncCall on self not supported: suspends execution."
    -- -- Async Calls are not scheduling points
    -- -- TODO What should be returned here?
    --
    -- Return value is not important? Just verify that everything
    -- is called with the same values?
    (AsyncCall obj method params) -> pure $ Future (Logic.Custom "Unknown")
    (GetExp (VarUse s)) -> do
      mp <- get
      let nm = "fut" <> s <> name
          locals = mp Map.! name
      case Map.lookup nm locals of
        Nothing -> pure . Boolean $ literal True
        Just v -> case locals Map.!? nm of
          Nothing -> throwError $ Other $ "Could not find " <> show nm <> " in map."
          Just v -> pure v
    (AwaitExp asyncCall) ->
      throwError $ AwaitError ("AwaitExp not supported: breaks atomicity: " <> show asyncCall)

generatePureExp :: (String, PureExp) -> Constraint SVar
generatePureExp (name, e) = do
  sta <- get
  case e of
    (VarUse s) -> do
      case sta Map.!? name >>= (Map.!? s) of
        Nothing -> throwError $ Other "Unsupported data type is missing from map"
        Just v -> pure v
    (FieldUse s) -> do
      -- lift $ gets ((Map.! s) . (Map.! "fields"))
      case sta Map.!? "fields" >>= (Map.!? s) of
        Nothing -> throwError $ Other "Unsupported data type is missing from map"
        Just v -> pure v
    -- To support FnApp we need access to the return type of the function
    (FnApp fnName exprs) -> do
      svars <- traverse (generatePureExp . (name,)) exprs
      mp <- lift get
      let fs = mp Map.! "fields"
          fn = mkName fs (name <> fnName)
          fs' = Map.insert fn (Lst svars) fs
          locals = mp Map.! name
      put $ Map.insert "fields" fs' mp
      case Map.lookup ("FnApp" <> fnName) locals of
        Nothing -> pure . Boolean $ literal True
        Just v -> pure v
    (OperatorExp exp) -> generateOperatorExp (name, exp)
    (Literal lit) ->
      pure $ case lit of
        IntLiteral i -> Numeric . literal $ fromIntegral i
        FloatLiteral i -> Flt . literal $ i
        StringLiteral s -> Str . literal $ s
    (DataConstrExp s) ->
      case s of
        "True" -> pure . Boolean $ literal True
        "False" -> pure . Boolean $ literal False
        v -> throwError $ UnsupportedType ("Unsupported Data Constructor: " <> show v)
    NullExp -> pure Null
    s -> throwError $ Other ("Unsupported PureExp: " <> show s)

generateOperatorExp :: (String, OperatorExp) -> Constraint SVar
generateOperatorExp (name, e) = do
  case e of
    UnaryExp op exp -> do
      case op of
        Minus -> do
          ret <- generatePureExp (name, exp)
          let Numeric num = ret
          pure . Numeric $ negate num
        Not -> do
          ret <- generatePureExp (name, exp)
          pure . Boolean $ sNot $ getBoolean ret
    BinaryExp op l r -> do
      l' <- generatePureExp (name, l)
      r' <- generatePureExp (name, r)
      case (l', r') of
        (Boolean a, Boolean b) ->
          case op of
            Or -> pure $ Boolean $ a .|| b
            And -> pure $ Boolean $ a .&& b
            Equal -> pure $ Boolean $ a .== b
            NotEqual -> pure $ Boolean $ a ./= b
        (Numeric x, Numeric y) ->
          case op of
            Equal -> pure $ Boolean $ x .== y
            NotEqual -> pure $ Boolean $ x ./= y
            LessThan -> pure $ Boolean $ x .< y
            LessThanEq -> pure $ Boolean $ x .<= y
            GreaterThan -> pure $ Boolean $ x Data.SBV.Trans..> y
            GreaterThanEq -> pure $ Boolean $ x .>= y
            Addition -> pure $ Numeric $ x + y
            Subtraction -> pure $ Numeric $ x - y
            Multiplication -> pure $ Numeric $ x * y
            Division -> pure $ Numeric $ sDiv x y
            Modulo -> pure $ Numeric $ sMod x y
        (Str s, Str r) ->
          case op of
            Addition -> pure . Str $ s .++ r
            o -> throwError $ Other ("Unsupported operations on strings: " <> show o)
        -- throwError $ Other "Operations on Strings are not supported"
        (Boolean _, Str s) -> pure (Str s)
        (a, b) -> throwError $ Other ("Unsupported types: " <> show a <> " and " <> show b)
