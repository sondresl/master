{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module AST where

import Control.Applicative (Alternative ((<|>)))
import Control.Lens
import Control.Lens.Plated
import Control.Monad (guard)
import Data.Aeson
import Data.Aeson.Types
import Data.Char (toUpper)
import Data.Data (Data)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics

newtype ModuleDecl = ModuleDecl Module
  deriving (Show, Data, Generic)

instance FromJSON ModuleDecl where
  parseJSON = withObject "ModuleDecl" $ \o -> do
    ModuleDecl <$> o .: "ModuleDecl"

data Module = Module
  { moduleName :: String,
    moduleDecls :: [Decl]
  }
  deriving (Show, Data, Generic)

instance FromJSON Module where
  parseJSON = withObject "ModuleDecl" $ \o -> do
    Module
      <$> o .: "ModuleName"
      <*> o .: "Declarations"

data MethodSig = Signature String Type [Param]
  deriving (Show, Data, Generic)

instance FromJSON MethodSig where
  parseJSON = withObject "MethodSig" $ \o -> do
    obj <- o .: "MethodSig"
    Signature
      <$> obj .: "Name"
      <*> obj .: "ReturnType"
      <*> obj .: "Params"

data Decl
  = ClassDecl
      { className :: String,
        classParams :: [Param],
        -- , interfaces :: [String]
        classFields :: [FieldDecl],
        classMethods :: [Method]
      }
  | -- Unsure how many of these we need
    InterfaceDecl
      { interfaceName :: String,
        extensions :: [String],
        methodSigs :: [MethodSig]
      }
  | TypeSynDecl String Type
  | TraitDecl
  | FunctionDecl
  | PartialFunctionDecl
  | DataTypeDecl
  | ExceptionDecl
  | NotImplementedDecl String -- TODO Placeholder for missing implementations
  deriving (Show, Data, Generic)

instance FromJSON Decl where
  parseJSON val =
    parseInterfaceDecl val
      <|> parseClassDecl val
      <|> parseTypeSynDecl val
      <|> parseNotImplementedDecl val
      <|> error (show val)
    where
      parseClassDecl =
        withObject "Class" $ \o -> do
          ClassDecl
            <$> o .: "ClassName"
            <*> o .: "Parameters"
            <*> o .: "Fields"
            <*> o .: "Methods"
      parseInterfaceDecl = withObject "InterfaceDecl" $ \o -> do
        obj <- o .: "InterfaceDecl"
        InterfaceDecl
          <$> obj .: "Name"
          <*> obj .: "Extends"
          <*> obj .: "Methods"
      parseTypeSynDecl = withObject "TypeSynDecl" $ \o -> do
        obj <- o .: "TypeSynDecl"
        TypeSynDecl
          <$> obj .: "Name"
          <*> obj .: "Value"
      parseNotImplementedDecl =
        withObject "NotSupportedDecl" $ \o -> do
          NotImplementedDecl <$> o .: "NotSupported"

-- | Why is this separate from `Decl` ?
--
-- Defined as `FieldDeclList` here, rather than as part of the decls, since a
-- FieldDecl can only occur in one place, and not where other types of
-- declarations can occur.
--   --> https://abs-models.org/manual/#sec:classes
data FieldDecl = FieldDecl
  { fieldName :: String,
    fieldType :: Type,
    fieldVal :: Maybe PureExp -- Maybe optional
    -- Reference types may not be initialized, but I do not generate JSON for
    -- InterfaceUse yet.
  }
  deriving (Show, Data, Generic)

instance FromJSON FieldDecl where
  parseJSON = withObject "FieldDecl" $ \o -> do
    FieldDecl
      <$> o .: "FieldName"
      <*> o .: "Type"
      <*> o .:? "InitExp"

-- https://abs-models.org/manual/#sec:builtin-types
--
-- Do we even need to distinguish between built-in types and
-- custom types? At what point do we care about the types? Maybe
-- if we want to know if certain operations commute? Do we need more
-- info than the name of the type?
data Type
  = Unit
  | Int
  | Rat -- Rational numbers
  | Bool
  | String
  | List -- Type
  | Set -- Type
  | Map -- Type Type
  | Maybe -- Type
  | Pair -- Type Type
  | Triple -- Type Type Type
  | Fut [Type]
  | Custom String
  deriving (Show, Eq, Ord, Generic, Data)

instance FromJSON Type where
  parseJSON val =
    parseSimpleType val
      <|> parseFutureType val
    where
      parseSimpleType = \case
        "Unit" -> pure Unit
        "Int" -> pure Int
        "Rat" -> pure Rat
        "Bool" -> pure AST.Bool
        "String" -> pure AST.String
        "List" -> pure AST.List
        "Set" -> pure AST.Set
        "Map" -> pure AST.Map
        "Maybe" -> pure AST.Maybe
        "Pair" -> pure AST.Pair
        "Triple" -> pure AST.Triple
        Data.Aeson.Types.String str -> pure $ Custom $ T.unpack str
        v -> fail ("Not a builtin type: " <> show v)
      parseFutureType = withObject "Type" $ \o -> do
        name <- o .: "CompoundType" :: Parser Text
        guard $ name == "Fut"
        args <- o .: "TypeParameters"
        pure $ Fut args

data Exp
  = PureExp PureExp
  | EffExp EffExp
  deriving (Show, Data, Generic)

instance FromJSON Exp where
  parseJSON e =
    (EffExp <$> parseJSON e)
      <|> (PureExp <$> parseJSON e)
      <|> fail (show e)

-- | EffExp EffExp
-- instance FromJSON Exp where
--   parseJSON = parseJSON
data PureExp
  = VarUse String -- Local variable
  | FieldUse String -- Class fields
  | FnApp String [PureExp] -- Identifier of function + args
  | OperatorExp OperatorExp
  | Literal Literal
  | DataConstrExp String -- Include params?
  | NullExp
  | ThisExp
  deriving (Show, Data, Generic)

-- Missing String -- Refers to not yet implemented

data Literal
  = IntLiteral Int
  | FloatLiteral Float
  | StringLiteral String
  deriving (Show, Data, Generic, ToJSON, FromJSON)

instance FromJSON PureExp where
  parseJSON val =
    parseIntLiteral val
      <|> parseVarUse val
      <|> parseFieldUse val
      <|> parseOperatorExp val
      <|> parseFnApp val
      <|> parseDataConstructor val
      <|> parseStringLiteral val
      <|> parseFloatLiteral val
      <|> parseNullExp val
      <|> parseThisExp val
    where
      -- <|> parseNotSupported val

      -- TODO Placeholder for constructs missing implementation
      -- parseNotSupported = withObject "NotSupportedPureExp" $ \o -> do
      --   Missing <$> o .: "NotSupported"
      parseIntLiteral = withObject "IntLit" $ \o -> do
        Literal . IntLiteral <$> o .: "IntLiteral"
      parseFloatLiteral = withObject "FloatLit" $ \o -> do
        Literal . FloatLiteral <$> o .: "IntLiteral"
      parseStringLiteral = withObject "StringLit" $ \o -> do
        Literal . StringLiteral <$> o .: "StringLiteral"
      parseVarUse = withObject "VarUse" $ \o -> do
        VarUse <$> o .: "VarName"
      parseFieldUse = withObject "FieldName" $ \o -> do
        FieldUse <$> o .: "FieldName"
      parseNullExp = withText "NullExp" $ \o -> do
        guard $ o == "NullExp"
        pure NullExp
      parseThisExp = withText "ThisExp" $ \o -> do
        guard $ o == "ThisExp"
        pure ThisExp
      parseFnApp = withObject "FnAppExp" $ \o -> do
        obj <- o .: "FnApp"
        FnApp <$> obj .: "FnName"
          <*> obj .: "FnArgs"
      parseOperatorExp = withObject "OperatorExp" $ \o -> do
        OperatorExp <$> parseJSON (Object o)
      -- Since a field might be used to construct some data, we need to
      -- know the fields involved.
      parseDataConstructor = withObject "DataConstructor" $ \o -> do
        DataConstrExp <$> o .: "DataConstructor"

-- this . SimpleIdentifier
-- This
-- TemplateString
-- LetExp
-- FnAppListExp
-- ParFnAppExp
-- WhenExp
-- CaseExp
-- TypeCheckExp
-- TypeCastExp
-- ( PureExp )

data EffExp
  = NewExp Bool String [PureExp]
  | -- Second PureExp is SimpleIdentifier
    SyncCall PureExp String [PureExp]
  | -- Second PureExp is SimpleIdentifier
    AsyncCall PureExp String [PureExp]
  | GetExp PureExp
  | AwaitExp EffExp -- Always an AsyncCall
  deriving (Show, Data, Generic)

instance FromJSON EffExp where
  parseJSON val =
    parseAsyncCall val
      <|> parseSyncCall val
      <|> parseNewExp val
      <|> parseGetExp val
    where
      parseAsyncCall = withObject "AsyncCall" $ \o -> do
        obj <- o .: "AsyncCall"
        AsyncCall <$> obj .: "Callee"
          <*> obj .: "Method"
          <*> obj .: "Params"
      parseSyncCall = withObject "SyncCall" $ \o -> do
        obj <- o .: "SyncCall"
        SyncCall <$> obj .: "Callee"
          <*> obj .: "Method"
          <*> obj .: "Params"
      parseNewExp = withObject "NewExp" $ \o -> do
        obj <- o .: "NewExp"
        NewExp <$> obj .: "IsLocal"
          <*> obj .: "ClassName"
          <*> obj .: "Params"
      parseGetExp = withObject "GetExp" $ \o -> do
        GetExp <$> o .: "GetExp"

data OperatorExp
  = UnaryExp
      { unaryOperator :: UnaryOp,
        unaryExp :: PureExp
      }
  | BinaryExp
      { binaryOp :: BinaryOp,
        left :: PureExp,
        right :: PureExp
      }
  deriving (Show, Data, Generic)

data UnaryOp
  = Not
  | Minus
  deriving (Show, Eq, Ord, Data, Generic)

data BinaryOp
  = Or
  | And
  | Equal
  | NotEqual
  | LessThan
  | LessThanEq
  | GreaterThan
  | GreaterThanEq
  | Addition
  | Subtraction
  | Multiplication
  | Division
  | Modulo
  deriving (Show, Eq, Ord, Data, Generic)

instance FromJSON OperatorExp where
  parseJSON val =
    parseBinaryExp val
      <|> parseUnaryEp val
    where
      parseUnaryEp = withObject "binary" $ \o -> do
        op <- o .: "Operator" :: Parser String
        let name = case op of
              "MinusExp" -> Minus
              "NegExp" -> Not
        val <- o .: "Value"
        pure $ UnaryExp name val
      parseBinaryExp = withObject "binary" $ \o -> do
        op <- o .: "Operator" :: Parser String
        let name = case op of
              "AddAddExp" -> Addition -- Names taken from ABS internals
              "SubAddExp" -> Subtraction
              "MultMultExp" -> Multiplication
              "DivMultExp" -> Division
              "ModMultExp" -> Modulo
              "AndBoolExp" -> And
              "OrBoolExp" -> Or
              "EqExp" -> Equal
              "LTExp" -> LessThan
              "GTExp" -> GreaterThan
              "NotEqExp" -> NotEqual
              _ -> error ("parseBinaryExp: Not a binary operation: " <> show op)
        left <- o .: "Left"
        right <- o .: "Right"
        pure $ BinaryExp name left right

data Param = Param
  { paramName :: String,
    paramType :: Type
  }
  deriving (Show, Data, Generic)

instance FromJSON Param where
  parseJSON = withObject "Param" $ \o -> do
    Param
      <$> o .: "ParamName"
      <*> o .: "ParamType"

data Statement
  = SkipStmt
  | VarDeclStmt String Type (Maybe Exp)
  | AssignStmt Exp Exp
  | ExprStmt Exp
  | AssertStmt
  | AwaitStmt Guard
  | SuspendStmt
  | ThrowStmt
  | ReturnStmt Exp
  | Block [Statement]
  | IfStmt PureExp [Statement] (Maybe [Statement])
  | SwitchStmt
  | WhileStmt PureExp [Statement]
  | ForeachStmt
  | TryCatchFinallyStmt
  | NotImplementedStmt String
  deriving (Show, Data, Generic)

instance FromJSON Statement where
  parseJSON val =
    parseReturnStmt val
      <|> parseAssignStmt val
      <|> parseVarDeclStatement val
      <|> notImplementedStmt val
      <|> parseExprStmt val
      <|> parseIfStmt val
      <|> parseWhileStmt val
      <|> parseAwaitStmt val
      <|> parseSkipStmt val
      <|> parseSuspendStmt val
      <|> fail ("Statement: " <> show val)
    where
      notImplementedStmt = withObject "NotSupportedStmt" $ \o -> do
        NotImplementedStmt <$> o .: "NotSupported"
      parseIfStmt = withObject "IfStmt" $ \o -> do
        obj <- o .: "IfStmt"
        IfStmt <$> obj .: "Condition"
          <*> obj .: "Then"
          <*> obj .:? "Else"
      parseWhileStmt = withObject "WhileStmt" $ \o -> do
        obj <- o .: "WhileStmt"
        WhileStmt <$> obj .: "Condition"
          <*> obj .: "Body"
      parseAssignStmt = withObject "AssignStmt" $ \o -> do
        obj <- o .: "AssignStatement"
        AssignStmt
          <$> obj .: "Variable"
          <*> obj .: "Value"
      parseReturnStmt = withObject "ReturnStmt" $ \o -> do
        ReturnStmt <$> o .: "ReturnStmt"
      parseExprStmt = withObject "ExprStmt" $ \o -> do
        ExprStmt <$> o .: "ExprStmt"
      parseSkipStmt = withText "SkipStmt" $ \o -> do
        guard $ o == "SkipStmt"
        pure SkipStmt
      parseSuspendStmt = withText "SuspendStmt" $ \o -> do
        guard $ o == "SuspendStmt"
        pure SuspendStmt
      parseAwaitStmt = withObject "AwaitStmt" $ \o -> do
        obj <- o .: "AwaitStmt"
        AwaitStmt <$> parseJSON obj
      parseVarDeclStatement = withObject "VarDeclStmt" $ \o -> do
        obj <- o .: "VarDeclStmt"
        VarDeclStmt
          <$> obj .: "VarName"
          <*> obj .: "Type"
          <*> obj .:? "InitExp"

data Guard
  = ClaimGuard PureExp
  | AndGuard Guard Guard
  | DurationGuard PureExp PureExp
  | ExpGuard PureExp
  deriving (Show, Data, Generic)

instance FromJSON Guard where
  parseJSON val =
    parseDurationGuard val
      <|> parseClaimGuard val
      <|> parseExpGuard val
      <|> fail ("Statement: " <> show val)
    where
      parseClaimGuard = withObject "Claim" $ \o -> do
        obj <- o .: "ClaimGuard"
        ClaimGuard <$> parseJSON obj
      parseDurationGuard = withObject "Duration" $ \o -> do
        obj <- o .: "DurationGuard"
        mi <- obj .: "Min"
        ma <- obj .:? "Max"
        pure $ case ma of
          Nothing -> DurationGuard mi mi
          Just v -> DurationGuard mi v
      parseExpGuard = withObject "ExpGuard" $ \o -> do
        obj <- o .: "ExpGuard"
        ExpGuard <$> parseJSON obj

data Method = Method
  { methodName :: String,
    returnType :: Type,
    params :: [Param],
    statements :: [Statement]
  }
  deriving (Show, Data, Generic)

instance FromJSON Method where
  parseJSON = withObject "Method" $ \o -> do
    obj <- o .: "MethodImpl"
    Signature name ret ps <- obj .: "Signature"
    Method name ret ps <$> obj .: "Body"

-- | Template Haskell
makePrisms ''Module
makePrisms ''Decl
makePrisms ''FieldDecl
makePrisms ''Type
makePrisms ''Exp
makePrisms ''PureExp
makePrisms ''Literal
makePrisms ''OperatorExp
makePrisms ''UnaryOp
makePrisms ''BinaryOp
makePrisms ''Param
makePrisms ''Statement
makePrisms ''Method

-- Plated instances for traversing the AST
deriving instance Plated Module

deriving instance Plated Decl

deriving instance Plated FieldDecl

deriving instance Plated Type

deriving instance Plated Exp

deriving instance Plated PureExp

deriving instance Plated Literal

deriving instance Plated OperatorExp

deriving instance Plated UnaryOp

deriving instance Plated BinaryOp

deriving instance Plated Param

deriving instance Plated Statement

deriving instance Plated Method
