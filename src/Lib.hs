module Lib
  ( classDecls,
    getModuleDecls,
    readWriteAnalysis,
    fnApps,
  )
where

import AST
import Control.Lens
import Control.Monad (replicateM)
import Data.Aeson (eitherDecode)
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import Data.Data.Lens (biplate)
import Data.Foldable (toList)
import Data.List (tails)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Pretty.Simple (pPrint)

-- | Get all the class declarations
classDecls :: ByteString -> [Decl]
classDecls = classes . getModuleDecls

fnApps :: ByteString -> [(Exp, Exp)]
fnApps = toListOf (biplate . _AssignStmt) . getModuleDecls

printMethods :: [(Method, Method)] -> [(String, String)]
printMethods = map (bimap methodName methodName)

methods :: ModuleDecl -> [Method]
methods = toListOf biplate

classes :: ModuleDecl -> [Decl]
classes = filter (has _ClassDecl) . toListOf biplate

sharedFieldUsage :: Decl -> [(String, String)]
sharedFieldUsage md = printMethods ms
  where
    ms = filter f . pairwise $ toListOf biplate md
    fieldUse = Set.fromList . toListOf (biplate . cosmos . _FieldUse)
    f (a, b) = not $ Set.disjoint (fieldUse a) (fieldUse b)

-- Find the variable occuring on the left side of
-- an assignment.
assignments :: Method -> Set String
assignments =
  Set.fromList
    . toListOf
      ( biplate
          . cosmos
          . _AssignStmt
          . _1
          . _PureExp
          . _FieldUse
      )

-- Find the variable occuring on the left side of
-- an assignment.
fieldUses :: Method -> Set String
fieldUses =
  Set.fromList
    . toListOf
      ( biplate
          . cosmos
          . _FieldUse
      )

getModuleDecls :: ByteString -> ModuleDecl
getModuleDecls = either (error . show) id . eitherDecode

-- | From a ReadWriteSet, return tuples of methods that
--   do commute.
readWriteAnalysis :: Method -> Method -> Bool
readWriteAnalysis metA metB =
  Set.null $
    Set.intersection metAwrites metBwrites
      `Set.union` Set.intersection metAwrites metBreads
      `Set.union` Set.intersection metBwrites metAreads
  where
    metAreads = fieldUses metA
    metAwrites = assignments metA
    metBreads = fieldUses metB
    metBwrites = assignments metB
    varString (FieldUse v) = v
    restrict f = Set.map varString . Set.filter f

-- -- Return True if two methods use the same field.
-- --   This will cut very broadly, and does not care about
-- --   how the field was used.
-- sharedFieldUsages :: (Method, Method) -> Bool
-- sharedFieldUsages (a, b) = not $ Set.disjoint (fieldUse a) (fieldUse b)
--     where
--       fieldUse = Set.fromList . toListOf (biplate . cosmos . _FieldUse)

-- Helper functions

-- Return all possible pairings of
-- two distinct elements from a list.
--
-- Should a method be compared to itself? Currently, this
-- will only compare distinct methods.
--
-- >>> pairwise [1,2,3]
-- [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]
pairwise :: [a] -> [(a, a)]
pairwise xs = do
  [x, y] <- replicateM 2 xs
  pure (x, y)
