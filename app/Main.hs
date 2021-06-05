module Main where

import AST
import Control.Monad
import Data.Bifunctor
import qualified Data.ByteString.Lazy as BS
import Data.List (tails)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV
import Data.Set (Set)
import qualified Data.Set as Set
import Lib
import Logic
import Text.Pretty.Simple

main :: IO ()
main = do
  inp <- BS.getContents
  -- pPrint $ classDecls inp

  let res = logicEntry (classDecls inp)
  forM_ res $ \(str, a, b, res) -> do
    putStr str
    res >>= printRes a b
  putStrLn "\nDone ---\n"

printRes :: Method -> Method -> Either AnalysisError ThmResult -> IO ()
printRes a b x = case x of
  Left (Other s) -> do
    putStrLn ("Undetermined by SMT due to: " <> show s)
    if readWriteAnalysis a b
      then putStrLn "\tReadWrite: Commuting"
      else putStrLn "\tReadWrite: Not commuting"
  Left err -> putStrLn ("Undetermined: " <> show err)
  Right (ThmResult res) -> case res of
    Unsatisfiable _ _ -> do
      putStrLn "SMT: Commuting"
      putStr "\t -> Trying read-write set analysis: "
      if readWriteAnalysis a b
        then putStrLn "Commute"
        else putStrLn "Not Commute"
    Satisfiable _ _ -> do
      putStrLn "SMT: Not commuting"
      putStr "\t -> Trying read-write set analysis: "
      if readWriteAnalysis a b
        then putStrLn "Commute"
        else putStrLn "Not Commute"
