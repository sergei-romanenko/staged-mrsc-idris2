module SMRSC.Main

{-
import Data.SortedMap

import SLanguage
import SCheck
import SParsers
import ProcessTree
import PTBuilder
import ResProgGen
import PrettyPrinter
-}

import Data.List

import SMRSC.Counters
import SMRSC.Protocols.Synapse

%default total

-- The process tree is returned by the supercompilers
-- just to enable the user to take a look at it.

main : IO ()
main = do
  putStrLn "Usage: staged-mrsc-idris2 taskname"
  putStrLn "Nothing to do!"
{-
main = do
  [_, taskName] <- getArgs
    | _ => putStrLn "Usage: spsc-lite-idris taskname"
  let pathTask = taskName ++ ".task"
  let pathTree = taskName ++ ".tree"
  let pathRes  = taskName ++ ".res"
  Right task <- readFile pathTask
    | Left ferr =>
        putStrLn ("Error reading file " ++ pathTask ++ ": " ++ show ferr)
  putStrLn ("* Task read from " ++ pathTask)
  let Right (MkTask e prog) = parseTask task
    | Left msg => putStrLn msg
  let Nothing = checkTask (MkTask e prog)
      | Just msg => putStrLn msg
  let tree = advancedBuilder prog e
  Right _ <- writeFile pathTree (ppTree $ tree) 
    | Left ferr =>
        putStrLn ("Error writing file " ++ pathTree ++ ": " ++ show ferr)
  putStrLn ("* Process tree written to " ++ pathTree)
  let (resExp, resProg) = genResidualProgram tree
  Right _ <- writeFile pathRes (ppTask $ MkTask resExp resProg)
    | Left ferr =>
        putStrLn ("Error writing file " ++ pathRes ++ ": " ++ show ferr)
  putStrLn ("* Output written to " ++ pathRes)
-}
