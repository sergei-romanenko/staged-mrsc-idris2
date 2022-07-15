module Do

import SMRSC.Graphs
import SMRSC.BigStepScTests

main : IO ()
main = do
  putStrLn $ graph_pp test_graph
