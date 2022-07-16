module Main

import Test.Golden

%default covering

allTests : TestPool
allTests = MkTestPool "Staged MRSC" [] Default
  [ "Util"
  , "Graphs"
  ]

main : IO ()
main = runner
  [ testPaths "smrsc" allTests
  ] where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
