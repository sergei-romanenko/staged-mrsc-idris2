module Main

import Test.Golden

%default covering

allTests : TestPool
allTests = MkTestPool "Staged MRSC" [] Default
  [ "Util"
  , "BigStepSc"
  ]

main : IO ()
main = runner
  [ testPaths "smrsc" allTests
  ] where
    testPaths : String -> TestPool -> TestPool
    -- testPaths dir = record { testCases $= map ((dir ++ "/") ++) }
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
