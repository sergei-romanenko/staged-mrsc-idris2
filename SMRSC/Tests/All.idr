module SMRSC.Tests.All

import SMRSC.Tests.Cartesian
import SMRSC.Tests.Graphs

export
runAll : IO ()
runAll = do
    runCartesian
    runGraphs