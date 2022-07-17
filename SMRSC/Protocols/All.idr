module SMRSC.Protocols.All

import SMRSC.Protocols.Synapse

export
runAll : IO ()
runAll = do
    runSynapse
    runSynapse8
