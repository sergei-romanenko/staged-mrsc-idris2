module SMRSC.Protocols.All

import SMRSC.Protocols.Synapse
import SMRSC.Protocols.MSI
import SMRSC.Protocols.MOSI
import SMRSC.Protocols.MESI
import SMRSC.Protocols.MOESI
import SMRSC.Protocols.Illinois
import SMRSC.Protocols.Berkley
import SMRSC.Protocols.Firefly

export
runAll : IO ()
runAll = do
    runSynapse

    runSynapse
    runMSI
    runMOSI
    runMESI
    -- runMOESI
    -- runIllinois
    -- runBerkley
    -- runFirefly
    -- runXerox
    -- runReaderWriter
    -- runDataRace
    -- Slow!
    -- runFuturebus

    runSynapse8
    runMSI8
    runMOSI8
    runMESI8
    runMOESI8
    runIllinois8
    runBerkley8
    runFirefly8
    -- runXerox8
    -- runReaderWriter8
    -- runDataRace8
    -- Slow!
    -- runFuturebus8
