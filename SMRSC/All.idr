module SMRSC.All

-- A (very abstract) model of small-step supercompilation

import SMRSC.AbstractSc

-- A model of big-step supercompilation

import SMRSC.Util
import SMRSC.AlmostFullRel
import SMRSC.BarWhistles
import SMRSC.Graphs
--import GraphsTheorems
import SMRSC.BigStepSc
--import BigStepScTheorems
import SMRSC.BigStepScTests
import SMRSC.Cographs
--import CographsTheorems
import SMRSC.Statistics
--import StatisticsTheorems
import SMRSC.Main

-- An instantiation of the model for counter systems

import SMRSC.Counters
import SMRSC.Protocols.Synapse
--import Protocols.MSI
--import Protocols.MOSI
--import Protocols.MESI
--import Protocols.MOESI
--import Protocols.Illinois
--import Protocols.Berkley
--import Protocols.Firefly
--import Protocols.Futurebus
--import Protocols.Xerox
--import Protocols.DataRace
