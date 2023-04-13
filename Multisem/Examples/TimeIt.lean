import Init.Data.Nat
import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.ListMacros
import Multisem.Lexicon

import Multisem.DiffListEncoding

-- This takes ~26s to parse in Coq
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

local instance : CurrentString [|every natural is nonnegative and some natural is even|] where

def bench_vs_coq := dspec [|every natural is nonnegative and some natural is even|]