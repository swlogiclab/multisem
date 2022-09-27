import Init.Data.Nat
import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.Macros
import Multisem.Lexicon
open Cat

-- This takes ~26s to parse in Coq
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000

def bench_vs_coq := pspec [|every natural is nonnegative and some natural is even|]