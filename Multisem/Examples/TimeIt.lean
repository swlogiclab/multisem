import Init.Data.Nat
import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.Macros
import Multisem.Lexicon
import Multisem.CaseStudies.VFA
open Cat

-- This takes ~26s to parse in Coq
def bench_vs_coq := pspec [|every natural is nonnegative and some natural is even|]