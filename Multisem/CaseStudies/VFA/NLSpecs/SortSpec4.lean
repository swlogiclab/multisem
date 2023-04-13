import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
open sort
open sort_specs
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- Handling the original
local instance sortspec4 : CurrentString ("sort"::"is"::"a"::"permutation"::[]) where

def sort_perm_spec' : 
  sort_perm_spec -> dspec ("sort"::"is"::"a"::"permutation"::[]) :=
  by simp [sort_perm_spec]
     intro H
     exists sort