import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
open sort
open sort_specs
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- No original english
local instance sortspec3 : CurrentString ("insert"::"is"::"a"::"permutation"::"of"::"cons"::[]) where

def insert_perm_spec' := dspec ("insert"::"is"::"a"::"permutation"::"of"::"cons"::[])

def insert_perm_spec'' : insert_perm_spec -> insert_perm_spec' :=
  by simp [insert_perm_spec,insert_perm_spec']
     intro H
     exists insert