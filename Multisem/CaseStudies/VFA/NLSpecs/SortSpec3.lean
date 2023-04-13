import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
open sort
open sort_specs
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- Original was: insertion sort makes a list sorted
-- This use of "a" is universal, rather than existential, let's switch to any
-- This original is actually ambiguous between the universal and existential reading of "a", so the rewrite improves precision
-- Proposal is: sort sorts any list
-- Reasoning: 'makes' here would normally suggest the list is being *mutated*, which of course it is not. Instead, we'd like to be more explicit about it returning a (possibly distinct) sorted list.
local instance sortspec3 : CurrentString ("insert"::"is"::"a"::"permutation"::"of"::"cons"::[]) where

def insert_perm_spec' := dspec ("insert"::"is"::"a"::"permutation"::"of"::"cons"::[])

def insert_perm_spec'' : insert_perm_spec -> insert_perm_spec' :=
  by simp [insert_perm_spec,insert_perm_spec']
     intro H
     exists insert