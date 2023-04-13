import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
open sort
open sort_specs
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

  -- Original was: insertion maintains sortedness
  -- Candidate: insertion of any natural maintains sortedness
local instance sortspec1 : CurrentString ("insertion"::"of"::"any"::"natural"::"maintains"::"sortedness"::[]) where

def insert_sorted_spec'' : insert_sorted_spec = dspec ("insertion"::"of"::"any"::"natural"::"maintains"::"sortedness"::[]) :=
  by simp [insert_sorted_spec]
