import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

local instance multisetspec4 : CurrentString ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) where

@[simp]
def contents_nil_inv_raw := ∀ l, (∀ x, 0 = contents l x) -> l = []

@[simp]
def contents_nil_inv_spec : Prop :=
  dspec ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[])

theorem empty_when_empty_match : contents_nil_inv_raw <-> contents_nil_inv_spec :=
  by simp