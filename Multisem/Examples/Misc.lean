import Init.Data.Nat
import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.Macros
import Multisem.Lexicon
open Cat


--#check dbgspec ["one"] (@NP Nat)
--#check dbgspec (["is"]++["odd"]) (lslash (@NP Nat) S)


-- These would need a the reverse associativity lemma, which is commented out because:
-- (a) everything comes out associated to the right from the parser (which we haven't yet ported from Coq)
-- (b) leaving it in currently, even with dramatically limited priority, leads typeclass resolution to cycle uselessly flipping the associativity of some sequences back and forth without progress
--#check pspec (["one"]++["is"]++["one"])
--#check pspec (["one"]++["is"]++["odd"])
--#check pspec ((["one"]++["is"])++["odd"])
def one_is_odd :=  pspec ("one"#("is"#"odd"))



--  instance and_sent_lex : @lexicon Bs BsBase  "and" (rslash (lslash (prim S) (prim S)) (prim S)) := { denotation := fun a n => a /\ n }
--  instance or_sent_lex : @lexicon Bs BsBase  "or" (rslash (lslash (prim S) (prim S)) (prim S)) := { denotation := fun a n => a \/ n }
--  instance or_adj_lex {T}: @lexicon Bs BsBase  "or" (rslash (lslash (prim (@ADJ T)) (prim (@ADJ T))) (prim (@ADJ T))) := { denotation := fun a n x => a x \/ n x }
--  instance and_adj_lex {T}: @lexicon Bs BsBase  "and" (rslash (lslash (prim (@ADJ T)) (prim (@ADJ T))) (prim (@ADJ T))) := { denotation := fun a n x => a x /\ n x }
--
--
instance equals_eq_lex {T}: lexicon Prop "equals" (((@NP T) ∖ S) // (@NP T)) where
  denotation := fun r l => r = l 

def one_equals_one := (pspec ("one" # ("equals" # "one")))
--def one_is_odd := (pspec ("one" # ("is" # "odd")))
def two_is_even := (pspec ("two" # ("is" # "even")))

-- This essentially pretty-prints. The example from the paper is based on manually extracting the interactive proof mode render
#eval (specwitness Prop [|two is even|])

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
def one_is_odd_and_two_is_even := (pspec ("one" # ("is" # ("odd" # ("and" # ("two" # ("is" # "even")))))))
---- a ha, so the problem is that I'm missing rules to reassociate appropriately...
---- ah, okay, was missing a couple structural rules
---- but so far, while I haven't added universe polymorphism or sorted the primitives by logical type, this seems way snappier than Coq
def one_is_odd_and_two_is_even' := (pspec (("one" # ("is" # "odd")) # ("and" # ("two" # ("is" # "even")))))
def one_is_odd_and_two_is_even'' := pspec [|one is odd and two is even|]
--
--
--

---- Specs from original testing file (though in the absence of the and/or lifting rules!!!)
def addone (n:Nat) := n + 1
instance addonelex : lexicon Prop "addone" (@NP (Nat -> Nat)) where 
  denotation := addone 

def addone_equals_addone := (pspec ("addone" # ("equals" # "addone")))
def addone_is_monotone := (pspec ("addone" # ("is" # "monotone")))
def addone_given_one_is_two := (pspec ("addone" # ("given" # ("one" # ("is" # "two")))))
def addone_given_three_is_four := (pspec ("addone" # ("given" # ("three" # ("is" # "four")))))
def addone_given_three_equals_four := (pspec ("addone" # ("given" # ("three" # ("equals" # "four")))))

def addone_mono : pspec [|addone is monotone|] :=
  by -- ⊢ pspec (ContextTree.one "addone"#ContextTree.one "is"#ContextTree.one "monotone")
     simp
     -- ⊢ ∀ (x y : Nat), x ≤ y → addone x ≤ addone y
     intro x y h
     simp [addone]
     sorry
     -- Not clear why I can't access these lemmas
     --apply Init.Data.Nat.add_le_add
     --apply Init.Data.Nat.add_le_add_right

--#check dbgspec ("is" # "non-negative") (lslash (@NP Nat) S)
--#check dbgspec "every" (quant Nat)
--#check dbgspec "natural" (@CN Nat)
--#check dbgspec ("every"#"natural") (rslash (S) (lslash (@NP Nat) S))

def every_natural_is_nonnegative := (pspec ("every" # ("natural" # ("is" # "non-negative"))))
def some_natural_is_nonnegative := (pspec ("some" # ("natural" # ("is" # "non-negative"))))
def some_natural_is_even := (pspec ("some" # ("natural" # ("is" # "even"))))

def four_is_even_and_nonnegative := (pspec ("four" # ("is" # ("even" # ("and" # "non-negative")))))
@[simp]
def three_is_nonnegative_and_four_is_even := (pspec ("three" # ("is" # ("non-negative" # ("and" # ("four" # ("is" # ("even"))))))))

def example5 := pspec [|every natural is nonnegative and some natural is even|]

theorem exmisc : three_is_nonnegative_and_four_is_even :=
  by simp

@[simp]
def every_natural_is_nonneg_and_some_natural_is_even := (pspec ("every" # ("natural" # ("is" # ("non-negative" # ("and" # ("some" # ("natural" # ("is" # "even")))))))))
theorem exmisc3 : every_natural_is_nonneg_and_some_natural_is_even :=
  by simp
     apply (Exists.intro 2); simp

@[simp]
def every_natural_is_nonneg_and_nonneg := (pspec ("every" # ("natural" # ("is" # ("non-negative" # ("and" # ("is" # "non-negative")))))))
theorem exmisc2 : every_natural_is_nonneg_and_nonneg :=
  by simp

theorem exmisc2' : pspec [| every natural is nonnegative and is nonnegative |] :=
  by simp

-- This needs a higher timeout
--theorem exmisc3' : pspec [| every natural is nonnegative and is odd or even |] :=
--  by simp

@[simp]
def every_natural_is_odd_or_even := (pspec ("every" # ("natural" # ("is" # ("odd" # ("or" # "even"))))))
@[simp]
def every_natural_is_odd_or_even3 := (pspec ("every" # ("natural" # ("is" # ("odd" # ("or" # "even"))))))


