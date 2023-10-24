import Multisem.Grammar
import Multisem.Lexicon
-- Temporary while exploring this as an alternative context structure:
--import Multisem.CaseStudies.VFA.Sort
--import Multisem.CaseStudies.VFA.MultiSet
--open sort

open Cat
/-
 - The official Lean 4 release added checks on instances
 - to ensure resolution will terminate, which basically
 - require all instances to propagate information from
 - "input" params to "output" params. These instances
 - do not do that, so we turn off checking of this
 - property.
-/
set_option synthInstance.checkSynthOrder false

/--
  Length already exists in the standard library, but we want a version
  we can mark for simplification during typeclass resolution without
  breaking other people's proofs
-/
--@[simp]
--def sentence_length (s : List string) : Nat :=
--  match s with
--  | [] => 0
--  | _::s' => Nat.succ (sentence_length s')

class StrictSubList (A B : List String) where
instance StrictSubListBase {a}{A} : StrictSubList (a::A) A where
instance StrictSubtListTail2 {A B}{a} [StrictSubList A B] : StrictSubList (a::A) B where

/--
  Named as `lt` to avoid naming collisions with `LT`.

  Note we've flipped the ordering from above: the smaller elt is now on the left
-/
class lt (A B : Nat) where
instance lt_ind (a b) [lt a b] : lt (Nat.succ a) (Nat.succ b) where
instance lt_base (n) : lt 0 (Nat.succ n) where
-- Some helpers to unfold during TC search...
--instance lt_sentence_length (x:Nat) (w:String) (s':List String) [lt x (Nat.succ (sentence_length s'))] : lt x (sentence_length (w::s')) where

namespace lt_tests
  def reqlt (x y : Nat) [lt x y] := ()
  #check reqlt 0 1
  #check reqlt 0 5
  #check reqlt 3 5
  --#check reqlt 0 (sentence_length ("three"::"is"::"even"::[]))
  --#check reqlt 2 (sentence_length ("three"::"is"::"even"::[]))
  --def but_its_lt : lt 0 (sentence_length ("three"::"is"::"even"::[])) :=
  --  lt_sentence_length 0 "three" ("is"::"even"::[])
end lt_tests

/--
  A tag typeclass for the current thing to parse.
  Essentially everything assumes there's never more than one of these in scope at a time.
  It is also critical that there are *no instances* of this class!
  We can use `CurrentString.mk` to provide an instance explicitly, but we don't want TC inference to go wild picking arbitrary sentences.
  We have marked the one parameter `outParam` to ensure that Lean will attempt to infer it with no specific
  constraints on `s` (which should be fine and fast as long as there's really only one instance in scope)
-/
class CurrentString (s : outParam (List String)) where

/--
  A typeclass for mapping the Nth word of a sentence, as a list of strings.
  TODO: Consider rule ordering
-/
class Nth (s : List String) (L : Nat) (w : String) where
instance nth_zero (s' w) : Nth (w::s') 0 w where
instance nth_succ (s' w w' n) [Nth s' n w'] : Nth (w::s') (Nat.succ n) w' where

section CheckNth
  def reqNth (s : List String) (L : Nat) (w : String) [Nth s L w] := ()
  #check reqNth ("hello"::[]) 0 "hello"
  #check reqNth ("hello"::"there"::[]) 0 "hello"
  #check reqNth ("hello"::"there"::[]) 1 "there"
  #check reqNth ("hello"::"there"::"Elgot"::[]) 2 "Elgot"
end CheckNth

--class Len (s : List String) (L : Nat) where
--instance len_zero : Len [] 0 where
--instance len_cons w s L [Len s L] : Len (w::s) (Nat.succ L) where




/--
  The core parsing result typeclass.

  We could in principle index this by the list we're parsing, but a big
  part of what we're trying to do is make table lookups during resolution fast,
  and sticking a possibly-long list of strings in the table will be counterproductive on that measure.
-/
class DSynth (P:Type u) (Front Back : Nat) (lc rc : outParam Bool) (C : outParam Cat) where
  dsem : interp P C
attribute [simp] DSynth.dsem

-- TODO: Consider attending to the order of the `lt` goals: currently back first because in the top-level goal this will force unfolding via `lt_sentence_length`

instance DRApp {P}(Front Back1 Back2 : Nat)(lc lc' rc') (A B : Cat)
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [lt Back1 Back2]
  [lt Front Back1]
  [L : DSynth P Front Back1 lc false (B // A)]
  [R : DSynth P Back1 Back2 lc' rc' A]
  : DSynth P Front Back2 false false B where
  dsem := L.dsem R.dsem
instance DLApp {P}(Front Back1 Back2 : Nat)(rc lc' rc') (A B : Cat)
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [lt Back1 Back2]
  [lt Front Back1]
  [R : DSynth P Back1 Back2 false rc (A ∖ B)] -- Look for the slash first, bail if it's not
  [L : DSynth P Front Back1 lc' rc' A]
  : DSynth P Front Back2 false false B where
  dsem := R.dsem L.dsem

/--
  An instance for lexical entries. This has the highest priority of any instance, as we should
  always try lexical lookups on singleton diff-lists.
-/
instance (priority := default + 100) DLex {P s}(L : Nat)(w:String)(C:Cat)
  [_cur:CurrentString s]
  [_nth:Nth s L w]
  [l : lexicon P w C]
  : DSynth P L (Nat.succ L) false false C where
  dsem := l.denotation

-- No Reassoc or Reassoc' is necessary!

instance DShift {P}(Front Back : Nat)(l c r)(lc rc)[lt Front Back][L:DSynth P Front Back lc rc (l ∖ (c // r))] : DSynth P Front Back false false ((l ∖ c) // r) where
  dsem xr xl := L.dsem xl xr

-- Search right first, try to bias parsing to right-to-left for English
-- TODO: these rules should also reject compositions as their primary functors
instance DRComp (P:Type u)(s smid s' c1 c2 c3)(lc rc lc')[lt smid s'][lt s smid][R:DSynth P smid s' lc rc (c2 // c3)][L:DSynth P s smid lc' false (c1 // c2)] : DSynth P s s' false true (c1 // c3) where
  dsem x := L.dsem (R.dsem x)
instance DLComp (P:Type u)(s smid s' c1 c2 c3)(lc rc rc')[lt smid s'][lt s smid][R:DSynth P smid s' false rc' (c2 ∖ c3)][L:DSynth P s smid lc rc (c1 ∖ c2)] : DSynth P s s' true false (c1 ∖ c3) where
  dsem x := R.dsem (L.dsem x)

-- English-specific lifting rules
-- Montague-style lifting for GQs in object position
instance DMLift (H:Type u){T U:Type u}(s s')(lc rc)[sem:DSynth H s s' lc rc (((@NP T) ∖ S) // (@NP U))] :
  DSynth H s s' false false (((@NP T) ∖ S) // (S // ((@NP U) ∖ S))) where 
  dsem := fun P x => P (fun y => sem.dsem y x)


/-
  The rules in here make the search space *much* larger, so they are disabled
  by default.
-/
namespace DiffJacobson
  -- Slightly simplified (concretized) Jacobson-style extraction (e.g., for anaphora), per Jaeger (p100)
  -- Jacobson restricts the automatic raising to cases where the extraction is a NP, which is all we need now, and also prevents these from completely trashing performance with unconstrained search
  /-
  local instance (priority := low) GR {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (A // B)]
    : Synth P X ((A % (@NP C)) // (B % (@NP C))) where
    denotation := fun x y => base.denotation (x y)
    stringRep := "(G> "++base.stringRep++")"
  local instance (priority := low) GL {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (B ∖ A)]
    : Synth P X ((B % (@NP C)) ∖ (A % (@NP C))) where
    denotation := fun x y => base.denotation (x y)
    stringRep := "(G< "++base.stringRep++")"
  
  local instance (priority := low) ZRR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X ((A // (@NP B)) // C)]
    : Synth P X ((A // (@NP B)) // (C % (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z>> "++base.stringRep++")"
  local instance (priority := low) ZLR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X (((@NP B) ∖ A) // C)]
    : Synth P X (((@NP B) ∖ A) // (C % (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z<> "++base.stringRep++")"
  local instance (priority := low) ZRL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ (A // (@NP B)))]
    : Synth P X ((C % (@NP B)) ∖ (A // (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z>< "++base.stringRep++")"
  local instance (priority := low) ZLL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ ((@NP B) ∖ A))]
    : Synth P X ((C % (@NP B)) ∖ ((@NP B) ∖ A)) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z<< "++base.stringRep++")"
      -/

  /- Even with the NP restrictions, the above still explode performance because
     they essentially result in TC resolution lifting random transitive verbs and such.
     As an alternative, let's consider what the Z rules actually do:
     they lift function types so they can combine with arguments that have extracted referents. But they allow *unnecessary* lifting.
     What if instead we fused them with application, yielding specialized application rules that only apply when it's necessary to combine with an extraction? That should control the slow-down, but would be subtle.

     These rules are much less general than the arbitrary lifting, because they won't automatically play well with other combinators --- we may end up needing quite a few more of these. Each seems to slow down search a little bit, so we will keep these in their own module: these will be scoped instances. We'll keep the original rules around as local instances (which will never be considered in real searches) so we can prove conservativity
  -/
  /-- A condensation of `GR` and `SynthRApp` -/
  scoped instance DAppGR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc lc' rc'}
    [lt X mid]
    [lt mid Y]
    [arg:DSynth P mid Y lc' rc' (B % (@NP C))]
    [f:DSynth P X mid lc false (A // B)]
    : DSynth P X Y false false (A % (@NP C)) where
    dsem := fun c => f.dsem (arg.dsem c)
  /-- A condensation of `GL` and `SynthLApp` -/
  scoped instance DAppGL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc rc rc'}
    [lt mid Y]
    [lt X mid]
    [arg:DSynth P X mid lc rc (B % (@NP C))]
    [f:DSynth P mid Y false rc' (B ∖ A)]
    : DSynth P X Y false false (A % (@NP C)) where
    dsem := fun c => f.dsem (arg.dsem c)
  scoped instance DAppZRR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc lc' rc'}
    [lt mid Y]
    [lt X mid]
    [arg:DSynth P mid Y lc' rc' (C % (@NP B))]
    [f:DSynth P X mid lc false ((A // (@NP B)) // C)]
    : DSynth P X Y false false (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZLR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc lc' rc'}
    [lt mid Y]
    [lt X mid]
    [arg:DSynth P mid Y lc' rc' (C % (@NP B))]
    [f:DSynth P X mid lc false (((@NP B) ∖ A) // C)]
    : DSynth P X Y false false ((@NP B) ∖ A) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZRL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc rc rc'}
    [lt mid Y]
    [lt X mid]
    [arg:DSynth P X mid lc rc (C % (@NP B))]
    [f:DSynth P mid Y false rc' (C ∖ (A // (@NP B)))]
    : DSynth P X Y false false (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZLL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}{lc rc rc'}
    [lt mid Y]
    [lt X mid]
    [arg:DSynth P X mid lc rc (C % (@NP B))]
    [f:DSynth P mid Y false rc' (C ∖ ((@NP B) ∖ A))]
    : DSynth P X Y false false (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n

  -- For now we'll keep the word 'the' under wraps as well
  scoped instance (priority := high) the_lex {P}[HeytingAlgebra P]{T}: lexicon P "the" ((@NP T % @NP T) // (@CN T)) where
    denotation := fun _cn x => x
  /- Another difficulty here is that for modified CNs (those that don't just denote true), this definition discards the restriction --- e.g., 'the even number' could resolve to an 'odd number'!

  One option would be to tweak CNs again to have them also reflect their predicate into the typeclass unification problem. But that will lead to problems with TC search failing for equivalent but not definitionally equal predicates (even positive vs positive even).

  Another approach would be to treat 'the' as a GQ that gets its argument externally (so, type is roughtly GQ|NP, so the semantics capture sentence-combining things), then could apply the CN predicate to whatever gets bound as a sanity check.
  -/

end DiffJacobson

@[simp]
--def dspec (L : List String) [D: DSynth Prop L [] S] : Prop := D.dsem
def dspec (L : List String) [_cur:CurrentString L] {lc rc}[D:DSynth Prop 0 ((@List.rec String (fun _ => Nat) 0 (fun _head _tail res => Nat.succ res)) L) lc rc S] : Prop := D.dsem
@[simp]
def dspec' (L : List String) (n:Nat) [_cur:CurrentString L] {lc rc}[D:DSynth Prop 0 n lc rc S] : Prop := D.dsem
@[simp]
def dbgdspec (L : List String) (n:Nat) [_cur:CurrentString L] {lc rc}[D:DSynth Prop 0 n lc rc S] : DSynth Prop 0 n lc rc S := D
@[simp]
def dbgdspec' (L : List String) [_cur:CurrentString L] {lc rc}[D:DSynth Prop 0 ((@List.rec String (fun _ => Nat) 0 (fun _head _tail res => Nat.succ res)) L) lc rc S] : DSynth Prop 0 ((@List.rec String (fun _ => Nat) 0 (fun _head _tail res => Nat.succ res)) L) lc rc S := D

#check @List.brecOn
#check @List.below
#print List.below
#check @List.rec
#check (@List.rec String (fun _ => Nat) 0 (fun _head _tail res => Nat.succ res))

-- While 400K was is enough to parse anything with raw DiffLists, it's inadequate to parse anything more than "three is even" in this model; the additional typeclasses seem to boost the number of comparisons made. But, 400K is a count of comparisons, not a linear cost. Since the theory here is that the individual checks were taking forever due to so many list lookups in typeclass tables, increasing this number isn't necessarily bad; 400K goes faster here than in DiffLists.
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
--set_option trace.Meta.synthInstance.instances true
--set_option trace.Meta.synthInstance.newAnswer true

namespace three_is_even

  local instance c : CurrentString ("three"::"is"::"even"::[]) where

-- Let's confirm the proof theory is complete enough to find this
def three_is_even_parse : DSynth Prop 0 3 false false S :=
  let three : DSynth Prop 0 1 false false (@NP Nat):= DLex 0 "three" (@NP Nat) --(l:=threelex)
  let is : DSynth Prop 1 2 false false (((@NP Nat) ∖ S) // (@ADJ Nat)) := DLex 1 "is" _ --(l:=noun_is_adj_lex)
  let even : DSynth Prop 2 3 false false (@ADJ Nat) := DLex 2 "even" _ --(l:=evenlex)
  let is_even : DSynth Prop 1 3 false false ((@NP Nat) ∖ S) := DRApp (L:=is) (R:=even)
  DLApp (L:=three) (R:=is_even)
#check three_is_even_parse.dsem

def three_is_even_imp_false : three_is_even_parse.dsem -> False :=
  by simp [three_is_even_parse]

@[simp]
def three_is_even_diff := dbgdspec ("three"::"is"::"even"::[]) 3

@[simp]
def three_is_even_diff' := dbgdspec' ("three"::"is"::"even"::[])

end three_is_even


--namespace contents_nil_inv_spec
--  open DiffJacobson
--  local instance : CurrentString ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) where
--
----instance its_contents_manual_hack : DSynth Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value))) :=
--  --DRApp (L:= DLex (l := its_ref)) (R:=DLex (l := contents_lex))
--
------ TODO: plural values
------def contents_nil_inv_spec_d := dspec ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[])
--
----def dbgdspec (P:Type u) (X Y : List String)[StrictSubList X Y] (C:Cat) [D:DSynth P X Y C] : DSynth P X Y C := D
--
--
----def contents_nil_inv_spec_d_manual_400K : DSynth Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] S :=
--  --let any_list_of_value := dbgdspec Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) (S // ((@NP (List value)) ∖ S)) 
--  --let is_empty := dbgdspec Prop ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) ("when"::"its"::"contents"::"are"::"empty"::[]) ((@NP (List value)) ∖ S)
--  ---- Yet again, we can't infer semantics for "its contents" even though it's totally trivial. Something about the lexical entries involved are not playing nice with Lean's unification.
--  ----let its_contents := dbgdspec Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value)))
--  ----let its_contents_manual : DSynth Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value))) :=
--  ----  DRApp (L:= DLex (l := its_ref)) (R:=DLex (l := contents_lex))
--  ---- Even with the above manual construction lifted as before to a hack instance, this next bit fails to parse, suggesting a bug in the port of the Jacobson specialization... Ah, yes, it helps to actually open the module with the required local instances
--  ----let its_contents_are_empty := dbgdspec Prop ("its"::"contents"::"are"::"empty"::[]) [] (S % (@NP (List value)))
--  --let when_its_contents_are_empty := dbgdspec Prop ("when"::"its"::"contents"::"are"::"empty"::[]) [] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
--  ----let is_empty_when_its_contents_are_empty := dbgdspec Prop ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] ((@NP (List value)) ∖ S)
--  ----DRapp (L:=any_list_of_value) (R:=is_empty_when_its_contents_are_empty)
--  --(any_list_of_value,is_empty,when_its_contents_are_empty)
--
----set_option synthInstance.maxHeartbeats 8000000
----set_option maxHeartbeats 8000000
----def contents_nil_inv_spec_d_manual_too_much_for_400K : DSynth Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] S :=
--  --let any_list_of_value := dbgdspec Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) (S // ((@NP (List value)) ∖ S)) 
--  --let is_empty_when_its_contents_are_empty := dbgdspec Prop ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] ((@NP (List value)) ∖ S)
--  --DRApp (L:=any_list_of_value) (R:=is_empty_when_its_contents_are_empty)
--  ----(any_list_of_value,is_empty_when_its_contents_are_empty)
--
----  #check @its_ref
----  #check @contents_lex
----set_option trace.Meta.synthInstance.newAnswer true
----set_option trace.Meta.synthInstance.instances true
--  instance its_contents_manual_hack : DSynth Prop 7 9 ((@NP multiset) % (@NP (List value))) :=
--    DRApp (L:= DLex 7 "its" (((@NP multiset) % (@NP (List value))) // (@NP (List value -> multiset)))) (R:=DLex 8 "contents" (@NP (List value -> multiset)))
--    -- Can't infer Nth instances... maybe write nth and nth_instance helpers to manually specify
----  #check @contents_lex
--
----def contents_nil_inv_spec_d_complete : Prop :=
----  dspec ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[])
----def contents_nil_inv_spec_d_complete : DSynth Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] S :=
--  --dbgdspec Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] S 
--end contents_nil_inv_spec
--
----/-
--  --Analysis notes on difflists vs context trees:
--    --Fundamentally, difflists represent all possible associations differently from context trees.
--    --Context trees are in fact binary trees (not ordered in any particular way). The number of binary trees with n nodes is apparently known to be the (n-1)'th [Catalan number](https://en.wikipedia.org/wiki/Catalan_number), which grows exponentially in n. This is also the number of ways to parenthesize a string of n symbols (which is more conceptually what we're doing). While many sentences can be parsed many different ways, the worst case still requires an exponential search, and in practice we must do the full search for at least a sub-sequence of the original sentence for more interesting grammatical constructions.
--
--    --Difflists directly model substrings, without the cost of constructing fresh cons lists for non-suffix substrings.
--    --By only representing substrings rather than all associations of the entire string, the search space is constrained: there are only `n*(n+1)/2` (i.e., quadratic) number of substrings to consider.
--
--    --But, things aren't *quite* that simple, even if this is roughly correct. The mathematical claims above are true, but the use in the context of search is a bit more complicated.
--
--    --The current search strategy for context trees is incomplete. I haven't worked out the math on how starting from a fully right-leaning tree and only including one direction of reassociativity restricts the size of the search space for sentence structure. But we know it's incomplete; some VFA case studies have shown us that. So given how expensive it is in practice *while* also being incomplete in a way that affects examples we care about, it's not clear how important those details really are.
--
--    --In both cases, search is recursive. Every time the difflist implementation picks a tentative split, it must recursively pick splits for each side, and try to parse that. The number of actually total splits is still quadratically bounded (and ultimately probably memoized by the StrictSubList relation + Lean's tabled resolution) for difflists, exponentially bounded for trees. But (I'm speculating Lean implementation details here) the difflists can in principle be represented with a quadratic number of pairs where each element comes from a linear number of actual allocated cons-lists. The trees don't permit the same degree of structure sharing. Though again, I'm speculating as to what degree Lean might be able to take advantage of that, *if* I've exposed that possibility adequately in my definitions, and even then that's at best a small factor compared to the overall memory overhead.
--
--
-----/
--
--
--
------ Here I have to port the 'experiments' section from Multiset to DSynth (those are the rules for variables) and try "for any list of value al for any list of value bl the contents of al equals the contents of bl when al is a permutation of bl" or similar
--