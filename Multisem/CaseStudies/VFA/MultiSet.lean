import Multisem.Text.Macros
import Multisem.Lexicon
import Multisem.CaseStudies.VFA.Sort

section multiset

  /- Note: VFA does a lot of this definition of short-hands for types,
     which interacts poorly with Lean's typeclass inference. Marking
     things `@[simp]` is supposed to make them transparent to typeclass
     inference, but this doesn't always work.
     On one hand this is a pain, on the other hand it's a good indication
     that doing this *outside* the proof assistant could be even worse,
     because in that setting you'd have to duplicate the equivalence checking
     in an external tool
  -/
  @[simp]
  def value := Nat
  attribute [simp] value
  deriving instance BEq for value

  def multiset := value -> Nat

  def empty : multiset := λ _x => 0

  def singleton (v:value) : multiset :=
    λ x => if x == v then 1 else 0

  def union (a b : multiset) : multiset :=
    λ x => a x + b x

  def contents (al : List value) : multiset :=
    match al with
    | [] => empty
    | a :: bl => union (singleton a) (contents bl)

  def is_a_sorting_algorithm' (f : List Nat -> List Nat) :=
    ∀ al, contents al = contents (f al) ∧ sort.sorted (f al)

end multiset

section specs

  open Cat

  section relocate_later
    instance assoc {T:Type}: lexicon Prop "associative" (@ADJ (T -> T -> T)) where
      denotation := λ f => ∀ a b c, f a (f b c) = f (f a b) c
    instance comm {T:Type}: lexicon Prop "commutative" (@ADJ (T -> T -> T)) where
      denotation := λ f => ∀ a b, f a b = f b a
    instance preserves_lex {X Y : Type}: lexicon Prop "preserves" (((@NP (X -> X)) ∖ S) // (@NP (X -> Y))) where
      denotation prop f := ∀ x, prop x = prop (f x)
    instance the_X_of_Y {X Y : Type}: lexicon Prop "the" (((@NP Y) // (@PP X PPType.OF)) // (@NP (X -> Y))) where
      denotation := fun f x => f x
  end relocate_later

  section locallex
    -- TODO: The lexicon decl needs an extra universe variable, if H is in an arbitrary universe here then it expects the operation type to be in the same universe
    instance union_lex (H:Type) : lexicon H "union" (@NP (multiset -> multiset -> multiset)) where
      denotation := union
    instance contents_lex : lexicon Prop "contents" (@NP (List value -> multiset)) where
      denotation := contents
    instance sort_np : lexicon Prop "sort" (@NP  (List value -> List value)) where
      denotation := sort.sort
    instance sorts_lex2 : lexicon Prop "sorts" ((@NP (List value -> List value)) ∖ S) where
      denotation f := ∀ l, sort.sorted (f l)

  end locallex

  -- General Multiset Specs

  -- Original: Prove that multiset union is associative
  @[simp]
  def union_assoc_raw := ∀ (a b c: multiset), union a (union b c) = union (union a b) c
  @[simp]
  def union_assoc_spec := pspec [| union is associative |]

  theorem union_assoc_consistent : union_assoc_raw -> union_assoc_spec :=
    by simp
       intro H
       apply H

  -- Original: Prove that multiset union is commutative
  @[simp]
  def union_comm_raw := ∀ (a b: multiset), union a b = union b a
  @[simp]
  def union_comm_spec := pspec [| union is commutative |]

  -- Original: Prove that multisets in a nested union can be swapped
  /- Note: This original is actually ambiguous, nothing explicitly 
     suggests that you're swapping in and out of the inner union,
     this text in isolation could mean
     `union a (union b c) = union a (union c b)`
     which is just a consequence of commutativity.
     In fact, the entire property itself follows trivially from commutativity and associativity. The only way this makes sense to describe is as the naive transliteration of the formal spec.

     Codex (davinci-002), prompted with a Coq comment, the core definitions, and a comment with this original description proves something equivalent to what's sought here, but it's worth noting that VFA and countless student solution attempts are in its training set!
  -/
  -- I don't think this makes sense
  @[simp]
  def union_swap_raw := ∀ (a b c : multiset), union a (union b c) = union b (union a c)
  @[simp]
  def union_swap_spec := pspec [|TBD|]
  theorem union_swap_consistent : union_swap_raw -> union_swap_spec :=
    by simp
       intro H
       sorry

  -- Verification of Insertion Sort

  /- TODO: To finish this batch of specs, I really need
     - support for multiple named variables
     - support for 'the' to refer to a referent (named or unnamed) introduced by a quantifier 

     Ideally I could read a solution to the first straight out of Ranta, though I could probably just tweak Jacobson's approach to work with a "named NP" construct used only for the 'hole' with discourse referents, coupled with named-quantifier forms "any list l"). Plus a tag/decl typeclass for marking which identifiers can be converted to variable references (via a lexicon instance). This is basically two minor variations on a single extension, and gets us through this chapter's specs.
  -/

  -- Original: Prove that insertion sort's insert function produces the same contents as merely prepending the inserted element to the front of the list
  -- Note: This is very verbose, and can be said much more succinctly
  -- Proposal: insertion of any value preserves contents
  -- Note: value was chosen here rather than natural for unification purposes
  @[simp]
  def insert_contents_raw := ∀ x l, contents (sort.insert x l) = contents (x :: l)
  instance insertion_func : lexicon Prop "insertion" ((@NP (List value -> List value)) // (@PP value PPType.OF)) := sort.sort_specs.insertion_func
  instance val_noun : lexicon Prop "value" (@CN value) := { denotation := fun _ => True }
  @[simp]
  def insert_contents_spec := pspec [| insertion of any value preserves contents |]
  theorem insert_contents_consistent : insert_contents_raw -> insert_contents_spec :=
    by simp
       intro H a x
       -- Aha! Indeed, this is wrong because there's no cons here

  -- Original: Prove that insertion sort preserves contents
  @[simp]
  def sort_contents_raw := ∀ l, contents l = contents (sort.sort l)
  @[simp]
  def sort_contents_spec := pspec [| sort preserves contents |]
  theorem sort_contents_consistent : sort_contents_raw -> sort_contents_spec :=
    λ x => x

  -- No original given
  -- Note: This pretty much translates the intuition behind `is_a_sorting_algorithm'`
  @[simp]
  def insertion_sort_correct_raw := is_a_sorting_algorithm' sort.sort
  @[simp]
  def insertion_sort_correct_spec2 := pspec [| sort preserves contents and sorts |]
  theorem insertion_sort_correct_consistent 
    : insertion_sort_correct_raw -> insertion_sort_correct_spec2 :=
    by simp
       simp [is_a_sorting_algorithm']
       intro H
       apply And.intro
       . intro x
         exact ((H x).1)
       . intro x
         exact ((H x).2)


  -- Equivalence of Permutation and Multiset Specifications
  -- These require dealing with two lists manipulated in various ways
  -- They also require a range of general list manipulations, which could be generally useful
  -- Arguably some of these are the sorts of "detailed internal specs" that one typically *wouldn't* try to write down explicitly in English

  instance : NLVar "al" where
  instance : NLVar "bl" where
  section experiments
    --open Anaphora
    instance permutation_list : lexicon Prop "permutation" ((@CN (List value)) // (@PP (List value) PPType.OF)) where
      denotation := λ a b => sort.Permutation a b 

    /-
      These instances do a lot of work, but they're limited to depth one.
      Much of the difficulty and subtlety of grammatical treatments of anaphora is ensuring that arbitrary stacking is handled, regardless of depth, ordering, or repetition.
      The systems I've studied in detail (notably Jacobson's but seemingly also Moortgat's, and based on initial investigations Barker and Shan's) seem to handle this by allowing arbitrary lifting of "whole" fragments to assume compatibility with an arbitrary hole. But of course this blows up search pretty bad because a lot of time is wasted lifting terms that don't need it (and this is with her restriction to NP referents).
    -/
    instance SynthRAppVar (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1 // c2)][R:Synth P s2 (c2 % (@Var T v))] : Synth P (s1#s2) (c1 % (@Var T v)) where
      denotation := λ (t:T) => @Synth.denotation P s1 (c1 // c2) L ((@Synth.denotation _ s2 _ R) t)
      stringRep := "(SynthRAppVar "++L.stringRep++" "++R.stringRep++")"
    instance SynthRAppVarF (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 ((c1 // c2) % (@Var T v))][R:Synth P s2 (c2)] : Synth P (s1#s2) (c1 % (@Var T v)) where
      denotation := λ (t:T) => L.denotation _ t (Synth.denotation s2) 
      stringRep := "(SynthRAppVarF "++L.stringRep++" "++R.stringRep++")"
    instance SynthLAppVar (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1 % (@Var T v))][R:Synth P s2 (c1 ∖ c2)] : Synth P (s1#s2) (c2 % (@Var T v)) where
      denotation := λ (t:T) => R.denotation _ (L.denotation _ t)
      stringRep := "(SynthLAppVar "++L.stringRep++" "++R.stringRep++")"
    instance SynthLAppVarF (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1)][R:Synth P s2 ((c1 ∖ c2) % (@Var T v))] : Synth P (s1#s2) (c2 % (@Var T v)) where
      denotation := λ (t:T) => R.denotation _ t (L.denotation)
      stringRep := "(SynthLAppVarF "++L.stringRep++" "++R.stringRep++")"
    -- Seems important but blows up search time
    --instance VarFold (P:Type u){s1}{C}{v}{T}[sem:Synth P s1 ((C % (@Var T v)) % (@Var T v))] : Synth P s1 (C % (@Var T v)) where
    --  denotation := λ t => sem.denotation _ t t
    --  stringRep := "(VarFold "++sem.stringRep++")"

    -- For now we'll limit ourselves to two variables
    -- Note the convention that the argument hole becomes the outer binder
    instance VarStackR (P:Type u){s1 s2}{C1 C2}{v1 v2}{T1 T2}
      [L:Synth P s1 ((C1 // C2) % (@Var v1 T1))]
      [R:Synth P s2 (C2 % (@Var v2 T2))]
      : Synth P (s1#s2) ((C1 % (@Var v1 T1)) % (@Var v2 T2)) where
      denotation := λ t2 t1 => L.denotation _ t1 (R.denotation _ t2)
      stringRep := "(VarStackR"++L.stringRep++" "++R.stringRep++")"
    instance VarStackL (P:Type u){s1 s2}{C1 C2}{v1 v2}{T1 T2}
      [L:Synth P s1 (C1 % (@Var v1 T1))]
      [R:Synth P s2 ((C1 ∖ C2) % (@Var v2 T2))]
      : Synth P (s1#s2) ((C2 % (@Var v2 T2)) % (@Var v1 T1)) where
      denotation := λ t1 t2 => R.denotation _ t2 (L.denotation _ t1)
      stringRep := "(VarStackR"++L.stringRep++" "++R.stringRep++")"
    instance VarMatchR (P:Type u){s1 s2}{C1 C2}{v}{T}
      [L:Synth P s1 ((C1 // C2) % (@Var v T))]
      [R:Synth P s2 (C2 % (@Var v T))]
      : Synth P (s1#s2) ((C1 % (@Var v T))) where
      denotation := λ t => L.denotation _ t (R.denotation _ t)
      stringRep := "(VarMatchR"++L.stringRep++" "++R.stringRep++")"
    instance VarMatchL (P:Type u){s1 s2}{C1 C2}{v}{T}
      [L:Synth P s1 (C1 % (@Var v T))]
      [R:Synth P s2 ((C1 ∖ C2) % (@Var v T))]
      : Synth P (s1#s2) ((C2 % (@Var v T))) where
      denotation := λ t => R.denotation _ t (L.denotation _ t)
      stringRep := "(VarMatchR"++L.stringRep++" "++R.stringRep++")"

    def _bl := dbgspecwitness Prop [|bl|] (@NP (List value) % (@Var (List value) "bl"))
    def _al := dbgspecwitness Prop [|al|] (@NP (List value) % (@Var (List value) "al"))
    def _of_bl := dbgspecwitness Prop [|of bl|] ((@PP (List value) PPType.OF) % (@Var (List value) "bl"))
    def _b := dbgspecwitness Prop [|permutation of bl|] ((@CN (List value)) % (@Var (List value) "bl"))
    def _c := dbgspecwitness Prop [|a permutation of bl|] (((((@NP (List value)) ∖ S) // (@ADJ (List value))) ∖ ((@NP (List value)) ∖ S)) % (@Var (List value) "bl"))
    def _d := dbgspecwitness Prop [|is a permutation of bl|] (((@NP (List value)) ∖ S) % (@Var (List value) "bl"))

    def _a := dbgspecwitness Prop [| al is a permutation of bl |] ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))

    -- 'if' should lift as a coordinator for ((S % (@Var ( List value) "bl")) % (@Var (List value) "al")), then shift to take right arg first, resulting in something that looks left
    -- TODO: Okay, apparently adding "if" as a coordinator causes performance problems, but also it's actually wrong in a way, because we don't want to say stuff like "(even if odd) three" or "5 ((is 3) if (is 4)"
    -- TODO: The reasons for the performance issues are unclear
    -- So we need a separate 'if' lexicon entry. We'd like if to work on only the ref surface heyting algebras, not all surface HAs.

    -- Can't decide if "if" should be handled via a similar lifting process to coordinators (but distinct and only for anaphra, per above), or something else. In the mean time let's just write a few special cases we'd like to be able to ideally derive, to make forward progress
    instance A_if_B_base {H}[ha:HeytingAlgebra H] : lexicon H "if" (S ∖ (S // S)) where
      denotation := λ concl hyp => ha.impl hyp concl
    instance A_if_B_abs1 {H}[ha:HeytingAlgebra H]{v}{T} : lexicon H "if" ((S % (@Var v T)) ∖ ((S % (@Var v T)) // (S % (@Var v T)))) where
      denotation := λ concl hyp x => ha.impl (hyp x) (concl x)
    instance A_if_B_abs2 {H}[ha:HeytingAlgebra H]{v v'}{T T'} : lexicon H "if" (((S % (@Var v' T')) % (@Var v T)) ∖ (((S % (@Var v' T')) % (@Var v T)) // ((S % (@Var v' T')) % (@Var v T)))) where
      denotation := λ concl hyp x y => ha.impl (hyp x y) (concl x y)

    def _checklift := dbgspecwitness Prop "if" 
      (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) // ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))))
    def _checkshift := dbgspecwitness Prop "if" ((((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))) // ((S % (@Var ( List value) "bl")) % (@Var (List value) "al")))
    set_option synthInstance.maxHeartbeats 200000
    def _3 := dbgspecwitness Prop ("if" # [| al is a permutation of bl |]) (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al")))
    def _3manual : Synth Prop ("if" # [| al is a permutation of bl |]) (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))) :=
      SynthRApp (L:= _checkshift) (R:=_a)
    
    -- not actually useful, but poking at coordination
    -- times out
    --def _a' := dbgspecwitness Prop [| al is a permutation of bl and al is a permutation of bl|] ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))

    -- Now we need the binders for 
  end experiments

  -- No explicit English
  -- Candidate: the contents of any list al equal the contents of any list bl if al is a permutation of bl
  /- TODO: Currently we have enough to do:
    "the contents of al equals the contents of bl if al is a permutation of bl"
    but we need to introduce the quantifiers.
    Doing this via "for any list al and any list bl" requires either special-casing 'for' in somem weird ways or preferably over-loading 'and' to conjoin quantifiers, ideally so the result looks for a sentence missing those two variables (in the right nesting order...)

    The alternative is to arrange for 'any list bl' to turn into a GQ in the appropriate way in 'the contents of any list al equal the contents of any list bl if ...'. This would really be the ideal approach, but the quantifier types seem quite complex... unless there's something crystal clear I missed in Steedman's Taking Scope. Long-term the ideal would be to implement Shan and Barker's continuation types, but this is too much of a detour for now.
  -/
  def perm_contents_raw := ∀ al bl, sort.Permutation al bl -> contents al = contents bl

  -- No Explicit English
  -- Note: This would be a nice demonstration of grammatical flexibiliy, dealing with nested quantifier scopes
  -- Candidate: if any list has empty contents that list is empty
  -- Candidate: any list is empty if <something about looking up the count of any key in contents>
  instance empty_multiset : lexicon Prop "empty" (@ADJ multiset) where
    denotation := λ ms => ∀ x, 0 = ms x
  instance empty_list {T:Type}: lexicon Prop "empty" (@ADJ (List T)) where
    denotation := λ l => l = []
  -- Candidate: any list is empty if its contents are empty
  /--
    This instance feels slightly over-specialized, like it should be derivable from a more general property.
    It seems to be in the same spirit as e.g. `Multisem.Grammar.Jacobson.ZRR`, but the version of Jacobson's
    work I took that from (Gerhard 2005) didn't address anaphora across coordinators.
  -/
  instance if_lift_ref {A:Type}: lexicon Prop "if" ((((@NP A) ∖ S) ∖ ((@NP A) ∖ S)) // (S % (@NP A))) where
    denotation := λ r l x => r x -> l x
  instance when_lwhent_ref {A:Type}: lexicon Prop "when" ((((@NP A) ∖ S) ∖ ((@NP A) ∖ S)) // (S % (@NP A))) where
    denotation := λ r l x => r x -> l x
  instance its_ref {A B:Type}: lexicon Prop "its" (((@NP B) % (@NP A)) / (@NP (A -> B))) where
    denotation := λ p a => p a
  instance any_head {A:Type}: lexicon Prop "any" ((S // ((@NP A) ∖ S)) // (@CN A)) where
    denotation := λ p rest => ∀ (x:A), p x -> rest x
  instance are_adj_lex {A:Type}: lexicon Prop "are" (((@NP A) ∖ S) // (@ADJ A)) where
    denotation := λ p x => p x

  #check contents
  def contents_nil_inv_raw := ∀ l, (∀ x, 0 = contents l x) -> l = []
  open Jacobson
  -- TODO: Currently fails even with higher heartbeat count, need to verify it actually parses the way I intend
  -- Currently working around the fact that "if" isn't a valid Lean identifier by using "when"
  def contents_nil_inv_spec := pspec [| any list is empty when its contents are empty |]
  section _dbg
    def its_contents_are_empty := dbgspecwitness Prop [|its contents are empty |] (S % (@NP (List value)))
    /-
      Why doesn't this resolve? It's literally just a rightward application with two lexicon entries from *this* file!
    -/
    def its_contents_auto := dbgspecwitness Prop [|its contents|] ((@NP multiset) % (@NP (List value)))
    def its_contents_are_empty' : Synth Prop [|its contents are empty |] (S % (@NP (List value))) :=
      --let are_empty := dbgspecwitness Prop [|are empty|] ((@NP multiset) ∖ S)
      /- Okay, this is weird: This `its_contents_manual` isn't directly used, but having it in scope seems to get it picked up when inferring the full spec.
         But there's no reason this should matter: it's just a right application! So one of several things must be happening:
         - AppGL doesn't fire unless this unit is already in scope
         - This particular associativity isn't explored
           + Seems pretty unlikely since it just requires one use of `Reassoc'`
         - For some reason it simply doesn't try this right application?
           + As bizarre as this is, it's consistent with the above issue where trying to synthesize the same type automatically fails even though it's trivial. There's a remote possibility there's an issue unifying some implicit argument somewhere, but the only issue I can predict there is the value vs Nat issue, which I've probed and discarded as a cause.
           + I think we can also rule out inability to choose an instantiation, since "contents" only has one lexical entry here
      -/
      let its_contents_manual := SynthRApp (L:= SynthLex (l := its_ref)) (R:= SynthLex (l:= contents_lex))
      --let its_contents := dbgspecwitness Prop [|its contents|] ((@NP multiset) % (@NP (List value)))
      --let full := AppGL (arg := its_contents) (f := are_empty)
      --Reassoc' (pre:=full)
      dbgspecwitness Prop [|its contents are empty|] (S % (@NP (List value)))
  
    def its_contents_manual_external := SynthRApp (L:= SynthLex (l := its_ref)) (R:= SynthLex (l:= contents_lex))
    #check its_contents_manual_external

    def when_ := dbgspecwitness Prop [|when its contents are empty|] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
    def when_manual := SynthRApp (L:=SynthLex (l:=when_lwhent_ref)) (R:= its_contents_are_empty') --dbgspecwitness Prop [|when its contents are empty|] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
    def after_all := Reassoc' (pre:= SynthLApp (L := dbgspecwitness Prop [|is empty|] ((@NP (List value)) ∖ S)) (R := when_manual))
    -- TODO: plural values
    def list_of_nats := dbgspecwitness Prop [|list of value|] (@CN (List value))
    def finished_manual_missing_assoc :=
      SynthRApp (L:= SynthRApp (L:=SynthLex (l:=any_head)) (R:=list_of_nats)) (R:=after_all)
    #eval finished_manual_missing_assoc

  end _dbg

  -- No Explicit English
  def contents_cons_inv_raw := ∀ l x n,
    Nat.succ n = contents l x ->
    (∃ l1 l2,
      l = l1 ++ x :: l2
      ∧ contents (l1 ++ l2) x = n)
  
  -- No Explicit English
  def contents_insert_other_raw := ∀ l1 l2 x y,
    y ≠ x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y

  -- No Explicit English
  -- Proposal, reverse the sentence structure of the perm -> content sentence
  def contents_perm_raw := ∀ al bl, contents al = contents bl -> sort.Permutation al bl

  -- No Explicit English
  def same_contents_iff_perm_raw := ∀ al bl, contents al = contents bl ↔ sort.Permutation al bl
  -- Semi-specified in English, "the two specifications are equivalent"
  -- TODO: How subtle is the grammar for "if and only if"?
  -- TODO: Makes sense to unfold *both* definitions
  #print sort.is_a_sorting_algorithm
  def sort_specifications_equivalent_raw := ∀ f, sort.is_a_sorting_algorithm f ↔ is_a_sorting_algorithm' f


    


end specs