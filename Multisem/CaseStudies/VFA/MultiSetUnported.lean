import Multisem.Text.Macros
import Multisem.Lexicon
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet


  -- Equivalence of Permutation and Multiset Specifications
  -- These require dealing with two lists manipulated in various ways
  -- They also require a range of general list manipulations, which could be generally useful
  -- Arguably some of these are the sorts of "detailed internal specs" that one typically *wouldn't* try to write down explicitly in English

  instance : NLVar "al" where
  instance : NLVar "bl" where
  section experiments
    --open Anaphora

    /-
      These instances do a lot of work, but they're limited to depth one.
      Much of the difficulty and subtlety of grammatical treatments of anaphora is ensuring that arbitrary stacking is handled, regardless of depth, ordering, or repetition.
      The systems I've studied in detail (notably Jacobson's but seemingly also Moortgat's, and based on initial investigations Barker and Shan's) seem to handle this by allowing arbitrary lifting of "whole" fragments to assume compatibility with an arbitrary hole. But of course this blows up search pretty bad because a lot of time is wasted lifting terms that don't need it (and this is with her restriction to NP referents).
    -/
    instance SynthRAppVar (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1 // c2)][R:Synth P s2 (c2 % (@Var T v))] : Synth P (s1#s2) (c1 % (@Var T v)) where
      denotation := λ (t:T) => @Synth.denotation P s1 (c1 // c2) L ((@Synth.denotation _ s2 _ R) t)
      stringRep := "(SynthRAppVar "++L.stringRep++" "++R.stringRep++")"
    instance SynthRAppVarF (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 ((c1 // c2) % (@Var T v))][R:Synth P s2 (c2)] : Synth P (s1#s2) (c1 % (@Var T v)) where
      denotation := λ (t:T) => L.denotation t (Synth.denotation s2) 
      stringRep := "(SynthRAppVarF "++L.stringRep++" "++R.stringRep++")"
    instance SynthLAppVar (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1 % (@Var T v))][R:Synth P s2 (c1 ∖ c2)] : Synth P (s1#s2) (c2 % (@Var T v)) where
      denotation := λ (t:T) => R.denotation (L.denotation t)
      stringRep := "(SynthLAppVar "++L.stringRep++" "++R.stringRep++")"
    instance SynthLAppVarF (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1)][R:Synth P s2 ((c1 ∖ c2) % (@Var T v))] : Synth P (s1#s2) (c2 % (@Var T v)) where
      denotation := λ (t:T) => R.denotation t (L.denotation)
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
      denotation := λ t2 t1 => L.denotation t1 (R.denotation t2)
      stringRep := "(VarStackR"++L.stringRep++" "++R.stringRep++")"
    instance VarStackL (P:Type u){s1 s2}{C1 C2}{v1 v2}{T1 T2}
      [L:Synth P s1 (C1 % (@Var v1 T1))]
      [R:Synth P s2 ((C1 ∖ C2) % (@Var v2 T2))]
      : Synth P (s1#s2) ((C2 % (@Var v2 T2)) % (@Var v1 T1)) where
      denotation := λ t1 t2 => R.denotation t2 (L.denotation t1)
      stringRep := "(VarStackR"++L.stringRep++" "++R.stringRep++")"
    instance VarMatchR (P:Type u){s1 s2}{C1 C2}{v}{T}
      [L:Synth P s1 ((C1 // C2) % (@Var v T))]
      [R:Synth P s2 (C2 % (@Var v T))]
      : Synth P (s1#s2) ((C1 % (@Var v T))) where
      denotation := λ t => L.denotation t (R.denotation t)
      stringRep := "(VarMatchR"++L.stringRep++" "++R.stringRep++")"
    instance VarMatchL (P:Type u){s1 s2}{C1 C2}{v}{T}
      [L:Synth P s1 (C1 % (@Var v T))]
      [R:Synth P s2 ((C1 ∖ C2) % (@Var v T))]
      : Synth P (s1#s2) ((C2 % (@Var v T))) where
      denotation := λ t => R.denotation t (L.denotation t)
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
    instance A_when_B_abs2 {H}[ha:HeytingAlgebra H]{v v'}{T T'} : lexicon H "when" (((S % (@Var v' T')) % (@Var v T)) ∖ (((S % (@Var v' T')) % (@Var v T)) // ((S % (@Var v' T')) % (@Var v T)))) where
      denotation := λ concl hyp x y => ha.impl (hyp x y) (concl x y)

    def _checklift := dbgspecwitness Prop "if" 
      (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) // ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))))
    def _checkshift := dbgspecwitness Prop "if" ((((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))) // ((S % (@Var ( List value) "bl")) % (@Var (List value) "al")))
    def _3 := dbgspecwitness Prop ("if" # [| al is a permutation of bl |]) (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al")))
    def _3manual : Synth Prop ("if" # [| al is a permutation of bl |]) (((S % (@Var ( List value) "bl")) % (@Var (List value) "al")) ∖ ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))) :=
      SynthRApp (L:= _checkshift) (R:=_a)
    def _4a := dbgspecwitness Prop ([| the contents of al |]) ((@NP multiset) % (@Var (List value) "al"))
    def _4b := dbgspecwitness Prop ([| the contents of bl |]) ((@NP multiset) % (@Var (List value) "bl"))
    -- Okay, this doesn't work because 'equals' is in Misc instead of Lexicon
    def _4b' := dbgspecwitness Prop ([| equals the contents of bl |]) (((@NP multiset) ∖ S) % (@Var (List value) "bl"))
    def _4 := dbgspecwitness Prop ([| the contents of al equals the contents of bl |]) ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))
    def _5_manual0 := SynthRApp (L:=SynthLApp (L:=_4) (R:=SynthLex (l:=A_when_B_abs2))) (R:=_a)
    def _5_manual := Reassoc' (pre:=_5_manual0)
    --def _5_manual' := Reassoc' (pre:=Reassoc' (pre:=_5_manual))
    --#check _5_manual'
--instance (priority := low) Reassoc (P:Type u){s1 s2 s3 c}[pre:Synth P (s1 # (s2 # s3)) c] : Synth P ((s1 # s2) # s3) c where
--  denotation := pre.denotation
--  stringRep := "(Reassoc "++pre.stringRep++")"
    -- Holding off on this, currently failing due to some missing associativity stuff (probably)
    --def _5 := dbgspecwitness Prop ([| the contents of al equals the contents of bl when al is a permutation of bl |]) ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))
    
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
  def perm_contents_tail:=
    dbgspecwitness Prop [| al is a permutation of bl|]

  -- No Explicit English
  -- Note: This would be a nice demonstration of grammatical flexibiliy, dealing with nested quantifier scopes
  -- Candidate: if any list has empty contents that list is empty
  -- Candidate: any list is empty if <something about looking up the count of any key in contents>
  -- Candidate: any list is empty if its contents are empty

  /-
    Why doesn't this resolve? It's literally just a rightward application with two lexicon entries from *this* file!
  -/
  --def its_contents_auto := dbgspecwitness Prop [|its contents|] ((@NP multiset) % (@NP (List value)))

  #check contents
  def contents_nil_inv_raw := ∀ l, (∀ x, 0 = contents l x) -> l = []
  open Jacobson
  -- TODO: Currently fails even with higher heartbeat count, need to verify it actually parses the way I intend
  -- Currently working around the fact that "if" isn't a valid Lean identifier by using "when"
    /-- This instance shouldn't be necessary for ANYTHING. It should be *trivially* derivable. but for whatever reason, this doesn't get derived! -/
    instance its_contents_manual_external : Synth Prop [|its contents|] ((@NP multiset) % (@NP (List value))) := SynthRApp (L:= SynthLex (l := its_ref)) (R:= SynthLex (l:= contents_lex))
    #check its_contents_manual_external
  -- TODO: plural values
  def contents_nil_inv_spec := pspec [| any list of value is empty when its contents are empty |]
  section _dbg
    def its_contents_are_empty := dbgspecwitness Prop [|its contents are empty |] (S % (@NP (List value)))
    def its_contents_are_empty' : Synth Prop [|its contents are empty |] (S % (@NP (List value))) :=
      --let are_empty := dbgspecwitness Prop [|are empty|] ((@NP multiset) ∖ S)
      /- Okay, this is weird: This `its_contents_manual` isn't directly used, but having it in scope seems to get it picked up when inferring the full spec.
         But there's no reason this should matter: it's just a right application! So one of several things must be happening:
         - AppGL doesn't fire unless this unit is already in scope
           + Seems pretty unlikely
         - This particular associativity isn't explored
           + Seems pretty unlikely since it just requires one use of `Reassoc'`, and once this is in scope that's found w/o issue
         - For some reason it simply doesn't try this right application?
           + As bizarre as this is, it's consistent with the above issue where trying to synthesize the same type automatically fails even though it's trivial. There's a remote possibility there's an issue unifying some implicit argument somewhere, but the only issue I can predict there is the value vs Nat issue, which I've probed and discarded as a cause.
           + I think we can also rule out inability to choose an instantiation, since "contents" only has one lexical entry here
         - This trips over some subtlety of Lean's unification algorithm
         - This is a bug in TC search
      -/
      let _its_contents_manual := SynthRApp (L:= SynthLex (l := its_ref)) (R:= SynthLex (l:= contents_lex))
      --let its_contents := dbgspecwitness Prop [|its contents|] ((@NP multiset) % (@NP (List value)))
      --let full := AppGL (arg := its_contents) (f := are_empty)
      --Reassoc' (pre:=full)
      dbgspecwitness Prop [|its contents are empty|] (S % (@NP (List value)))
  
    def when_ := dbgspecwitness Prop [|when its contents are empty|] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
    def when_manual := SynthRApp (L:=SynthLex (l:=when_lwhent_ref)) (R:= its_contents_are_empty') --dbgspecwitness Prop [|when its contents are empty|] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
    def after_all := Reassoc' (pre:= SynthLApp (L := dbgspecwitness Prop [|is empty|] ((@NP (List value)) ∖ S)) (R := when_manual))
    -- TODO: plural values
    def list_of_nats := dbgspecwitness Prop [|list of value|] (@CN (List value))
    def finished_manual_missing_assoc :=
      SynthRApp (L:= SynthRApp (L:=SynthLex (l:=any_head)) (R:=list_of_nats)) (R:=after_all)
    #eval finished_manual_missing_assoc
    #check (Reassoc' (pre:=finished_manual_missing_assoc))
    -- depends on the hack for 'its contents'...
    def after_all_inferred := dbgspecwitness Prop [|is empty when its contents are empty|] ((@NP (List value) ∖ S))

    def _consistent : contents_nil_inv_raw -> finished_manual_missing_assoc.denotation :=
      by simp [contents_nil_inv_raw, finished_manual_missing_assoc,after_all,when_manual,its_contents_are_empty']
         intros H x _
         apply H

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
