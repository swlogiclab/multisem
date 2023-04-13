import Multisem.Grammar
import Multisem.Text.Macros -- contains ContextTree
open Cat

namespace TreeSpecs

class Synth (P:Type u)(ws:ContextTree String) (c:Cat) where
  denotation : interp P c
  stringRep : Lean.Format
attribute [simp] Synth.denotation

-- The Repr typeclass is how Lean displays results of #eval commands.
-- Implementing this (and for that matter, requiring Synth.stringRep)
-- lets us print the result of a call to specwitness
instance (P:Type u)(ws:ContextTree String) (c:Cat) : Repr (Synth P ws c) where
  reprPrec inst n := inst.stringRep



instance SynthLex (P:Type u){w:String}{C:Cat}[l:lexicon P w C] : Synth P (ContextTree.one w) C where
  denotation := lexicon.denotation w
  stringRep := "lexicon<"++w++":"++ (reprPrec C 0) ++">"

instance SynthRApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 (c1 // c2)][R:Synth P s2 c2] : Synth P (s1#s2) c1 where
  denotation := L.denotation R.denotation --@Synth.denotation P s1 (c1 // c2) L (Synth.denotation s2)
  stringRep := "(SynthRApp "++L.stringRep++" "++R.stringRep++")"
instance SynthLApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 c1][R:Synth P s2 (c1 ∖ c2)] : Synth P (s1#s2) c2 where
  denotation := R.denotation (L.denotation)
  stringRep := "(SynthLApp "++L.stringRep++" "++R.stringRep++")"
--  denotation := @Synth.denotation P _ _ _ R (Synth.denotation s1)

--instance (priority := default-1000) Reassoc (P:Type u){s1 s2 s3 c}[pre:Synth P (s1 ++ (s2 ++ s3)) c] : Synth P ((s1 ++ s2) ++ s3) c where
--  denotation := pre.denotation
instance Reassoc' (P:Type u){s1 s2 s3 c}[pre:Synth P ((s1 # s2) # s3) c] : Synth P (s1 # (s2 # s3)) c where
  denotation := pre.denotation
  stringRep := "(Reassoc' "++pre.stringRep++")"

instance SynthShift (P:Type u){s c l r}[L:Synth P s (l ∖ (c // r))] : Synth P s ((l ∖ c) // r) where
  denotation xr xl := L.denotation xl xr
  stringRep := "(SynthShift "++L.stringRep++")"

instance RComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (c1 // c2)][R:Synth P s' (c2 // c3)] : Synth P (s # s') (c1 // c3) where
  denotation x := L.denotation (R.denotation x)
  stringRep := "(RComp "++L.stringRep++" "++R.stringRep++")"
instance LComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (c1 ∖ c2)][R:Synth P s' (c2 ∖ c3)] : Synth P (s # s') (c1 ∖ c3) where
  denotation x := R.denotation (L.denotation x)
  stringRep := "(LComp "++L.stringRep++" "++R.stringRep++")"

-- Lifting rules for exponents a la Jacobson/Morrill/Carpenter
-- This is used for pronouns and currently for definite articles
-- TODO: lift referents over slash types. Follow Jaeger's exposition.


-- TODO: Need to add type raising!

-- English-specific lifting rules
-- Montague-style lifting for GQs in object position
instance MLift (H:Type u){T U:Type u}{s}[sem:Synth H s (((@NP T) ∖ S) // (@NP U))] :
  Synth H s (((@NP T) ∖ S) // (S // ((@NP U) ∖ S))) where 
  stringRep := "(MLift "++sem.stringRep++")"
  denotation := fun P x => P (fun y => sem.denotation y x)

/-
  The rules in here make the search space *much* larger, so they are disabled
  by default.
-/
namespace Jacobson
  -- Slightly simplified (concretized) Jacobson-style extraction (e.g., for anaphora), per Jaeger (p100)
  -- Jacobson restricts the automatic raising to cases where the extraction is a NP, which is all we need now, and also prevents these from completely trashing performance with unconstrained search
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

  /- Even with the NP restrictions, the above still explode performance because
     they essentially result in TC resolution lifting random transitive verbs and such.
     As an alternative, let's consider what the Z rules actually do:
     they lift function types so they can combine with arguments that have extracted referents. But they allow *unnecessary* lifting.
     What if instead we fused them with application, yielding specialized application rules that only apply when it's necessary to combine with an extraction? That should control the slow-down, but would be subtle.

     These rules are much less general than the arbitrary lifting, because they won't automatically play well with other combinators --- we may end up needing quite a few more of these. Each seems to slow down search a little bit, so we will keep these in their own module: these will be scoped instances. We'll keep the original rules around as local instances (which will never be considered in real searches) so we can prove conservativity
  -/
  /-- A condensation of `GR` and `SynthRApp` -/
  scoped instance AppGR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X (A // B)][arg:Synth P Y (B % (@NP C))]
    : Synth P (X # Y) (A % (@NP C)) where
    denotation := fun c => f.denotation (arg.denotation c)
    stringRep := "(AppGR "++f.stringRep++" "++arg.stringRep++")"
  /-- A condensation of `GL` and `SynthLApp` -/
  scoped instance AppGL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (B % (@NP C))][f:Synth P Y (B ∖ A)]
    : Synth P (X # Y) (A % (@NP C)) where
    denotation := fun c => f.denotation (arg.denotation c)
    stringRep := "(AppGL "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZRR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X ((A // (@NP B)) // C)][arg:Synth P Y (C % (@NP B))]
    : Synth P (X # Y) (A // (@NP B)) where
    denotation := fun n => f.denotation (arg.denotation n) n
    stringRep := "(AppZRR "++f.stringRep++" "++arg.stringRep++")"
  theorem AppZRR_conservative {P X Y A B C}[HeytingAlgebra P]
    (f:Synth P X ((A // (@NP B)) // C))(arg:Synth P Y (C % (@NP B)))
    : (SynthRApp (L := ZRR (base:=f)) (R := arg)).denotation = (AppZRR (f:=f) (arg:=arg)).denotation :=
      by simp
  scoped instance AppZLR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X (((@NP B) ∖ A) // C)][arg:Synth P Y (C % (@NP B))]
    : Synth P (X # Y) ((@NP B) ∖ A) where
    denotation := fun n => f.denotation (arg.denotation n) n
    stringRep := "(AppZLR "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZRL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (C % (@NP B))][f:Synth P Y (C ∖ (A // (@NP B)))]
    : Synth P (X # Y) (A // (@NP B)) where
    denotation := fun n => f.denotation (arg.denotation n) n
    stringRep := "(AppZRL "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZLL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (C % (@NP B))][f:Synth P Y (C ∖ ((@NP B) ∖ A))]
    : Synth P (X # Y) (A // (@NP B)) where
    denotation := fun n => f.denotation (arg.denotation n) n
    stringRep := "(AppLRL "++f.stringRep++" "++arg.stringRep++")"

  -- For now we'll keep the word 'the' under wraps as well
  scoped instance (priority := high) the_lex {P}[HeytingAlgebra P]{T}: lexicon P "the" ((@NP T % @NP T) // (@CN T)) where
    denotation := fun _cn x => x
  /- Another difficulty here is that for modified CNs (those that don't just denote true), this definition discards the restriction --- e.g., 'the even number' could resolve to an 'odd number'!

  One option would be to tweak CNs again to have them also reflect their predicate into the typeclass unification problem. But that will lead to problems with TC search failing for equivalent but not definitionally equal predicates (even positive vs positive even).

  Another approach would be to treat 'the' as a GQ that gets its argument externally (so, type is roughtly GQ|NP, so the semantics capture sentence-combining things), then could apply the CN predicate to whatever gets bound as a sanity check.
  -/

end Jacobson




@[simp]
def dbgspec (l:ContextTree String) (C:Cat) [sem:Synth Prop l C] : interp Prop C :=
  sem.denotation
@[simp]
def pspec (l:ContextTree String) [HeytingAlgebra Prop][sem:Synth Prop l S] : Prop :=
  sem.denotation
@[simp]
def specwitness (P:Type u)(l:ContextTree String) [HeytingAlgebra P][sem:Synth P l S] : Synth P l S := sem
@[simp]
def dbgspecwitness (P:Type u)(l:ContextTree String)(C:Cat) [HeytingAlgebra P][sem:Synth P l C] : Synth P l C := sem

end TreeSpecs