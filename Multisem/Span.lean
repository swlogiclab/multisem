import Multisem.Text.Macros
import Multisem.Lexicon
open Cat

/-- Let's try to use Span to map ranges to trees -/
class Span (P:Type)[HeytingAlgebra P] (i j : Nat) (c:Cat) where
  tree : ContextTree String
  synth : interp P c

class Index (s:String) (i:Nat) where

instance span_index {P}[HeytingAlgebra P]{s}{i}{c}[l:lexicon P s c][idx:Index s i] : Span P i (Nat.succ i) c where
  tree := s
  synth := l.denotation

instance span_RApp {P}[HeytingAlgebra P]{i j k}{A B}[L:Span P i j (A // B)][R:Span P j k B] : Span P i k A where
  tree := (L.tree # R.tree)
  synth := L.synth (R.synth)
instance span_LApp {P}[HeytingAlgebra P]{i j k}{A B}[L:Span P i j B][R:Span P j k (B ∖ A)] : Span P i k A where
  tree := (L.tree # R.tree)
  synth := R.synth (L.synth)

def span_sem {P}[HeytingAlgebra P](n)[parse:Span P 0 n S] : interp P S := parse.synth

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
#check Span.synth
def three_is_even_tire_kicking 
  [a:Index "three" 0]
  [b:Index "is" (Nat.succ Nat.zero)]
  [c:Index "even" (Nat.succ (Nat.succ Nat.zero))]
: Prop :=
  --/- So without these manual hinds here, the "excursions" into the lexicon or index entries get stuck (which one depends on how I reorder the lexicon and Index args to span_index). The number along isn't enough for it to get to the lexicon. But as soon as I explicitly supply the index or lexicon entry, the other is resolved...-/
  --let d : Span Prop 0 1 (@NP Nat) := span_index (l:=threelex) --(idx:=a)
  --let e : Span Prop 1 2 (((@NP Nat) ∖ S) // (@ADJ Nat)) := span_index (idx:=b)
  --let f : Span Prop 2 3 (@ADJ Nat) := span_index (l:=evenlex)
  --let g : Span Prop 1 3 ((@NP Nat) ∖ S) := span_RApp (L:=e) (R:=f)
  --let h : Span Prop 0 3 S := span_LApp (L:= d) (R := g)
  --h.synth
  Span.synth 0 (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (c:=S)
  --let e : Span Prop 1 1 (((@NP Nat) ∖ S) // (@ADJ Nat)) := _
  --span_sem 2
  --by simp [span_index]
     --apply (@Span.synth Prop (c:= S))