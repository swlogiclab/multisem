class HeytingAlgebra (P:Type u) where
  top : P
  bottom : P
  conj : P -> P -> P
  disj : P -> P -> P
  impl : P -> P -> P
class HeytingAlgebraLaws (P : Type u) extends HeytingAlgebra P where
  conj_comm : ∀ x y, conj x y = conj y x
  conj_assoc : ∀ x y z, conj (conj x y) z = conj x (conj y z)
  disj_comm : ∀ x y, disj x y = disj y x
  disj_assoc : ∀ x y z, disj (disj x y) z = disj x (disj y z)
  distrib_left : ∀ x y z, conj x (disj y z) = disj (conj x y) (conj x z)
  distrib_right : ∀ x y z, conj (disj x y) z = disj (conj x z) (conj y z)
  -- TODO: missing impl laws

class HeytingAlgebraMorphism (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] where
  morph : P -> Q
class HeytingAlgebraMorphismLaws (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] extends HeytingAlgebraMorphism P Q where
  preserves_top : morph HeytingAlgebra.top = HeytingAlgebra.top
  preserves_bottom : morph HeytingAlgebra.bottom = HeytingAlgebra.bottom
  preserves_conj : ∀ x y, morph (HeytingAlgebra.conj x y) = HeytingAlgebra.conj (morph x) (morph y)
  preserves_disj : ∀ x y, morph (HeytingAlgebra.disj x y) = HeytingAlgebra.disj (morph x) (morph y)
  preserves_impl : ∀ x y, morph (HeytingAlgebra.impl x y) = HeytingAlgebra.impl (morph x) (morph y)


instance pointwiseHA (X : Type v)(H : Type u)[HeytingAlgebra H] : HeytingAlgebra (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)

instance pointwiseHALaws (X : Type v)(H : Type u)[HeytingAlgebraLaws H] : HeytingAlgebraLaws (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)
  conj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_comm }
  conj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_assoc }
  disj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_comm }
  disj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_assoc }
  distrib_left x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_left
  distrib_right x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_right

instance PropHeyting : HeytingAlgebra Prop where
  top := True
  bottom := False
  conj x y := x ∧ y
  disj x y :=  x ∨ y
  impl x y := x -> y