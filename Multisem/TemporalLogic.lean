import Multisem.HeytingAlgebras

def StateFormula (T : Type u) := T -> Prop

instance StateFormulatHeyting (T : Type u): HeytingAlgebra (StateFormula T) := pointwiseHA T Prop

namespace ltl
  inductive LTLFormula (T : Type u) where
    | true : LTLFormula T
    | false : LTLFormula T
    | stateProp : StateFormula T -> LTLFormula T
    | not : LTLFormula T -> LTLFormula T
    | next : LTLFormula T -> LTLFormula T
    | or : LTLFormula T -> LTLFormula T -> LTLFormula T
    -- "until" is a reserved keyword in Lean
    | unt : LTLFormula T -> LTLFormula T -> LTLFormula T
  -- Convenient shorthands for outside this namespace
  def true {T : Type u} : LTLFormula T := LTLFormula.true
  def false {T : Type u} : LTLFormula T := LTLFormula.false
  def or {T : Type u} : LTLFormula T -> LTLFormula T -> LTLFormula T:= LTLFormula.or
  def unt {T : Type u} : LTLFormula T -> LTLFormula T -> LTLFormula T:= LTLFormula.unt
  def next {T : Type u} : LTLFormula T -> LTLFormula T:= LTLFormula.next
  def not {T : Type u} : LTLFormula T -> LTLFormula T:= LTLFormula.not
  
  -- LTL is typically classical, so these are derived in the classic way
  def and {T : Type u} (a b : LTLFormula T) : LTLFormula T :=
    LTLFormula.not (LTLFormula.or (LTLFormula.not a) (LTLFormula.not b))
  def impl {T : Type u} (a b : LTLFormula T) : LTLFormula T :=
    LTLFormula.or (LTLFormula.not a) b
  -- other derived forms
  -- "finally" is a reserved keyword
  def final {T : Type u} (a : LTLFormula T) : LTLFormula T :=
    LTLFormula.unt LTLFormula.true a
  -- TODO: G(lobally)
  
end ltl

namespace ctlstar
  mutual
    inductive CTLStarFormula (T : Type u) where
      | false
      | true
      | stateProp : StateFormula T -> CTLStarFormula T
      | not : CTLStarFormula T -> CTLStarFormula T
      | or : CTLStarFormula T -> CTLStarFormula T -> CTLStarFormula T
      | A : CTLPathFormula T -> CTLStarFormula T
      | E : CTLPathFormula T -> CTLStarFormula T
    inductive CTLPathFormula (T : Type u) where
      | starformula : CTLStarFormula T -> CTLPathFormula T
      | not : CTLPathFormula T -> CTLPathFormula T
      | or : CTLPathFormula T -> CTLPathFormula T -> CTLPathFormula T
      | X : CTLPathFormula T -> CTLPathFormula T
      | F : CTLPathFormula T -> CTLPathFormula T
      | G : CTLPathFormula T -> CTLPathFormula T
      | U : CTLPathFormula T -> CTLPathFormula T -> CTLPathFormula T
    end

  def and {T : Type u} (a b : CTLStarFormula T) : CTLStarFormula T :=
    CTLStarFormula.not (CTLStarFormula.or (CTLStarFormula.not a) (CTLStarFormula.not b))
  def impl {T : Type u} (a b : CTLStarFormula T) : CTLStarFormula T :=
    CTLStarFormula.or (CTLStarFormula.not a) b

end ctlstar

namespace ctl
  inductive CTLFormula (T : Type u) where
    | false
    | true
    | stateProp : StateFormula T -> CTLFormula T
    | not : CTLFormula T -> CTLFormula T
    | or : CTLFormula T -> CTLFormula T -> CTLFormula T
    | EG : CTLFormula T -> CTLFormula T
    | EU : CTLFormula T -> CTLFormula T
    | EX : CTLFormula T -> CTLFormula T
    | AG : CTLFormula T -> CTLFormula T
    | AU : CTLFormula T -> CTLFormula T
    | AX : CTLFormula T -> CTLFormula T
  def and {T : Type u} (a b : CTLFormula T) : CTLFormula T :=
    CTLFormula.not (CTLFormula.or (CTLFormula.not a) (CTLFormula.not b))
  def impl {T : Type u} (a b : CTLFormula T) : CTLFormula T :=
    CTLFormula.or (CTLFormula.not a) b
end ctl

instance LTLHeyting (T : Type u) : HeytingAlgebra (ltl.LTLFormula T) where
  top := ltl.true
  bottom := ltl.false
  conj := ltl.and
  disj := ltl.or
  impl := ltl.impl

instance CTLHeyting (T : Type u) : HeytingAlgebra (ctl.CTLFormula T) where
  top := ctl.CTLFormula.true
  bottom := ctl.CTLFormula.false
  disj := ctl.CTLFormula.or
  conj := ctl.and
  impl := ctl.impl

instance CTLStarHeyting (T : Type u) : HeytingAlgebra (ctlstar.CTLStarFormula T) where
  top := ctlstar.CTLStarFormula.true
  bottom := ctlstar.CTLStarFormula.false
  disj := ctlstar.CTLStarFormula.or
  conj := ctlstar.and
  impl := ctlstar.impl

def ctl_to_ctlstar {T : Type u} (x : ctl.CTLFormula T) : ctlstar.CTLStarFormula T :=
  match x with
  | ctl.CTLFormula.false => ctlstar.CTLStarFormula.false
  | ctl.CTLFormula.true => ctlstar.CTLStarFormula.true
  | ctl.CTLFormula.or a b => ctlstar.CTLStarFormula.or (ctl_to_ctlstar a) (ctl_to_ctlstar b)
  | ctl.CTLFormula.not a => ctlstar.CTLStarFormula.not (ctl_to_ctlstar a)
  | ctl.CTLFormula.stateProp p => ctlstar.CTLStarFormula.stateProp p
  | ctl.CTLFormula.AX a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.X (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.AU a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.U (ctlstar.CTLPathFormula.starformula ctlstar.CTLStarFormula.true) (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.AG a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.G (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EX a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.X (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EU a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.U (ctlstar.CTLPathFormula.starformula ctlstar.CTLStarFormula.true) (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EG a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.G (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))

-- HA Morphisms

-- CTL -> CTL*
instance CTLStarMorphism (T : Type u) : HeytingAlgebraMorphism (ctl.CTLFormula T) (ctlstar.CTLStarFormula T) where
  morph := ctl_to_ctlstar

-- State formulas -> LTL & CTL
instance ltl_state (T : Type u) : HeytingAlgebraMorphism (StateFormula T) (ltl.LTLFormula T) where
  morph := ltl.LTLFormula.stateProp
instance ctl_state (T : Type u) : HeytingAlgebraMorphism (StateFormula T) (ctl.CTLFormula T) where
  morph := ctl.CTLFormula.stateProp

-- State formulas -> CTL* by way of CTL
instance ctl_star_state (T : Type u) : HeytingAlgebraMorphism (StateFormula T) (ctlstar.CTLStarFormula T) where
  morph := HeytingAlgebraMorphism.morph ∘ (@HeytingAlgebraMorphism.morph (StateFormula T) (StateFormulatHeyting T) (ctl.CTLFormula T) (CTLHeyting T) (ctl_state T))
