import Mathlib.Tactic

inductive SecurityLevel where
  | Pub : SecurityLevel
  | Sec : SecurityLevel
  deriving DecidableEq, Repr

/-
The security level semiring S is a two-point lattice of
security levels S = {Pub ⊑ Sec} with
• 0 = Sec
• 1 = Pub
• Addition as the meet: r + s = r ⊓ s
• Multiplication as the join r · s = r ⊔ s
-/

namespace SecurityLevel

instance : Zero SecurityLevel := ⟨Sec⟩
instance : One SecurityLevel := ⟨Pub⟩

instance : Lattice SecurityLevel where
  le := fun a b =>
    match a, b with
    | Pub, Pub => True
    | Pub, Sec => True
    | Sec, Pub => False
    | Sec, Sec => True
  le_refl := by intro a; cases a <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> trivial
  sup := fun a b =>
    match a, b with
    | Pub, Pub => Pub
    | Pub, Sec => Sec
    | Sec, Pub => Sec
    | Sec, Sec => Sec
  le_sup_left := by intro a b; cases a <;> cases b <;> trivial
  le_sup_right := by intro a b; cases a <;> cases b <;> trivial
  sup_le := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial
  inf := fun a b =>
    match a, b with
    | Pub, Pub => Pub
    | Pub, Sec => Pub
    | Sec, Pub => Pub
    | Sec, Sec => Sec
  inf_le_left := by intro a b; cases a <;> cases b <;> trivial
  inf_le_right := by intro a b; cases a <;> cases b <;> trivial
  le_inf := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial

-- Convenient notations
notation "R0" => (Sec : SecurityLevel)
notation "R1" => (Pub : SecurityLevel)
-- Custom notations specialized to `SecurityLevel`
infixl:65 " +R " => (fun a b : SecurityLevel => a ⊓ b)
infixl:70 " *R " => (fun a b : SecurityLevel => a ⊔ b)
notation:50 " ≤R " => (fun a b : SecurityLevel => a ≤ b)

-- Simplification lemmas for + (meet)
@[simp] theorem add_sec_left (a : SecurityLevel) : Sec +R a = a := by cases a <;> rfl
@[simp] theorem add_sec_right (a : SecurityLevel) : a +R Sec = a := by cases a <;> rfl
@[simp] theorem add_pub_left (a : SecurityLevel) : Pub +R a = Pub := by cases a <;> rfl
@[simp] theorem add_pub_right (a : SecurityLevel) : a +R Pub = Pub := by cases a <;> rfl

-- Simplification lemmas for * (join)
@[simp] theorem mul_pub_left (a : SecurityLevel) : Pub *R a = a := by cases a <;> rfl
@[simp] theorem mul_pub_right (a : SecurityLevel) : a *R Pub = a := by cases a <;> rfl
@[simp] theorem mul_sec_left (a : SecurityLevel) : Sec *R a = Sec := by cases a <;> rfl
@[simp] theorem mul_sec_right (a : SecurityLevel) : a *R Sec = Sec := by cases a <;> rfl

instance : CommSemiring SecurityLevel where
  -- AddCommMonoid
  add := fun a b : SecurityLevel => a ⊓ b
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero := Sec
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  nsmul := fun
    | 0, _ => 0
    | Nat.succ _, a => a
  nsmul_zero := by intro a; rfl
  nsmul_succ := by intro n a; cases n <;> cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl

  -- MonoidWithZero
  mul := fun a b : SecurityLevel => a ⊔ b
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one := Pub
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl

  -- Distributivity
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

  -- Commutativity of multiplication
  mul_comm := by intro a b; cases a <;> cases b <;> rfl

end SecurityLevel
