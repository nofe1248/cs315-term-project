import Mathlib.Tactic

inductive SecurityLevel where
  | Irrelevant : SecurityLevel
  | Public : SecurityLevel
  | Secret : SecurityLevel
  deriving DecidableEq, Repr

-- The security level semiring S is a three-point lattice of security levels
-- {Irrelevant ⊑ Secret ⊑ Public} with
-- • 0 = Irrelevant
-- • 1 = Secret
-- • Addition as the join: r + s = r ∪ s
-- • Multiplication as the join plus a special case: If r or s
-- is Irrelevant, then r · s = Irrelevant, otherwise
-- r · s = r ⊔ s

namespace SecurityLevel

/- The intended order as a custom relation. -/
def leRel : SecurityLevel → SecurityLevel → Prop
  | Irrelevant, _ => True
  | Secret, Secret => True
  | Secret, Public => True
  | Public, Public => True
  | _, _ => False

infix:50 " ⊑ " => leRel

instance : DecidableRel (fun a b : SecurityLevel => a ⊑ b) := by
  intro a b
  cases a <;> cases b <;>
    first
    | exact isTrue trivial
    | exact isTrue trivial
    | exact isTrue trivial
    | exact isTrue trivial
    | exact isFalse (fun h => h.elim)

@[simp] theorem irrelevant_le (a : SecurityLevel) : Irrelevant ⊑ a := by
  cases a <;> decide

@[simp] theorem secret_le_public : Secret ⊑ Public := by decide

@[simp] theorem secret_le_secret : Secret ⊑ Secret := by decide

@[simp] theorem public_le_public : Public ⊑ Public := by decide

@[simp] theorem not_secret_le_irrelevant : ¬ (Secret ⊑ Irrelevant) := by decide

@[simp] theorem not_public_le_secret : ¬ (Public ⊑ Secret) := by decide

@[simp] theorem not_public_le_irrelevant : ¬ (Public ⊑ Irrelevant) := by decide

/- Join (least upper bound) as a primitive operation. -/
def join : SecurityLevel → SecurityLevel → SecurityLevel
  | Irrelevant, x => x
  | x, Irrelevant => x
  | Public, _ => Public
  | _, Public => Public
  | Secret, Secret => Secret

@[simp] theorem join_irrelevant_left (a : SecurityLevel) : join Irrelevant a = a := by
  cases a <;> rfl
@[simp] theorem join_irrelevant_right (a : SecurityLevel) :
    join a Irrelevant = a := by
  cases a <;> rfl
@[simp] theorem join_public_left (a : SecurityLevel) : join Public a = Public := by cases a <;> rfl
@[simp] theorem join_public_right (a : SecurityLevel) : join a Public = Public := by cases a <;> rfl
@[simp] theorem join_secret_secret : join Secret Secret = Secret := rfl

/- Basic algebraic laws for join. -/
@[simp] theorem join_comm (a b : SecurityLevel) : join a b = join b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem join_assoc (a b c : SecurityLevel) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/- Zero/One and arithmetic operations as specified. -/
instance : Zero SecurityLevel where zero := Irrelevant
instance : One SecurityLevel  where one  := Secret

@[simp] theorem zero_def : (0 : SecurityLevel) = Irrelevant := rfl
@[simp] theorem one_def : (1 : SecurityLevel) = Secret := rfl

/- Addition is join. -/
instance : Add SecurityLevel where
  add a b := join a b

@[simp] theorem add_def (a b : SecurityLevel) : a + b = join a b := rfl

/- Multiplication is join unless one of the arguments is Irrelevant, which
   annihilates the product. -/
instance : Mul SecurityLevel where
  mul a b :=
    match a, b with
    | Irrelevant, _ => Irrelevant
    | _, Irrelevant => Irrelevant
    | Public, _     => Public
    | _, Public     => Public
    | Secret, Secret => Secret

@[simp] theorem mul_def : ∀ a b : SecurityLevel, a * b =
    (match a, b with
     | Irrelevant, _ => Irrelevant
     | _, Irrelevant => Irrelevant
     | Public, _     => Public
     | _, Public     => Public
     | Secret, Secret => Secret) := by
  intro a b; cases a <;> cases b <;> rfl

/- Helpful computation lemmas (simp). -/
@[simp] theorem add_irrelevant_left (a : SecurityLevel) : Irrelevant + a = a := by
  simp [add_def]

@[simp] theorem add_irrelevant_right (a : SecurityLevel) : a + Irrelevant = a := by
  simp [add_def]

@[simp] theorem add_secret_public : Secret + Public = Public := by simp [add_def]
@[simp] theorem add_public_secret : Public + Secret = Public := by simp [add_def]
@[simp] theorem add_secret_secret : Secret + Secret = Secret := by simp [add_def]
@[simp] theorem add_public_public : Public + Public = Public := by simp [add_def]

@[simp] theorem mul_irrelevant_left (a : SecurityLevel) : Irrelevant * a = Irrelevant := by
  cases a <;> simp []

@[simp] theorem mul_irrelevant_right (a : SecurityLevel) : a * Irrelevant = Irrelevant := by
  cases a <;> simp []

@[simp] theorem mul_secret_secret : Secret * Secret = Secret := by simp []
@[simp] theorem mul_secret_public : Secret * Public = Public := by simp []
@[simp] theorem mul_public_secret : Public * Secret = Public := by simp []
@[simp] theorem mul_public_public : Public * Public = Public := by simp []

/- A lightweight additive commutative monoid instance (join is idempotent, but we
   only need standard commutative monoid laws to be convenient). -/
instance : AddCommMonoid SecurityLevel where
  add := (· + ·)
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  zero := 0
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  nsmul := nsmulRec

/- Monoid with Irrelevant as zero-annihilator and Secret as one. -/
instance : Monoid SecurityLevel where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  npow := npowRec

/- Distributivity and annihilation to obtain a (nontrivial) semiring-like
   structure. We provide the standard Semiring instance (addition is idempotent).
-/
instance : CommSemiring SecurityLevel where
  __ := (inferInstance : AddCommMonoid SecurityLevel)
  __ := (inferInstance : Monoid SecurityLevel)
  zero := 0
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  left_distrib a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  natCast n := if n = 0 then 0 else 1
  natCast_zero := by simp
  natCast_succ n := by
    by_cases h : n = 0
    · subst h; simp
    · have : (Nat.succ n) ≠ 0 := by simp
      simp [h]

end SecurityLevel

open SecurityLevel

/- Export a few convenient notations at the top-level. -/
notation:50 "ℓ⊥" => SecurityLevel.Irrelevant
notation:50 "ℓS" => SecurityLevel.Secret
notation:50 "ℓ⊤" => SecurityLevel.Public
