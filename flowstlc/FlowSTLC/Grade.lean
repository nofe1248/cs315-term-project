namespace FlowSTLC

/-- The two-point confidentiality lattice, ordered `public <= secret`. -/
inductive Grade where
  | pub
  | sec
  deriving DecidableEq, Repr

namespace Grade

def le : Grade -> Grade -> Prop
  | .pub, _ => True
  | .sec, .sec => True
  | .sec, .pub => False

instance : LE Grade := ⟨le⟩
instance (a b : Grade) : Decidable (a ≤ b) :=
  match a, b with
  | .pub, .pub => isTrue trivial
  | .pub, .sec => isTrue trivial
  | .sec, .pub => isFalse id
  | .sec, .sec => isTrue trivial

/-- Semiring addition is lattice meet. -/
def add : Grade -> Grade -> Grade
  | .pub, _ => .pub
  | _, .pub => .pub
  | .sec, .sec => .sec

/-- Semiring multiplication is lattice join. -/
def mul : Grade -> Grade -> Grade
  | .sec, _ => .sec
  | _, .sec => .sec
  | .pub, .pub => .pub

instance : Add Grade := ⟨add⟩
instance : Mul Grade := ⟨mul⟩

@[simp] theorem pub_le (r : Grade) : pub ≤ r := by cases r <;> trivial
@[simp] theorem le_sec (r : Grade) : r ≤ sec := by cases r <;> trivial
@[simp] theorem sec_not_le_pub : ¬ sec ≤ pub := by simp [LE.le, le]

theorem le_refl (r : Grade) : r ≤ r := by cases r <;> trivial

theorem le_trans {a b c : Grade} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [LE.le, le]

theorem le_antisymm {a b : Grade} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> simp_all [LE.le, le]

@[simp] theorem add_pub_left (r : Grade) : pub + r = pub := by cases r <;> rfl
@[simp] theorem add_pub_right (r : Grade) : r + pub = pub := by cases r <;> rfl
@[simp] theorem add_sec_left (r : Grade) : sec + r = r := by cases r <;> rfl
@[simp] theorem add_sec_right (r : Grade) : r + sec = r := by cases r <;> rfl
@[simp] theorem add_self (r : Grade) : r + r = r := by cases r <;> rfl

@[simp] theorem mul_pub_left (r : Grade) : pub * r = r := by cases r <;> rfl
@[simp] theorem mul_pub_right (r : Grade) : r * pub = r := by cases r <;> rfl
@[simp] theorem mul_sec_left (r : Grade) : sec * r = sec := by cases r <;> rfl
@[simp] theorem mul_sec_right (r : Grade) : r * sec = sec := by cases r <;> rfl
@[simp] theorem mul_self (r : Grade) : r * r = r := by cases r <;> rfl

theorem add_assoc (a b c : Grade) : (a + b) + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_comm (a b : Grade) : a + b = b + a := by
  cases a <;> cases b <;> rfl

theorem mul_assoc (a b c : Grade) : (a * b) * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mul_comm (a b : Grade) : a * b = b * a := by
  cases a <;> cases b <;> rfl

theorem mul_add_left (a b c : Grade) : a * (b + c) = a * b + a * c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mul_add_right (a b c : Grade) : (a + b) * c = a * c + b * c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_le_left (a b : Grade) : a + b ≤ a := by
  cases a <;> cases b <;> trivial

theorem add_le_right (a b : Grade) : a + b ≤ b := by
  cases a <;> cases b <;> trivial

theorem mul_le {a b observer : Grade} (ha : a ≤ observer) (hb : b ≤ observer) :
    a * b ≤ observer := by
  cases a <;> cases b <;> cases observer <;> simp_all [LE.le, le]

theorem add_monotone {a b c d : Grade} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [LE.le, le]

theorem mul_monotone {a b c d : Grade} (hab : a ≤ b) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [LE.le, le]

theorem isSecuritySemiring :
    (∀ a b c : Grade, (a + b) + c = a + (b + c)) ∧
    (∀ a b : Grade, a + b = b + a) ∧
    (∀ a : Grade, a + sec = a) ∧
    (∀ a b c : Grade, (a * b) * c = a * (b * c)) ∧
    (∀ a : Grade, a * pub = a) ∧
    (∀ a : Grade, a * sec = sec) ∧
    (∀ a b c : Grade, a * (b + c) = a * b + a * c) := by
  exact ⟨add_assoc, add_comm, add_sec_right, mul_assoc, mul_pub_right,
    mul_sec_right, mul_add_left⟩

end Grade
end FlowSTLC
