import Mathlib.Tactic
import Flowstlc.SecurityLevel

-- Basic types --
inductive Typ : Type
| typ_base : Typ
| typ_arrow : Typ → Typ → Typ
| typ_graded : SecurityLevel → Typ
deriving DecidableEq, Repr

-- Defining (pre)terms by recursion --
inductive Trm : Type
| bvar : ℕ → Trm
| fvar : ℕ → Trm
| abs : Typ → Trm → Trm
| app : Trm → Trm → Trm
| promote : Trm → Trm
| letg : ℕ → Trm → Trm → Trm
deriving DecidableEq, Repr

namespace Trm

-- Notations --
notation t1 " -> " t2 => Typ.typ_arrow t1 t2
notation "€" i => bvar i
notation "$" x => fvar x
notation "λ " T "," t => abs T t
notation t1 " @ " t2 => app t1 t2
notation "[" t "]" => promote t
notation "let " "[" x "]" " = " t1 " in " t2 => letg x t1 t2

-- Defining free variable substitution by induction on terms --
@[simp]
def subst (x : ℕ) (a : Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if y = x then a else (fvar y)
| abs T u => abs T (subst x a u)
| app u1 u2 => app (subst x a u1) (subst x a u2)
| promote u => promote (subst x a u)
| letg y t1 t2 =>
  let t1' := subst x a t1
  if y = x then
    letg y t1' t2
  else
    letg y t1' (subst x a t2)

notation  "["x" // "u"] "t => subst x u t

-- Set of free variables --
def fv : Trm → Finset ℕ
| bvar _ => {}
| fvar y => {y}
| abs _ t => fv t
| app t1 t2 => (fv t1) ∪ (fv t2)
| promote t => fv t
| letg y t1 t2 => (fv t1) ∪ (fv t2).erase y

--We can always pick a fresh variable for a given term out of a fixed set.
lemma pick_fresh (t : Trm) (L : Finset ℕ) : ∃ (x : ℕ), x ∉ (L ∪ fv t) := by
  exact Infinite.exists_notMem_finset (L ∪ fv t)

-- If a variable does not appear free in a term, then substituting for it has no effect --
lemma subst_fresh (t u : Trm) (y : ℕ) (h : y ∉ (fv t)) : ([y // u] t) = t := by
  induction t
  case bvar i =>
    rfl
  case fvar x =>
    simp only [subst]
    rw [if_neg]
    simp [fv] at h
    exact (fun p => h (p.symm))
  case abs T t ht =>
    simp only [subst, abs.injEq]
    constructor
    · simp only
    exact (ht h)
  case app t1 t2 h1 h2 =>
    simp only [subst, app.injEq]
    simp [fv] at h
    exact ⟨(h1 h.1), (h2 h.2)⟩
  case promote t ht =>
    simp [subst, fv] at *
    exact ht h
  case letg x t1 t2 h1 h2 =>
    -- h : y ∉ fv (letg x t1 t2) = y ∉ (fv t1 ∪ (fv t2).erase x)
    have hy_notin_t1 : y ∉ fv t1 := by
      simpa [fv] using (by
        have := h
        -- y ∉ A ∪ B ⇒ y ∉ A
        exact Finset.notMem_union.mp this |>.left)
    have hy_notin_erase : y ∉ (fv t2).erase x := by
      -- from y ∉ (fv t1 ∪ (fv t2).erase x) we get y ∉ (fv t2).erase x
      simpa [fv] using (Finset.notMem_union.mp h).right
    by_cases hx : x = y
    · -- bound variable matches the substituted variable: do not substitute in t2
      simp [subst, hx]
      exact h1 hy_notin_t1
    · -- x ≠ y, so from y ∉ erase we get y ∉ fv t2
      have hy_notin_t2 : y ∉ fv t2 := by
        -- y ∉ (fv t2).erase x and x ≠ y ⇒ y ∉ fv t2
        -- using: a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s
        have : ¬ (y ≠ x ∧ y ∈ fv t2) := by
          simpa [Finset.mem_erase] using hy_notin_erase
        exact by
          by_contra hyIn
          exact this ⟨Ne.symm hx, hyIn⟩
      simp [subst, hx]
      exact ⟨h1 hy_notin_t1, h2 hy_notin_t2⟩

end Trm
