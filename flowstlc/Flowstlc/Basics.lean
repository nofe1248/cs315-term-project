import Mathlib.Tactic
import Flowstlc.SecurityLevel

structure FieldMap (α : Type) where
  entries : List (String × α)
deriving Repr

namespace FieldMap

variable {α : Type}

@[simp] def empty : FieldMap α := ⟨[]⟩

@[simp] def ofList (fs : List (String × α)) : FieldMap α := ⟨fs⟩

@[simp] def toList (fm : FieldMap α) : List (String × α) := fm.entries

@[simp] def mapVals {β : Type} (f : α → β) (fm : FieldMap α) : FieldMap β :=
  ⟨fm.entries.map (fun (k, v) => (k, f v))⟩

@[simp] def foldVals {σ : Type} (fm : FieldMap α) (init : σ) (f : σ → α → σ) : σ :=
  fm.entries.foldl (fun acc (_, v) => f acc v) init

end FieldMap

-- Basic types --
inductive Typ : Type
| Unit : Typ
| Bool : Typ
| Nat : Typ
| FunTy : Typ → SecurityLevel → Typ → Typ
| Box : SecurityLevel → Typ → Typ
| Record : FieldMap Typ → Typ
deriving Repr

-- Defining (pre)terms by recursion --
inductive Trm : Type
| bvar : ℕ → Trm
| fvar : ℕ → Trm
| abs  : Typ → Trm → Trm
| app  : Trm → Trm → Trm
-- box_intro : [t]
| box_intro : Trm → Trm
-- box_elim : let [x] = t1 in t2, which will substitute t1 for x in t2
| box_elim : ℕ → Trm → Trm → Trm
-- record and projection
| record : FieldMap Trm → Trm
| proj : Trm → String → Trm
-- cond : if t1 then t2 else t3
| cond : Trm → Trm → Trm → Trm
-- nat literals and operations : 0, succ, pred, iszero
| nat_zero : Trm
| nat_succ : Trm → Trm
| nat_pred : Trm → Trm
| nat_iszero : Trm → Trm
-- unit : ()
| unit_intro : Trm
-- unit_elim : let () = t1 in t2
| unit_elim : Trm → Trm → Trm
-- boolean literals : true, false
| bool_true : Trm
| bool_false : Trm
deriving DecidableEq, Repr

namespace Trm

-- Notations --
notation t1 " ->^" ℓ t2 => Typ.FunTy t1 ℓ t2
notation "□" ℓ T => Typ.Box ℓ T
notation "{" fs "}" => Typ.Record (FieldMap.ofList fs)
notation "€" i => bvar i
notation "$" x => fvar x
notation "λ " T "," t => abs T t
notation t1 " @ " t2 => app t1 t2
notation "[" t "]" => box_intro t
notation "let " "[" x "]" " = " t1 " in " t2 => box_elim x t1 t2
notation "{" fs "}" => record (FieldMap.ofList fs)
notation t "." l => proj t l
notation "if " t1 " then " t2 " else " t3 => cond t1 t2 t3
notation "nat0" => nat_zero
notation "succ " t => nat_succ t
notation "pred " t => nat_pred t
notation "iszero " t => nat_iszero t
notation "unit" => unit_intro
notation "let " "()" " = " t1 " in " t2 => unit_elim t1 t2
notation "tru" => bool_true
notation "fls" => bool_false

-- Defining free variable substitution by induction on terms --
mutual
  def subst (x : ℕ) (a : Trm) : Trm → Trm
  | bvar i => bvar i
  | fvar y => if y = x then a else (fvar y)
  | abs T u => abs T (subst x a u)
  | app u1 u2 => app (subst x a u1) (subst x a u2)
  | box_intro u => box_intro (subst x a u)
  | box_elim y u1 u2 => box_elim y (subst x a u1) (if y = x then u2 else subst x a u2)
  | record fs => record (substFields x a fs)
  | proj u l => proj (subst x a u) l
  | cond u1 u2 u3 => cond (subst x a u1) (subst x a u2) (subst x a u3)
  | nat_zero => nat_zero
  | nat_succ u => nat_succ (subst x a u)
  | nat_pred u => nat_pred (subst x a u)
  | nat_iszero u => nat_iszero (subst x a u)
  | unit_intro => unit_intro
  | unit_elim u1 u2 => unit_elim (subst x a u1) (subst x a u2)
  | bool_true => bool_true
  | bool_false => bool_false

  def substFields (x : ℕ) (a : Trm) : FieldMap Trm → FieldMap Trm
  | ⟨fs⟩ => ⟨substFieldsList x a fs⟩

  def substFieldsList (x : ℕ) (a : Trm) : List (String × Trm) → List (String × Trm)
  | [] => []
  | (l, t) :: rest => (l, subst x a t) :: substFieldsList x a rest
end

notation  "["x" // "u"] "t => subst x u t

mutual
  def fv : Trm → Finset ℕ
  | bvar _ => {}
  | fvar y => {y}
  | abs _ t => fv t
  | app t1 t2 => (fv t1) ∪ (fv t2)
  | box_intro t => fv t
  | box_elim y t1 t2 => (fv t1) ∪ ((fv t2) \ {y})
  | record fs => fvFields fs
  | proj t _ => fv t
  | cond t1 t2 t3 => (fv t1) ∪ (fv t2) ∪ (fv t3)
  | nat_zero => {}
  | nat_succ t => fv t
  | nat_pred t => fv t
  | nat_iszero t => fv t
  | unit_intro => {}
  | unit_elim t1 t2 => (fv t1) ∪ (fv t2)
  | bool_true => {}
  | bool_false => {}

  def fvFields (fs : FieldMap Trm) : Finset ℕ :=
    FieldMap.foldVals fs {} (fun acc t => acc ∪ fv t)
end

--We can always pick a fresh variable for a given term out of a fixed set.
lemma pick_fresh (t : Trm) (L : Finset ℕ) : ∃ (x : ℕ), x ∉ (L ∪ fv t) := by
  exact Infinite.exists_notMem_finset (L ∪ fv t)

mutual
  -- If a variable does not appear free in a term, then substituting for it has no effect
  lemma subst_fresh (t u : Trm) (y : ℕ) (h : y ∉ (fv t)) : ([y // u] t) = t := by
    cases t
    case bvar i =>
      rfl
    case fvar x =>
      simp only [subst]
      rw [if_neg]
      simp [fv] at h
      exact (fun p => h (p.symm))
    case abs T t =>
      simp only [subst, abs.injEq]
      constructor
      · simp only
      · exact (subst_fresh t u y h)
    case app t1 t2 =>
      simp only [subst, app.injEq]
      simp [fv] at h
      exact ⟨(subst_fresh t1 u y h.1), (subst_fresh t2 u y h.2)⟩
    case box_intro t =>
      simp only [subst, box_intro.injEq]
      exact (subst_fresh t u y h)
    case box_elim z t1 t2 =>
      simp only [subst, box_elim.injEq]
      simp [fv] at h
      rcases h with ⟨h1, h2⟩
      refine And.intro ?_ ?_
      · exact trivial
      · refine And.intro ?_ ?_
        · exact (subst_fresh t1 u y h1)
        · by_cases hz : z = y
          · subst hz
            simp
          · have hyfv : y ∉ fv t2 := by
              intro hyIn
              have hyEq : y = z := h2 hyIn
              exact False.elim (hz hyEq.symm)
            have := subst_fresh t2 u y hyfv
            simpa [if_neg hz] using this
    case record fs =>
      simp only [subst, record.injEq]
      have hy : y ∉ fvFields fs := by
        simpa [fv] using h
      exact substFields_fresh fs u y hy
    case proj s t =>
      simp [subst, proj.injEq]
      exact (subst_fresh s u y h)
    case cond t1 t2 t3 =>
      simp only [subst, cond.injEq]
      simp [fv] at h
      exact ⟨(subst_fresh t1 u y h.1), (subst_fresh t2 u y h.2.1), (subst_fresh t3 u y h.2.2)⟩
    case nat_zero =>
      rfl
    case nat_succ t =>
      simp only [subst, nat_succ.injEq]
      exact (subst_fresh t u y h)
    case nat_pred t =>
      simp only [subst, nat_pred.injEq]
      exact (subst_fresh t u y h)
    case nat_iszero t =>
      simp only [subst, nat_iszero.injEq]
      exact (subst_fresh t u y h)
    case unit_intro =>
      rfl
    case unit_elim t1 t2 =>
      simp only [subst, unit_elim.injEq]
      simp [fv] at h
      exact ⟨(subst_fresh t1 u y h.1), (subst_fresh t2 u y h.2)⟩
    case bool_true =>
      rfl
    case bool_false =>
      rfl

  lemma substFields_fresh (fs : List (String × Trm)) (u : Trm) (y : ℕ)
      (h : y ∉ fvFields fs) : substFields y u fs = fs := by
    revert y
    revert u
    induction fs with
    | nil =>
        intro u y h
        simp [substFields]
    | cons head tail ih =>
        intro u y h
        cases head with
        | mk l t =>
            have hy : y ∉ fv t ∧ y ∉ fvFields tail := by
              simpa [fvFields, Finset.mem_union] using h
            rcases hy with ⟨hy_t, hy_tail⟩
            have head_eq := subst_fresh t u y hy_t
            have tail_eq := ih u y hy_tail
            simp [substFields, head_eq, tail_eq]
end

end Trm
