import Flowstlc.Basics
import Flowstlc.SecurityLevel

namespace Trm

/- Variable opening turns some bound variables into free variables.
It is used to investigate the body of an abstraction.
Variable closing turns some free variables into bound variables.
It is used to build an abstraction given a representation of its body· -/

@[simp]
def opening (k : ℕ) (u : Trm) : Trm → Trm
| bvar i => if k = i then u else (bvar i)
| fvar x => fvar x
| abs T t => abs T (opening (k + 1) u t)
| app t1 t2 => app (opening k u t1) (opening k u t2)
| box_intro t => box_intro (opening k u t)
| box_elim y t1 t2 =>
  let t1' := opening k u t1
  match u with
  | Trm.fvar x =>
      if y = x then
        -- When opening with a free variable that matches the let-binder,
        -- occurrences of that variable in t2 are bound; don't open t2.
        box_elim y t1' t2
      else
        box_elim y t1' (opening k u t2)
  | _ =>
      box_elim y t1' (opening k u t2)
| cond t1 t2 t3 => cond (opening k u t1) (opening k u t2) (opening k u t3)
| nat_zero => nat_zero
| nat_succ t => nat_succ (opening k u t)
| nat_pred t => nat_pred (opening k u t)
| nat_iszero t => nat_iszero (opening k u t)
| unit_intro => unit_intro
| unit_elim t1 t2 => unit_elim (opening k u t1) (opening k u t2)
| bool_true => bool_true
| bool_false => bool_false

notation " {" k " ~> " u "} " t => opening k u t

--Opening at index zero
def open₀ t u := opening 0 u t

lemma open_var_fv (t u : Trm) :
  (k : ℕ) → fv (opening k u t) ⊆ (fv t) ∪ (fv u) := by
  classical
  intro k
  revert k
  induction t with
  | bvar i =>
    intro k
    by_cases hk : k = i
    · simp [opening, fv, hk]
    · simp [opening, fv, hk]
  | fvar x =>
    intro _
    simp [opening, fv]
  | abs T t ih =>
    intro k
    simpa [opening, fv] using ih (k + 1)
  | app t1 t2 ih1 ih2 =>
    intro k
    intro a ha
    have hmem : a ∈ fv (opening k u t1) ∨ a ∈ fv (opening k u t2) := by
      simpa [opening, fv] using ha
    have : a ∈ (fv t1 ∪ fv t2) ∪ fv u := by
      cases hmem with
      | inl h1 =>
        have h1' := ih1 k h1
        rcases Finset.mem_union.mp h1' with h1t | h1u
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))
        · exact Finset.mem_union.mpr (Or.inr h1u)
      | inr h2 =>
        have h2' := ih2 k h2
        rcases Finset.mem_union.mp h2' with h2t | h2u
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2t)))
        · exact Finset.mem_union.mpr (Or.inr h2u)
    simpa [fv]
  | box_intro t ih =>
    intro k
    simpa [opening, fv] using ih k
  | box_elim y t1 t2 ih1 ih2 =>
    intro k
    match u with
    | Trm.fvar x =>
      by_cases hxy : y = x
      · intro a ha
        have hmem : a ∈ fv (opening k ($ x) t1) ∨ (a ∈ fv t2 ∧ a ≠ y) := by
          simpa [opening, fv, hxy]
          using ha
        have : a ∈ (fv t1 ∪ ((fv t2) \ {y})) ∪ {x} := by
          cases hmem with
          | inl h1 =>
            have h1' := ih1 k h1
            rcases Finset.mem_union.mp h1' with h1t | h1u
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))
            · exact Finset.mem_union.mpr (Or.inr h1u)
          | inr h2 =>
            have : a ∈ (fv t2) \ {y} :=
            Finset.mem_sdiff.mpr
              ⟨h2.left, by simpa [Finset.mem_singleton] using h2.right⟩
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr this)))
        simpa [fv]
      · intro a ha
        have hmem : a ∈ fv (opening k ($ x) t1)
          ∨ (a ∈ fv (opening k ($ x) t2) ∧ a ≠ y) := by
          simpa [opening, fv, hxy] using ha
        have : a ∈ (fv t1 ∪ ((fv t2) \ {y})) ∪ {x} := by
          cases hmem with
          | inl h1 =>
            have h1' := ih1 k h1
            rcases Finset.mem_union.mp h1' with h1t | h1u
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))
            · exact Finset.mem_union.mpr (Or.inr h1u)
          | inr h2 =>
            have h2' := ih2 k h2.left
            rcases Finset.mem_union.mp h2' with h2t | h2u
            · have : a ∈ (fv t2) \ {y} :=
                Finset.mem_sdiff.mpr
                  ⟨h2t, by simpa [Finset.mem_singleton] using h2.right⟩
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr this)))
            · exact Finset.mem_union.mpr (Or.inr h2u)
        simpa [fv]
    | u' =>
      intro a ha
      have hmem : a ∈ fv (opening k u' t1)
        ∨ (a ∈ fv (opening k u' t2) ∧ a ≠ y) := by
          simp at ha
          cases u' with
          | fvar x' =>
              by_cases hxy : y = x'
              · simp [fv, hxy] at ha
                sorry
              · simp [fv, hxy] at ha
                exact ha
          | _ =>
              simp [fv] at ha
              exact ha
      have : a ∈ (fv t1 ∪ ((fv t2) \ {y})) ∪ fv u' := by
        cases hmem with
        | inl h1 =>
          have h1' := ih1 k h1
          rcases Finset.mem_union.mp h1' with h1t | h1u
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))
          · exact Finset.mem_union.mpr (Or.inr h1u)
        | inr h2 =>
          have h2' := ih2 k h2.left
          rcases Finset.mem_union.mp h2' with h2t | h2u
          · have : a ∈ (fv t2) \ {y} :=
            Finset.mem_sdiff.mpr
              ⟨h2t, by simpa [Finset.mem_singleton] using h2.right⟩
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr this)))
          · exact Finset.mem_union.mpr (Or.inr h2u)
      simpa [fv]
  | cond t1 t2 t3 ih1 ih2 ih3 =>
    intro k
    intro a ha
    have hmem : a ∈ fv (opening k u t1)
      ∨ a ∈ fv (opening k u t2) ∨ a ∈ fv (opening k u t3) := by
      simpa [opening, fv]
      using ha
    have : a ∈ ((fv t1 ∪ fv t2) ∪ fv t3) ∪ fv u := by
      cases hmem with
      | inl h1 =>
        have h1' := ih1 k h1
        rcases Finset.mem_union.mp h1' with h1t | h1u
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))))
        · exact Finset.mem_union.mpr (Or.inr h1u)
      | inr h23 =>
        cases h23 with
        | inl h2 =>
          have h2' := ih2 k h2
          rcases Finset.mem_union.mp h2' with h2t | h2u
          · exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2t)))))
          · exact Finset.mem_union.mpr (Or.inr h2u)
        | inr h3 =>
          have h3' := ih3 k h3
          rcases Finset.mem_union.mp h3' with h3t | h3u
          · exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr h3t)))
          · exact Finset.mem_union.mpr (Or.inr h3u)
    simpa [fv, Finset.union_assoc]
  | nat_zero =>
    intro _
    simp [opening, fv]
  | nat_succ t ih =>
    intro k
    simpa [opening, fv] using ih k
  | nat_pred t ih =>
    intro k
    simpa [opening, fv] using ih k
  | nat_iszero t ih =>
    intro k
    simpa [opening, fv] using ih k
  | unit_intro =>
    intro _
    simp [opening, fv]
  | unit_elim t1 t2 ih1 ih2 =>
    intro k
    intro a ha
    have hmem : a ∈ fv (opening k u t1) ∨ a ∈ fv (opening k u t2) := by
      simpa [opening, fv] using ha
    have : a ∈ (fv t1 ∪ fv t2) ∪ fv u := by
      cases hmem with
      | inl h1 =>
        have h1' := ih1 k h1
        rcases Finset.mem_union.mp h1' with h1t | h1u
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1t)))
        · exact Finset.mem_union.mpr (Or.inr h1u)
      | inr h2 =>
        have h2' := ih2 k h2
        rcases Finset.mem_union.mp h2' with h2t | h2u
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2t)))
        · exact Finset.mem_union.mpr (Or.inr h2u)
    simpa [fv]
  | bool_true =>
    intro _
    simp [opening, fv]
  | bool_false =>
    intro _
    simp [opening, fv]

lemma opening_lc_lemma (t u v : Trm) :
    (i j : ℕ) → i ≠ j
    → ({j ~> u} t) = ({i ~> v} ({j ~> u} t))
    → t = ({i ~> v} t) := by
  intro i j
  revert i j
  induction t with
  | bvar k =>
      intro i j hij h
      by_cases hjk : j = k
      · have hik : i ≠ k := by
          simpa [hjk] using hij
        simp [opening, hik]
      · by_cases hik : i = k
        · simp [opening, hjk, hik] at h
          simpa [opening, hik] using h
        · simp [opening, hik]
  | fvar _ =>
      intro _ _ _ _
      simp [opening]
  | abs T t ih =>
      intro i j hij h
      simp [opening] at h
      have hij' : i + 1 ≠ j + 1 := by
        intro h'
        apply hij
        exact Nat.add_right_cancel h'
      have ih_res := ih (i + 1) (j + 1) hij' h
      exact congrArg (fun s => abs T s) ih_res
  | app t₁ t₂ ih₁ ih₂ =>
      intro i j hij h
      simp [opening] at h
      obtain ⟨h₁, h₂⟩ := h
      have ih₁' := ih₁ i j hij h₁
      have ih₂' := ih₂ i j hij h₂
      exact congrArg₂ Trm.app ih₁' ih₂'
  | box_intro t ih =>
      intro i j hij h
      simp [opening] at h
      have ih' := ih i j hij h
      exact congrArg Trm.box_intro ih'
  | box_elim x t1 t2 ih1 ih2 =>
      intro i j hij h
      simp [opening] at h
      cases u with
      | fvar y =>
          by_cases hxy : x = y
          · -- binder matches opened free var: t2 is not opened
            simp [hxy] at h
            cases v with
            | fvar z =>
                simp at h
                by_cases hyz : y = z
                · simp [hyz] at h
                  simp [hxy, hyz]
                  rw [← hyz] at h ih1 ⊢
                  have h1 := ih1 i j hij h
                  exact h1
                · simp [hyz] at h
                  simp [hxy, hyz]
                  have h1 := ih1 i j hij h.left
                  exact ⟨h1, h.right⟩
            | _ =>
                simp at h
                simp [hxy]
                have h1 := ih1 i j hij h.left
                exact ⟨h1, h.right⟩
          · -- binder differs: both t1 and t2 are opened
            simp [hxy] at h
            cases v with
            | fvar z =>
                simp at h
                by_cases hyz : y = z
                · simp [hyz] at h
                  have hxz : x ≠ z := by
                    rw [← hyz]
                    exact hxy
                  simp [hxz] at h ⊢
                  rw [hyz] at ih1 ih2
                  have h1 := ih1 i j hij h.left
                  have h2 := ih2 i j hij h.right
                  exact ⟨h1, h2⟩
                · by_cases hxz : x = z
                  · simp [hxz] at h
                    simp [hxz]
                    rw [← hxz] at ih1 ih2
                    rw [← hxz] at h
                    have h1 := ih1 i j hij h
                    rw [← hxz]
                    exact h1
                  · simp [hxz] at h
                    simp [hxz]
                    have h1 := ih1 i j hij h.left
                    have h2 := ih2 i j hij h.right
                    exact ⟨h1, h2⟩
            | _ =>
                simp at h
                simp
                have h1 := ih1 i j hij h.left
                have h2 := ih2 i j hij h.right
                exact ⟨h1, h2⟩
      | _ =>
          -- u is not a free variable; both t1 and t2 are opened by the inner opening
          simp [opening] at h
          cases v with
          | fvar z =>
              by_cases hxz : x = z
              · simp [hxz] at h
                simp [opening, hxz]
                have h1 := ih1 i j hij h
                exact h1
              · simp [hxz] at h
                simp [opening, hxz]
                have h1 := ih1 i j hij h.left
                have h2 := ih2 i j hij h.right
                exact ⟨h1, h2⟩
          | _ =>
              simp at h
              simp
              have h1 := ih1 i j hij h.left
              have h2 := ih2 i j hij h.right
              exact ⟨h1, h2⟩

----------------------------------------------------------------------
@[simp]
def closing (k x : ℕ) : Trm → Trm
| bvar i => bvar i
| fvar i => if x = i then (bvar k) else (fvar i)
| abs T t => abs T (closing (k + 1) x t)
| app t1 t2 => app (closing k x t1) (closing k x t2)
| box_intro t => box_intro (closing k x t)
| box_elim y t1 t2 =>
  let t1' := closing k x t1
  if y = x then
    -- When the let-binder matches x, occurrences of $x in t2 are bound;
    -- closing should not capture them, so we skip closing in t2.
    box_elim y t1' t2
  else
    box_elim y t1' (closing k x t2)

notation " { " k " <~ " x " } " t => closing k x t

--Closing at index zero
def close₀ u x := closing 0 x u

lemma close_var_fv (t : Trm) (x : ℕ) :
    (k : ℕ) → fv (closing k x t) = (fv t) \ {x} := by
  induction t
  case bvar _ =>
    simp [closing, fv]
  case fvar y =>
    intro k
    by_cases hy : x = y
    · subst hy
      simp [closing, fv]
    · have hx : x ∉ ({y} : Finset ℕ) := by
        simp [Finset.mem_singleton, hy]
      simp [closing, fv, hy, Finset.sdiff_singleton_eq_erase, hx]
  case abs T u hu =>
    intro k
    simp [closing, fv]
    exact (hu (k + 1))
  case app u1 u2 hu1 hu2 =>
    intro k
    simp [closing, fv]
    simp [hu1 k, hu2 k]
    exact Eq.symm (Finset.union_sdiff_distrib (fv u1) (fv u2) {x})
  case box_intro u hu =>
    intro k
    simp [closing, fv]
    exact (hu k)
  case box_elim y u1 u2 hu1 hu2 =>
    intro k
    simp [closing, fv]
    have h1 : fv (closing k x u1) = fv u1 \ {x} := hu1 k
    by_cases hy : y = x
    · -- when the let-binder matches x, closing does not affect t2
      simp [hy]
      rw [fv]
      simp [Finset.union_sdiff_distrib]
      have h1 := hu1 k
      have h2 := hu2 k
      rw [h1]
      simp [Finset.erase_eq]
    · -- when the let-binder does not match x, closing affects t2
      have h2 : fv (closing k x u2) = fv u2 \ {x} := hu2 k
      simp [hy]
      rw [fv]
      simp [Finset.union_sdiff_distrib]
      rw [h1, h2]
      simp [Finset.erase_eq]
      ext a
      simp [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton,
        and_left_comm, and_comm]


----------------------------------------------------------------------
--Locally closed terms
inductive lc : Trm → Prop
| lc_var : ∀ x : ℕ, lc (fvar x)
| lc_abs : ∀ t : Trm, ∀ T : Typ, ∀ L : Finset ℕ,
   (∀ x : ℕ, x ∉ L → lc (open₀ t ($ x))) → lc (abs T t)
| lc_app : ∀ t1 t2 : Trm, lc t1 → lc t2 → lc (app t1 t2)
| lc_box_intro : ∀ t : Trm, lc t → lc (box_intro t)
| lc_box_elim : ∀ y : ℕ, ∀ t1 t2 : Trm, lc t1 → lc t2 → lc (box_elim y t1 t2)

open lc

/-The predicate “body t” asserts that t describes
the body of a locally closed abstraction.-/
def body t := ∃ (L : Finset ℕ), ∀ x, x ∉ L → lc (open₀ t ($ x))

lemma lc_abs_iff_body : ∀ t T, lc (abs T t) ↔ body t := by
  intro t T
  constructor
  · intro h
    cases h
    next L a =>
      use L
  · rintro ⟨L, h⟩
    exact (lc_abs t T L h)
----------------------------------------------------------------------
/-The following lemmas show that opening and closing
are inverses of each other on variables.-/
--1) Close(Open)=Id
lemma close_open (x : ℕ) (t : Trm) :
    x ∉ fv t → (k : ℕ) → closing k x (opening k ($ x) t) = t := by
  intro hx
  induction t
  case bvar i =>
    intro j
    simp [opening]
    by_cases hi : j = i
    · rw [if_pos]
      · simp only [closing, ite_true, hi]
      exact hi
    · rw [if_neg]
      · simp only [closing]
      exact hi
  case fvar y =>
    simp [opening, closing]
    simp [fv] at hx
    exact hx
  case abs u hu =>
    simp [opening, closing] at hu ⊢
    rw [fv] at hx
    exact (fun p => hu hx (p + 1))
  case app u1 u2 hu1 hu2 =>
    simp [opening, closing]
    simp [fv] at hx
    exact (fun p => ⟨hu1 hx.1 p, hu2 hx.2 p⟩)
  case box_intro u hu =>
    simp [opening, closing]
    exact (fun p => hu hx p)
  case box_elim y u1 u2 hu1 hu2 =>
    simp [opening]
    simp [fv] at hx
    by_cases hxy : x = y
    · -- binder matches opened free var: t2 is not opened
      simp only [hxy]
      intro j
      have h1 := hu1 hx.left j
      simp
      rw [← hxy]
      exact h1
    · -- binder differs: both t1 and t2 are opened
      intro j
      have h1 := hu1 hx.left j
      have h2 := hu2 (hx.right hxy) j
      have hyx : y ≠ x := fun p => hxy p.symm
      simp [closing, hyx, h1, h2]


--special case of close_open at j=0
lemma close_open_var (x : ℕ) (t : Trm) :
    x ∉ fv t → close₀ (open₀ t ($ x)) x = t := fun hx => close_open x t hx 0

--Using this fact, we can show open₀ is injective on terms.
lemma open₀_injective (x : ℕ) (t1 t2 : Trm) :
    x ∉ fv t1 → x ∉ fv t2 → open₀ t1 ($ x) = open₀ t2 ($ x) → t1 = t2 := by
  intro hx1 hx2 eq
  rw [← close_open_var x t1 hx1]
  rw [← close_open_var x t2 hx2]
  rw [eq]

----------------------------------------------------------------------
--2) Open(Close)=Id
--First, we need a lemma.
lemma open_close_lemma (x y z : ℕ) (t : Trm) : x ≠ y → y ∉ fv t
    → ((i j : ℕ) → i ≠ j → ({ i ~> ($ y)} ({j ~> ($ z)} ({j <~ x} t)))
      = ({j ~> ($ z)} ({j <~ x} ({i ~> ($ y)} t))) ):= by
  intro neqxy hy
  induction t
  case bvar k =>
    intro i j neqij
    simp only [opening]
    by_cases hik : i = k
    · simp only [closing, opening]
      rw [if_pos hik]
      rw [if_neg]
      · simp only [opening, closing]
        rw [if_pos hik, if_neg neqxy, opening]
      exact (fun p => neqij (by rw [← p] at hik; exact hik))
    · rw [if_neg hik]
      simp [opening]
      by_cases hjk : j = k
      · rw [if_pos hjk]
        simp only [opening]
      · rw [if_neg hjk]
        simp only [opening, ite_eq_right_iff]
        intro ik
        simp
        exact (hik ik)
  case fvar a =>
    intro i j _
    simp only [closing]
    by_cases hxa : x = a
    · simp only [opening, closing]
      rw [if_pos hxa]
      simp only [opening, ite_true]
    · simp only [opening, closing]
      rw [if_neg hxa]
      simp only [opening]
  case abs T u hu =>
    simp only [ne_eq, opening]
    rw [fv] at hy
    intro i j neqij
    simp only [closing, opening, abs.injEq]
    constructor
    · simp only
    apply (hu hy (i + 1) (j + 1))
    exact Iff.mpr Nat.succ_ne_succ neqij
  case app u1 u2 hu1 hu2 =>
    intro i j neqij
    simp only [closing, opening, app.injEq]
    simp [fv] at hy
    exact ⟨hu1 hy.1 i j neqij, hu2 hy.2 i j neqij⟩
  case box_intro u hu =>
    intro i j neqij
    simp only [closing, opening, box_intro.injEq]
    exact hu hy i j neqij
  case box_elim a u1 u2 hu1 hu2 =>
    intro i j neqij
    simp [opening]
    simp [fv] at hy
    by_cases hax : x = a
    · have hay : y ≠ a := by
        rw [← hax]
        simpa [eq_comm] using neqxy
      simp [hax]
      by_cases haz : z = a
      · simp [haz, hay, eq_comm]
        have hu1' := hu1 hy.left i j neqij
        simp [haz, hax] at hu1'
        exact hu1'
      · simp [haz, hay, eq_comm]
        have hu1' := hu1 hy.left i j neqij
        have hu2' := hu2 (hy.right hay) i j neqij
        simp [hax] at hu1' hu2'
        sorry
    · sorry

lemma open_close (x : ℕ) (t : Trm) :
    lc t → (k : ℕ) → opening k ($ x) (closing k x t) = t := by
  intro lct
  induction lct
  case lc_var y =>
    intro j
    simp [closing]
    by_cases hxy : x = y
    · rw [if_pos, hxy]
      · simp []
      exact hxy
    · rw [if_neg]
      · simp []
      exact hxy
  case lc_abs u T L _ hu =>
    intro j
    simp [closing, opening]
    let ⟨y, hy⟩ := pick_fresh u (L ∪ (fv ($ x)) ∪ (fv (( {j + 1 ~> $ x} { j + 1 <~ x } u))))
    simp at hy
    apply (open₀_injective y ( {j + 1 ~> $ x} { j + 1 <~ x } u)  u (hy.2.2.1) (hy.2.2.2))
    rw [← (hu y (hy.1) (j + 1))]
    simp [open₀]
    apply (open_close_lemma x y x u)
    · have hyx := hy.2.1
      simp [fv] at hyx
      exact (fun p => hyx p.symm)
    · exact hy.2.2.2
    exact (Nat.succ_ne_zero j).symm
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro j
    simp [opening, closing]
    exact ⟨hu1 j, hu2 j⟩
  case lc_box_intro t ht =>
    intro j
    simp [closing, opening]
    exact ht j
  case lc_box_elim u t1 t2 ht1 ht2 =>
    intro j
    simp [closing]
    have ht1' := ht1 j
    have ht2' := ht2 j
    sorry

--special case of open_close at j=0
lemma open_close_var (x : ℕ) (t : Trm) :
    lc t → open₀ (close₀ t x) ($ x) = t := by
  intro lct
  exact (open_close x t lct 0)

--Using this fact, we can show closing is injective on terms.
lemma closing_injective (x i : ℕ) (t1 t2 : Trm) :
    lc t1 → lc t2 → closing i x t1 = closing i x t2 → t1 = t2 := by
  intro lct1 lct2 eq
  rw [← open_close x t1 lct1 i]
  rw [← open_close x t2 lct2 i]
  rw [eq]

-----------------------------------------
--Auxilary lemma about opening
lemma opening_lc (t u : Trm) : lc t → (k : ℕ) → (t = {k ~> u} t) := by
  intro lce
  induction lce
  case lc_var x =>
    intro _
    rfl
  case lc_abs v T L _ hv =>
    intro i
    simp [open₀] at hv
    rw [opening]
    have  ⟨x, hx⟩ : ∃ x : ℕ, x ∉ L := by
      exact Infinite.exists_notMem_finset L
    have h : v = { i + 1 ~> u } v := by
      apply (opening_lc_lemma v ($ x) u (i + 1) 0)
      · exact Nat.succ_ne_zero i
      exact (hv x hx (i + 1))
    rw [← h]
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro i
    simp [opening]
    exact ⟨hu1 i, hu2 i⟩
  case lc_box_intro t ht =>
    intro i
    simp [opening]
    exact ht i
  case lc_box_elim y t1 t2 _ _ ht1 ht2 =>
    intro i
    simp [opening]
    sorry

lemma open₀_lc (t u : Trm) : lc t → (t = open₀ t u) := by
  intro lce
  simp [open₀]
  apply (opening_lc t u lce 0)

--Free variable substitution distributes over index substitution.
lemma subst_open_rec (t1 t2 u : Trm) : (i j : ℕ) → lc u
    → ([i // u] ({j ~> t2} t1)) = ({j ~> [i // u] t2} ([i // u] t1)) := by
  induction t1
  case bvar k =>
   intro i j _
   by_cases hjk : (j = k)
   · simp [opening]
     rw [if_pos, if_pos] <;> exact hjk
   · simp [opening]
     rw [if_neg, if_neg, subst]
     <;> exact hjk
  case fvar y =>
   intro i j lcu
   by_cases hyi : (y = i)
   · simp [opening, subst]
     rw [if_pos]
     · exact (opening_lc u ([ i // u ] t2) lcu j)
     exact hyi
   · simp [opening, subst]
     rw [if_neg]
     · exact (opening_lc ($ y) ([ i // u ] t2) (lc.lc_var y) j)
     exact hyi
  case abs T v hv =>
   intro i j lcu
   simp [opening, subst]
   exact (hv i (j + 1) lcu)
  case app u1 u2 hu1 hu2 =>
   intro i j lcu
   simp [opening, subst]
   exact ⟨hu1 i j lcu, hu2 i j lcu⟩
  case box_intro v hv =>
   intro i j lcu
   simp [opening, subst]
   exact hv i j lcu
  case box_elim y v1 v2 hv1 hv2 =>
   intro i j lcu
   simp [opening, subst]
   sorry

--The lemma above is most often used with k = 0 and e2 as some fresh variable.
--Therefore, it simplifies matters to define the following useful corollary.
lemma subst_open_var (t u : Trm) : lc u → (i j : ℕ) → i ≠ j
    → (open₀ ([i // u] t) ($ j)) = ([i // u] (open₀ t ($ j))) := by
  intro lcu i j neqij
  simp [open₀]
  rw [subst_open_rec t ($ j) u i 0 lcu]
  rw [subst, if_neg]
  exact (fun p => neqij (Eq.symm p))


--When we open a term, we can instead open the term with a fresh variable and
--then substitute for that variable.
lemma subst_intro (t u : Trm) : lc u → (x : ℕ) → x ∉ (fv t)
    → (open₀ t u) = ([x // u] (open₀ t ($ x))) := by
  intro lcu x hx
  simp [open₀]
  rw [subst_open_rec t ($ x) u x 0 lcu]
  rw [subst, if_pos]
  · rw [subst_fresh]
    exact hx
  rfl

lemma subst_lc (t u : Trm) : (x : ℕ) → lc t → lc u → lc ([x // u] t) := by
  intro x lct lcu
  induction lct
  case lc_var y =>
    rw [subst]
    by_cases hxy : y = x
    · rw [if_pos]
      · exact lcu
      exact hxy
    · rw [if_neg]
      · exact (lc_var y)
      exact hxy
  case lc_abs v T L _ hv =>
    apply lc_abs ([x // u] v) T (L ∪ {x})
    intro x₀ hx₀
    have hx₀L : x₀ ∉ L := by
      intro hx₀mem
      exact hx₀ (Finset.mem_union.mpr (Or.inl hx₀mem))
    have hx₀x : x ≠ x₀ := by
      intro hx₀eq
      apply hx₀
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hx₀eq.symm))
    rw [subst_open_var v u lcu x x₀ hx₀x]
    exact hv x₀ hx₀L
  case lc_app t1 t2 lct1 lct2 ht1 ht2 =>
    dsimp [subst]
    apply (lc_app ( [ x // u ] t1) ( [ x // u ] t2) ht1 ht2)
  case lc_box_intro v lcv hv =>
    dsimp [subst]
    exact lc.lc_box_intro ([x // u] v) hv
  case lc_box_elim y t1 t2 lct1 lct2 ht1 ht2 =>
    dsimp [subst]
    by_cases hxy : y = x
    · simp [hxy]
      rw [← hxy] at ⊢ ht1
      exact lc.lc_box_elim y ([y // u] t1) t2 ht1 lct2
    · simp [hxy]
      exact lc.lc_box_elim y ([x // u] t1) ([x // u] t2) ht1 ht2

lemma open_var_body : ∀ x t, body t → lc (open₀ t ($ x)) := by
  intro x t bt
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ : ∃ y : ℕ, y ∉ (L ∪ {x} ∪ (fv t)) := by
      exact Infinite.exists_notMem_finset (L ∪ {x} ∪ (fv t))
  have hyL : y ∉ L := by
    intro hyMem
    apply hy
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hyMem)))
  have hyfv : y ∉ fv t := by
    intro hyMem
    apply hy
    exact Finset.mem_union.mpr (Or.inr hyMem)
  have lcy : lc (open₀ t ($ y)) := a y hyL
  have lcx : lc ($ x) := lc_var x
  rw [subst_intro t ($ x) lcx y hyfv]
  exact subst_lc (open₀ t ($ y)) ($ x) y lcy lcx

lemma open_var_lc : ∀ x t, lc (abs T t) → lc (open₀ t ($ x)) := by
  intro x t lcat
  rw [lc_abs_iff_body t] at lcat
  exact (open_var_body x t lcat)

lemma open_body : ∀ t u, body t → lc u → lc (open₀ t u) := by
  intro t u bt lcu
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ : ∃ y : ℕ, y ∉ (L ∪ (fv t)) := by
      exact Infinite.exists_notMem_finset (L ∪ (fv t))
  simp at hy
  rw [subst_intro t u lcu y hy.2]
  exact (subst_lc (open₀ t ($ y)) u y (a y hy.1) lcu)

--general version of open_var_lc
lemma open_lc : ∀ t u, lc (abs T t) → lc u → lc (open₀ t u) := by
  intro t u lcat lcu
  rw [lc_abs_iff_body t] at lcat
  exact (open_body t u lcat lcu)

lemma open_close_subst t x y :
    lc t → (∀ k, (opening k ($ y) (closing k x t)) = ([x // ($ y)] t)) := by
  intro lct
  induction lct
  case lc_var y =>
    simp only [closing, subst]
    by_cases hxy : x = y
    · simp [if_pos hxy, if_pos hxy.symm]
    · have hyx : y ≠ x := (fun p => (hxy p.symm))
      simp [if_neg hxy, if_neg hyx]
  case lc_abs s T L f h =>
    simp [opening, subst, abs.injEq]
    intro k
    let ⟨w, qw⟩ :=
      pick_fresh s (L ∪ {x} ∪ (fv ( {k + 1 ~> $ y} { k + 1 <~ x } s)) ∪ (fv ([x // $ y] s)))
    simp at qw
    push_neg at qw
    have hwx : x ≠ w := qw.1.symm
    have fact := h w qw.2.1 (k + 1)
    rw [← subst_open_var _ _ (lc_var y) _ _ hwx, open₀] at fact
    rw [← open_close_lemma _ _ _ _ hwx, ← open₀] at fact
    · apply open₀_injective w _
      · exact qw.2.2.1
      · exact qw.2.2.2.1
      exact fact
    · exact qw.2.2.2.2
    exact Nat.ne_of_beq_eq_false rfl
  case lc_app u1 u2 _ _ f1 f2 =>
    intro k
    simp
    exact ⟨f1 k, f2 k⟩
  case lc_box_intro s hs =>
    intro k
    simp [opening, closing, subst]
    exact hs k
  case lc_box_elim u u1 u2 h1 h2 f1 f2 =>
    intro k
    simp [closing, subst]
    by_cases hux : u = x
    · -- binder matches x: t2 is not closed
      simp [hux]
      by_cases hxy : x = y
      · -- y = x
        simp [hxy]
        have f1' := f1 k
        rw [hxy] at f1'
        exact f1'
      · -- y ≠ x
        simp [hxy]
        have f1' := f1 k
        have f2' := f2 k
        sorry
    · -- binder differs: both t1 and t2 are closed
      by_cases hxy : x = y
      · -- y = x
        have huy : u ≠ y := by
          rw [← hxy]
          exact hux
        simp [hxy, huy]
        have f1' := f1 k
        have f2' := f2 k
        rw [hxy] at f1' f2'
        exact ⟨f1', f2'⟩
      · -- y ≠ x
        sorry

end Trm
