import Flowstlc.Basics
import Flowstlc.SecurityLevel

/-
In order to make typing judgments, we need the notion of context.
The definition is designed to talk about "(x : [T]_ℓ)"-like assumptions.
-/
open List
open SecurityLevel

notation "context" => List (ℕ × Typ × SecurityLevel)

@[simp]
def context_terms : context → (Finset ℕ)
| [] => ∅
| ((x, _, _) :: Γ') => {x} ∪ (context_terms Γ')

@[simp]
def in_context (x : ℕ) : context → Prop
| [] => False
| ((y, _, _) :: m) => (x = y) ∨ (in_context x m)

lemma context_terms_iff_in_list (x : ℕ) (Γ : context) :
    (x ∈ context_terms Γ) ↔ in_context x Γ := by
  induction Γ
  case nil =>
    simp only [context_terms, Finset.notMem_empty, in_context]
  case cons b Γ' f =>
    simp only [context_terms, Finset.mem_union, Finset.mem_singleton, in_context]
    rw [f]

lemma not_context_terms_to_not_in_context x Γ :
    ¬ (x ∈ context_terms Γ) →  ¬ in_context x Γ := by
  rw [context_terms_iff_in_list]
  simp

lemma in_context_append_neg (x : ℕ) (Γ Δ : context) :
    ¬ (in_context x (Γ ++ Δ)) → ¬ (in_context x Γ) ∧ ¬ (in_context x Δ) := by
  intro H
  induction Γ
  case nil =>
    simp only [in_context, not_false_eq_true, true_and] at H ⊢
    rwa [nil_append] at H
  case cons b Γ' f =>
    simp [in_context] at H f ⊢
    exact ⟨⟨H.1, (f (H.2)).1⟩, (f (H.2)).2⟩

lemma in_context_append_neg' (x : ℕ) (Γ Δ : context) :
    ¬ (in_context x Γ) ∧ ¬ (in_context x Δ) → ¬ (in_context x (Γ ++ Δ)) := by
  rintro ⟨H1, H2⟩
  induction Γ
  case nil =>
    simp only [nil_append]
    exact H2
  case cons b Γ' f =>
    simp [in_context] at H1 ⊢
    exact ⟨H1.1, f H1.2⟩

-- We can only bind variable once per context --
inductive valid_ctx : context → Prop where
| valid_nil : valid_ctx []
| valid_cons (Γ : context) (x : ℕ) (T : Typ) (ℓ : SecurityLevel) :
  (valid_ctx Γ) → (¬ (in_context x Γ)) → valid_ctx ((x, T, ℓ) :: Γ)

open valid_ctx

--Properties of valid contexts
lemma valid_push (Γ : context) (x : ℕ) (T : Typ) (ℓ : SecurityLevel) :
    valid_ctx Γ → ¬ (in_context x Γ) → valid_ctx ([(x, T, ℓ)] ++ Γ) := by
  simp only [singleton_append]
  exact (valid_cons Γ x T ℓ)

lemma valid_remove_mid (Γ Δ Ψ : context) :
    valid_ctx (Ψ ++ Δ ++ Γ) -> valid_ctx (Ψ ++ Γ) := by
  induction Ψ
  case nil =>
    induction Δ
    case nil =>
      simp only [append_nil, nil_append, imp_self]
    case cons b Δ' f =>
      simp only [nil_append, cons_append] at f ⊢
      intro H
      cases H
      next x S p p' =>
        exact (f p)
  case cons b Ψ f =>
    simp only [cons_append, append_assoc]
    intro H
    cases H
    next x S p p' =>
      simp only [append_assoc] at f p ⊢
      apply valid_cons
      · exact (f p)
      apply in_context_append_neg'
      constructor
      · exact (in_context_append_neg _ _ _ p').1
      exact (in_context_append_neg _ _ _ (in_context_append_neg _ _ _ p').2).2

lemma valid_remove_mid_cons (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    valid_ctx (Δ ++ (x, T, ℓ) :: Γ)
    → valid_ctx (Δ ++ Γ) := by
  intro H
  simp only [append_cons Δ (x, T, ℓ) Γ] at H
  exact (valid_remove_mid Γ ((x, T, ℓ) :: []) Δ H)

lemma valid_remove_cons (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ : context) :
    valid_ctx ((x, T, ℓ) :: Γ)
    → valid_ctx (Γ) := by
  intro H
  have := valid_remove_mid Γ [(x, T, ℓ)] [] H
  simpa using this

--Extracting (x : T) from a context
@[simp]
def get (x : ℕ) : context → Option (Typ × SecurityLevel)
| [] => none
| (y, S, ℓ) :: Γ' => if x = y then some (S, ℓ) else get x Γ'

@[simp]
def binds x T ℓ (Γ : context) := (get x Γ = some (T, ℓ))

--Properties of binds
lemma binds_singleton (x : ℕ) (T : Typ) (ℓ : SecurityLevel) :
    binds x T ℓ [(x, T, ℓ)] := by
  simp only [binds]
  simp only [_root_.get]
  simp only [ite_true]

lemma binds_singleton_tail (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ : context) :
    binds x T ℓ ([(x, T, ℓ)] ++ Γ) := by
  simp [binds, _root_.get, nil_append]

lemma binds_tail (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ Γ → (¬ (in_context x Δ)) → binds x T ℓ (Δ ++ Γ) := by
  intro bx nx
  simp [binds] at bx ⊢
  induction Δ
  case nil =>
    simp only [nil_append, bx]
  case cons b Δ' f' =>
    simp [in_context] at nx
    push_neg at nx
    simp [_root_.get]
    rw [if_neg nx.1]
    apply (f' nx.2)

lemma binds_head (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ Γ → binds x T ℓ (Γ ++ Δ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [binds, _root_.get]
    by_cases hxb : x = b.1
    · simp only [cons_append, _root_.get]
      rw [if_pos hxb, if_pos hxb]
      exact id
    · simp only [cons_append, _root_.get]
      rw [if_neg hxb]
      intro H
      simp [binds] at f
      rw [if_neg hxb]
      exact (f H)

--Case analysis on binds
lemma binds_concat_inv' (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ (Γ ++ Δ)
    → ((in_context x Γ) ∨ ¬(binds x T ℓ Δ))
    → (binds x T ℓ Γ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    intro bxT h
    rcases h with h1 | h2
    · by_cases hxb : x = b.1
      · simp [if_pos hxb] at bxT ⊢
        exact bxT
      · simp [if_neg hxb] at bxT ⊢
        apply f
        · exact bxT
        simp [in_context, hxb] at h1
        left
        exact h1
    · simp only [binds, _root_.get]
      by_cases hxb : x = b.1
      · simp [if_pos hxb] at bxT ⊢
        exact bxT
      · simp [if_neg hxb] at bxT ⊢
        apply f
        · exact bxT
        right
        exact h2

lemma binds_concat_inv (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ (Γ ++ Δ)
    → ((¬ (in_context x Γ)) ∧ (binds x T ℓ Δ)) ∨ (binds x T ℓ Γ) := by
  intro bxT
  refine Iff.mpr or_iff_not_imp_left ?_
  intro H
  apply binds_concat_inv' _ _ _ _ _ bxT
  push_neg at H
  exact Iff.mpr or_iff_not_imp_left H

lemma binds_singleton_inv (x y : ℕ) (X Y : Typ) (ℓ₁ ℓ₂ : SecurityLevel) :
    binds x X ℓ₁ [(y,Y,ℓ₂)] → (x = y) ∧ (X = Y) ∧ (ℓ₁ = ℓ₂) := by
  simp only [binds, _root_.get]
  intro H
  by_cases hxy : x = y
  · simp [if_pos hxy] at H
    exact ⟨hxy, ⟨H.left.symm, H.right.symm⟩⟩
  · simp [if_neg hxy] at H

lemma binds_mid (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Δ Γ : context) :
    valid_ctx (Γ ++ [(x,T,ℓ)] ++ Δ)
    → binds x T ℓ (Γ ++ [(x,T,ℓ)] ++ Δ) := by
  induction Γ
  case nil =>
    simp only [nil_append, singleton_append, binds, _root_.get, ite_true, implies_true]
  case cons b Γ' f =>
    intro H
    cases H
    next y S ℓ H' g =>
      simp only [binds, append_eq, append_assoc, singleton_append] at f H' g ⊢
      by_cases hxy : x = y
      · simp [if_pos hxy]
        have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push_neg at t2
        by_contra _
        exact (t2.1 hxy.symm)
      · simp [if_neg hxy]
        exact (f H')

lemma binds_mid_eq (x : ℕ) (T S : Typ) (ℓ₁ ℓ₂ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ₁ (Δ ++ [(x,S,ℓ₂)] ++ Γ)
    → valid_ctx (Δ ++ [(x,S,ℓ₂)] ++ Γ) →  T = S := by
  induction Δ
  case nil =>
    simp only [binds, _root_.get, nil_append, ite_true, Option.some.injEq, singleton_append]
    exact fun p _ => (congrArg Prod.fst p).symm
  case cons b Δ' f =>
    intro p H
    cases H
    next y S' ℓ' H' g =>
      simp only [binds, append_eq, append_assoc, singleton_append] at p f H' g ⊢
      by_cases hxy : x = y
      · have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push_neg at t2
        by_contra _
        exact (t2.1 hxy.symm)
      · simp [if_neg hxy] at p
        exact (f p H')

lemma binds_mid_eq_cons (x : ℕ) (T S : Typ) (ℓ₁ ℓ₂ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ₁ (Δ ++ (x,S,ℓ₂) :: Γ)
    → valid_ctx (Δ ++ (x,S,ℓ₂) :: Γ) → T = S := by
  intro p H
  simp only [append_cons Δ (x, S, ℓ₂) Γ] at p H
  exact (binds_mid_eq x T S ℓ₁ ℓ₂ Γ Δ p H)

--Additional properties of binds
lemma binds_in_context (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ : context) :
    binds x T ℓ Γ → in_context x Γ := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [binds, _root_.get, in_context] at f ⊢
    by_cases hxb : x = b.1
    · simp only [if_pos hxb]
      intro _
      exact (Or.inl hxb)
    · simp only [if_neg hxb]
      intro p
      exact (Or.inr (f p))

lemma binds_fresh (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ : context) :
    ¬ in_context x Γ → ¬ binds x T ℓ Γ := by
  contrapose
  simp only [not_not]
  exact (binds_in_context x T ℓ Γ)

lemma binds_concat_ok (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ Γ -> valid_ctx (Δ ++ Γ) -> binds x T ℓ (Δ ++ Γ) := by
  induction Δ
  case nil =>
    simp only [binds, nil_append]
    exact (fun p _ => p)
  case cons b Δ' f =>
    intro p H
    cases H
    next y S ℓ' H' g =>
      simp only [binds, append_eq] at H' ⊢
      by_cases hxy : x = y
      · simp [if_pos hxy]
        by_contra
        apply g
        apply binds_in_context y T ℓ (Δ' ++ Γ)
        rw [← hxy]
        exact (f p H')
      · simp [if_neg hxy]
        exact (f p H')

lemma binds_weaken (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ Ψ : context) :
    binds x T ℓ (Ψ ++ Γ)
    → valid_ctx (Ψ ++ Δ ++ Γ)
    → binds x T ℓ (Ψ ++ Δ ++ Γ) := by
  induction Ψ
  case nil =>
    simp only [binds, nil_append]
    exact (fun p H => (binds_concat_ok _ _ _ _ _ p H))
  case cons b Ψ' f =>
    intro p H
    cases H
    next y S ℓ' H' g =>
      simp only [binds, append_eq, append_assoc] at f H' p g ⊢
      by_cases hxy : x = y
      · simp [if_pos hxy] at p ⊢
        exact p
      · simp [if_neg hxy] at p ⊢
        exact (f p H')

lemma binds_weaken_at_head (x : ℕ) (T : Typ) (ℓ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ Δ → valid_ctx (Γ ++ Δ)
    → binds x T ℓ (Γ ++ Δ) := (binds_weaken x T ℓ Δ Γ [])

lemma binds_remove_mid (x y : ℕ) (T S : Typ) (ℓ₁ ℓ₂ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ₁ (Γ ++ ([(y,S,ℓ₂)] ++ Δ))
    → x ≠ y → binds x T ℓ₁ (Γ ++ Δ) := by
  intro p H
  have t := (binds_concat_inv x T ℓ₁ Γ ([(y,S,ℓ₂)] ++ Δ) p)
  rcases t with ⟨t11, t12⟩ | t2
  · apply (binds_tail x T ℓ₁ Δ Γ)
    · simp [if_neg H] at t12
      exact t12
    exact t11
  · apply (binds_head _ _ _ _ _ t2)

lemma binds_remove_mid_cons (x y : ℕ) (T S : Typ) (ℓ₁ ℓ₂ : SecurityLevel) (Γ Δ : context) :
    binds x T ℓ₁ (Δ ++ (y, S, ℓ₂) :: Γ)
    → x ≠ y → binds x T ℓ₁ (Δ ++ Γ) := by
  intro H p
  apply (binds_remove_mid x y T S ℓ₁ ℓ₂ Δ Γ)
  · rwa [append_cons, append_assoc] at H
  exact p
