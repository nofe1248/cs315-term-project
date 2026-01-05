import FlowSTLC.Core

namespace FlowSTLC

open Grade

/-- Observer-indexed logical relation on semantic values. -/
def ValueRel (adv : Grade) : (A : Ty) -> Val A -> Val A -> Prop
  | .unit, _, _ => True
  | .bool, b₁, b₂ => b₁ = b₂
  | .nat, n₁, n₂ => n₁ = n₂
  | .record A B, (a₁, b₁), (a₂, b₂) =>
      ValueRel adv A a₁ a₂ ∧ ValueRel adv B b₁ b₂
  | .arr r A B, f₁, f₂ =>
      ∀ x₁ x₂, (r ≤ adv -> ValueRel adv A x₁ x₂) ->
        ValueRel adv B (f₁ x₁) (f₂ x₂)
  | .box r A, x₁, x₂ => r ≤ adv -> ValueRel adv A x₁ x₂

/-- Environments agree relationally at every grade observable to `adv`. -/
def EnvRel (adv : Grade) : {Γ : Ctx} -> Usage Γ -> Env Γ -> Env Γ -> Prop
  | [], _, _, _ => True
  | A :: _, ρ, (v₁, e₁), (v₂, e₂) =>
      (Usage.head ρ ≤ adv -> ValueRel adv A v₁ v₂) ∧
      EnvRel adv (Usage.tail ρ) e₁ e₂

namespace Usage

theorem eta (ρ : Usage (A :: Γ)) : cons (head ρ) (tail ρ) = ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

end Usage

namespace EnvRel

theorem cons {adv : Grade} {A : Ty} {Γ : Ctx} {r : Grade} {ρ : Usage Γ}
    {v₁ v₂ : Val A} {e₁ e₂ : Env Γ}
    (hHead : r ≤ adv -> ValueRel adv A v₁ v₂)
    (hTail : EnvRel adv ρ e₁ e₂) :
    EnvRel adv (Usage.cons r ρ) (v₁, e₁) (v₂, e₂) := by
  exact ⟨hHead, hTail⟩

theorem extend {adv : Grade} {A : Ty} {Γ : Ctx} {ρ : Usage (A :: Γ)}
    {v₁ v₂ : Val A} {e₁ e₂ : Env Γ}
    (hHead : Usage.head ρ ≤ adv -> ValueRel adv A v₁ v₂)
    (hTail : EnvRel adv (Usage.tail ρ) e₁ e₂) :
    EnvRel adv ρ (v₁, e₁) (v₂, e₂) := by
  exact ⟨hHead, hTail⟩

theorem lookup {adv : Grade} {Γ : Ctx} {ρ : Usage Γ} {e₁ e₂ : Env Γ}
    (h : EnvRel adv ρ e₁ e₂) (i : Fin Γ.length) (hi : ρ i ≤ adv) :
    ValueRel adv (Γ.get i) (Env.lookup e₁ i) (Env.lookup e₂ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | cons A Γ ih =>
      rcases e₁ with ⟨v₁, e₁⟩
      rcases e₂ with ⟨v₂, e₂⟩
      cases i using Fin.cases with
      | zero => exact h.1 hi
      | succ j => exact ih h.2 j hi

theorem add_left {adv : Grade} {Γ : Ctx} {ρ σ : Usage Γ} {e₁ e₂ : Env Γ}
    (h : EnvRel adv (Usage.add ρ σ) e₁ e₂) : EnvRel adv ρ e₁ e₂ := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
      rcases e₁ with ⟨v₁, e₁⟩
      rcases e₂ with ⟨v₂, e₂⟩
      constructor
      · intro hρ
        apply h.1
        exact Grade.le_trans (Grade.add_le_left _ _) hρ
      · exact ih h.2

theorem add_right {adv : Grade} {Γ : Ctx} {ρ σ : Usage Γ} {e₁ e₂ : Env Γ}
    (h : EnvRel adv (Usage.add ρ σ) e₁ e₂) : EnvRel adv σ e₁ e₂ := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
      rcases e₁ with ⟨v₁, e₁⟩
      rcases e₂ with ⟨v₂, e₂⟩
      constructor
      · intro hσ
        apply h.1
        exact Grade.le_trans (Grade.add_le_right _ _) hσ
      · exact ih h.2

theorem scale {adv r : Grade} {Γ : Ctx} {ρ : Usage Γ} {e₁ e₂ : Env Γ}
    (hr : r ≤ adv) (h : EnvRel adv (Usage.scale r ρ) e₁ e₂) :
    EnvRel adv ρ e₁ e₂ := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
      rcases e₁ with ⟨v₁, e₁⟩
      rcases e₂ with ⟨v₂, e₂⟩
      constructor
      · intro hρ
        apply h.1
        exact Grade.mul_le hr hρ
      · exact ih h.2

theorem approx {adv : Grade} {Γ : Ctx} {ρ' ρ : Usage Γ} {e₁ e₂ : Env Γ}
    (hle : Usage.LE ρ' ρ) (h : EnvRel adv ρ' e₁ e₂) :
    EnvRel adv ρ e₁ e₂ := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
      rcases e₁ with ⟨v₁, e₁⟩
      rcases e₂ with ⟨v₂, e₂⟩
      constructor
      · intro hρ
        apply h.1
        exact Grade.le_trans (hle 0) hρ
      · apply ih (ρ' := Usage.tail ρ') (ρ := Usage.tail ρ)
        · intro i
          exact hle i.succ
        · exact h.2

end EnvRel

theorem evaluation_complete {Γ : Ctx} {ρ : Usage Γ} {A : Ty}
    (t : Term Γ ρ A) (env : Env Γ) : Evaluates t env (t.eval env) := by
  induction t with
  | var i => exact Evaluates.var env i
  | lam body ih => exact Evaluates.lam env body
  | app fn arg ihFn ihArg =>
      exact Evaluates.app fn arg env (fn.eval env) (arg.eval env) (ihFn env) (ihArg env)
  | promote r term ih => exact Evaluates.promote r term env (term.eval env) (ih env)
  | letBox boxed body ihBox ihBody =>
      exact Evaluates.letBox boxed body env (boxed.eval env)
        (body.eval (Env.extend (boxed.eval env) env))
        (ihBox env) (ihBody (Env.extend (boxed.eval env) env))
  | approx term allowed ih =>
      exact Evaluates.approx term allowed env (term.eval env) (ih env)
  | record left right ihLeft ihRight =>
      exact Evaluates.record left right env (left.eval env) (right.eval env)
        (ihLeft env) (ihRight env)
  | first pairTerm ih =>
      exact Evaluates.first pairTerm env (pairTerm.eval env).1 (pairTerm.eval env).2 (ih env)
  | second pairTerm ih =>
      exact Evaluates.second pairTerm env (pairTerm.eval env).1 (pairTerm.eval env).2 (ih env)
  | true => exact Evaluates.true env
  | false => exact Evaluates.false env
  | ite controlGrade publicControl condition thenBranch elseBranch ihC ihT ihE =>
      cases hc : condition.eval env with
      | false =>
          have hcEval := ihC env
          rw [hc] at hcEval
          simpa [Term.eval, hc] using
            Evaluates.iteFalse controlGrade publicControl condition thenBranch elseBranch
              env (elseBranch.eval env) hcEval (ihE env)
      | true =>
          have hcEval := ihC env
          rw [hc] at hcEval
          simpa [Term.eval, hc] using
            Evaluates.iteTrue controlGrade publicControl condition thenBranch elseBranch
              env (thenBranch.eval env) hcEval (ihT env)
  | zero => exact Evaluates.zero env
  | succ term ih => exact Evaluates.succ term env (term.eval env) (ih env)
  | pred term ih => exact Evaluates.pred term env (term.eval env) (ih env)
  | isZero term ih => exact Evaluates.isZero term env (term.eval env) (ih env)
  | unit => exact Evaluates.unit env
  | letUnit unitTerm body ihUnit ihBody =>
      exact Evaluates.letUnit unitTerm body env (body.eval env) (ihUnit env) (ihBody env)

/-- Evaluation preserves the statically indexed result type and agrees with
the executable evaluator. -/
theorem preservation {Γ : Ctx} {ρ : Usage Γ} {A : Ty}
    {t : Term Γ ρ A} {env : Env Γ} {v : Val A} (h : Evaluates t env v) :
    t.eval env = v := by
  induction h with
  | var => rfl
  | lam => rfl
  | app fn arg env f value fnEval argEval ihFn ihArg =>
      simp only [Term.eval]
      rw [ihFn, ihArg]
  | promote r term env value termEval ih => exact ih
  | letBox boxed body env value result boxedEval bodyEval ihBox ihBody =>
      simp only [Term.eval]
      rw [ihBox]
      exact ihBody
  | approx term allowed env value termEval ih => exact ih
  | record left right env leftValue rightValue leftEval rightEval ihLeft ihRight =>
      simp only [Term.eval]
      rw [ihLeft, ihRight]
  | first pairTerm env leftValue rightValue pairEval ih =>
      simp only [Term.eval]
      rw [ih]
  | second pairTerm env leftValue rightValue pairEval ih =>
      simp only [Term.eval]
      rw [ih]
  | true => rfl
  | false => rfl
  | iteTrue controlGrade publicControl condition thenBranch elseBranch env result
      conditionEval branchEval ihCondition ihBranch =>
      simp only [Term.eval]
      rw [ihCondition]
      exact ihBranch
  | iteFalse controlGrade publicControl condition thenBranch elseBranch env result
      conditionEval branchEval ihCondition ihBranch =>
      simp only [Term.eval]
      rw [ihCondition]
      exact ihBranch
  | zero => rfl
  | succ term env value termEval ih => exact congrArg Nat.succ ih
  | pred term env value termEval ih => exact congrArg Nat.pred ih
  | isZero term env value termEval ih => exact congrArg (fun n => Nat.beq n 0) ih
  | unit => rfl
  | letUnit unitTerm body env result unitEval bodyEval ihUnit ihBody => exact ihBody

/-- Every well-typed closed term can take an operational evaluation step to a
canonical value. -/
theorem progress {A : Ty} {ρ : Usage []} (t : Term [] ρ A) :
    ∃ v : Val A, Evaluates t Env.empty v :=
  ⟨t.eval Env.empty, evaluation_complete t Env.empty⟩

/-- Binary fundamental theorem for the security semiring. -/
theorem fundamental {adv : Grade} {Γ : Ctx} {ρ : Usage Γ} {A : Ty}
    (t : Term Γ ρ A) (e₁ e₂ : Env Γ) (h : EnvRel adv ρ e₁ e₂) :
    ValueRel adv A (t.eval e₁) (t.eval e₂) := by
  induction t with
  | var i =>
      apply EnvRel.lookup h i
      simp [Usage.single]
  | lam body ih =>
      intro x₁ x₂ hx
      apply ih _ _
      exact EnvRel.extend hx h
  | app fn arg ihFn ihArg =>
      apply ihFn e₁ e₂ (EnvRel.add_left h) (arg.eval e₁) (arg.eval e₂)
      intro hr
      exact ihArg e₁ e₂ (EnvRel.scale hr (EnvRel.add_right h))
  | promote r term ih =>
      intro hr
      exact ih e₁ e₂ (EnvRel.scale hr h)
  | letBox boxed body ihBox ihBody =>
      apply ihBody _ _
      exact EnvRel.cons (ihBox e₁ e₂ (EnvRel.add_left h)) (EnvRel.add_right h)
  | approx term allowed ih =>
      exact ih e₁ e₂ (EnvRel.approx allowed h)
  | record left right ihLeft ihRight =>
      exact ⟨ihLeft e₁ e₂ (EnvRel.add_left h), ihRight e₁ e₂ (EnvRel.add_right h)⟩
  | first pairTerm ih => exact (ih e₁ e₂ h).1
  | second pairTerm ih => exact (ih e₁ e₂ h).2
  | true => rfl
  | false => rfl
  | ite controlGrade publicControl condition thenBranch elseBranch ihC ihT ihE =>
      have hControl : controlGrade ≤ adv :=
        Grade.le_trans publicControl (Grade.pub_le adv)
      have hc := ihC e₁ e₂ (EnvRel.scale hControl (EnvRel.add_left h))
      have hBranches := EnvRel.add_right h
      have ht := ihT e₁ e₂ (EnvRel.add_left hBranches)
      have he := ihE e₁ e₂ (EnvRel.add_right hBranches)
      simp only [Term.eval]
      rw [hc]
      cases condition.eval e₂ <;> assumption
  | zero => rfl
  | succ term ih => exact congrArg Nat.succ (ih e₁ e₂ h)
  | pred term ih => exact congrArg Nat.pred (ih e₁ e₂ h)
  | isZero term ih => exact congrArg (fun n => Nat.beq n 0) (ih e₁ e₂ h)
  | unit => trivial
  | letUnit unitTerm body ihUnit ihBody =>
      exact ihBody e₁ e₂ (EnvRel.add_right h)

inductive IsBase : Ty -> Prop where
  | unit : IsBase .unit
  | bool : IsBase .bool
  | nat : IsBase .nat

theorem base_eq {adv : Grade} {A : Ty} (hA : IsBase A) {v₁ v₂ : Val A}
    (h : ValueRel adv A v₁ v₂) : v₁ = v₂ := by
  cases hA with
  | unit => cases v₁; cases v₂; rfl
  | bool => exact h
  | nat => exact h

/-- The singleton context used in the report's non-interference theorem. -/
def inputUsage (A : Ty) (r : Grade) : Usage [A] := fun _ => r

def secretInputUsage (A : Ty) : Usage [A] := inputUsage A .sec

theorem highInput_related (adv r : Grade) (hadv : adv ≤ r) (hne : adv ≠ r)
    (A : Ty) (v₁ v₂ : Val A) :
    EnvRel adv (inputUsage A r) (v₁, Env.empty) (v₂, Env.empty) := by
  constructor
  · intro hra
    exact False.elim (hne (Grade.le_antisymm hadv hra))
  · trivial

/-- Termination-insensitive non-interference in the exact shape stated in the
report: changing one secret input cannot change a terminating public base
observation. Evaluation is total here, so the result is slightly stronger. -/
theorem termination_insensitive_noninterference_general
    {adv r : Grade} (hadv : adv ≤ r) (hne : adv ≠ r)
    {Input Output : Ty} (hOutput : IsBase Output)
    (t : Term [Input] (inputUsage Input r) (.box adv Output))
    (v₁ v₂ : Val Input) :
    t.eval (v₁, Env.empty) = t.eval (v₂, Env.empty) := by
  apply base_eq hOutput
  have hrel := fundamental t (v₁, Env.empty) (v₂, Env.empty)
    (highInput_related adv r hadv hne Input v₁ v₂)
  exact hrel (Grade.le_refl adv)

theorem termination_insensitive_noninterference
    {Input Output : Ty} (hOutput : IsBase Output)
    (t : Term [Input] (secretInputUsage Input) (.box .pub Output))
    (v₁ v₂ : Val Input) :
    t.eval (v₁, Env.empty) = t.eval (v₂, Env.empty) := by
  exact termination_insensitive_noninterference_general
    (Grade.pub_le .sec) (by decide) hOutput t v₁ v₂

/-- Strong normalization for the intrinsic, recursion-free semantics: every
well-typed term is evaluated by a structurally total Lean function. -/
theorem strong_normalization {Γ : Ctx} {ρ : Usage Γ} {A : Ty}
    (t : Term Γ ρ A) (env : Env Γ) : ∃ v : Val A, Evaluates t env v :=
  ⟨t.eval env, evaluation_complete t env⟩

end FlowSTLC
