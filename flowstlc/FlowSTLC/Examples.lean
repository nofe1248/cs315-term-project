import FlowSTLC.Metatheory

namespace FlowSTLC.Examples

open FlowSTLC

/-- The identity function necessarily has a public-use arrow. -/
def publicIdentity (A : Ty) :=
  Term.lam (Term.var (Γ := [A]) 0)

theorem publicIdentity_eval (A : Ty) (v : Val A) :
    (publicIdentity A).eval Env.empty v = v := rfl

/-- A public boxed result that does not inspect its secret input. -/
def publicZero (Input : Ty) :
    Term [Input] (secretInputUsage Input) (.box .pub .nat) :=
  Term.approx (Term.promote .pub (Term.zero (Γ := [Input]))) (by
    intro i
    exact Grade.le_refl .sec)

theorem publicZero_is_noninterfering (Input : Ty) (v₁ v₂ : Val Input) :
    (publicZero Input).eval (v₁, Env.empty) =
      (publicZero Input).eval (v₂, Env.empty) := by
  exact termination_insensitive_noninterference IsBase.nat (publicZero Input) v₁ v₂

/-- The orientation of `T-Approx` cannot disguise a public use as secret. -/
theorem approximation_cannot_hide_public_use (A : Ty) :
    ¬ Usage.LE (secretInputUsage A) (Usage.single (0 : Fin [A].length)) := by
  intro h
  apply Grade.sec_not_le_pub
  simpa [secretInputUsage, inputUsage, Usage.unused] using h (0 : Fin [A].length)

/-- A public conditional is accepted and computes the ordinary Boolean `not`. -/
def boolNot :=
  Term.lam
    (Term.ite .pub (Grade.le_refl .pub)
      (Term.var (Γ := [.bool]) 0)
      (Term.false (Γ := [.bool]))
      (Term.true (Γ := [.bool])))

theorem boolNot_true : (boolNot.eval Env.empty) true = false := rfl
theorem boolNot_false : (boolNot.eval Env.empty) false = true := rfl

end FlowSTLC.Examples
