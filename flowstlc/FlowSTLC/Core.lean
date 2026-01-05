import FlowSTLC.Grade

namespace FlowSTLC

/-- Core types. Finite records are represented by nested products. -/
inductive Ty where
  | unit
  | bool
  | nat
  | record (left right : Ty)
  | arr (grade : Grade) (domain codomain : Ty)
  | box (grade : Grade) (contents : Ty)
  deriving DecidableEq, Repr

abbrev Ctx := List Ty

/-- One grade per variable in a de Bruijn typing context. -/
abbrev Usage (Γ : Ctx) := (i : Fin Γ.length) -> Grade

namespace Usage

def unused : Usage Γ := fun _ => .sec

def single (target : Fin Γ.length) : Usage Γ := fun i =>
  if i = target then .pub else .sec

def add (ρ σ : Usage Γ) : Usage Γ := fun i => ρ i + σ i

def scale (r : Grade) (ρ : Usage Γ) : Usage Γ := fun i => r * ρ i

def cons (r : Grade) (ρ : Usage Γ) : Usage (A :: Γ) := fun i =>
  Fin.cases r ρ i

def head (ρ : Usage (A :: Γ)) : Grade := ρ 0

def tail (ρ : Usage (A :: Γ)) : Usage Γ := fun i => ρ i.succ

def LE (ρ σ : Usage Γ) : Prop := ∀ i, ρ i ≤ σ i

@[simp] theorem single_self {Γ : Ctx} (i : Fin Γ.length) : single i i = .pub := by
  simp [single]

@[simp] theorem cons_zero (r : Grade) (ρ : Usage Γ) : cons (A := A) r ρ 0 = r := rfl

@[simp] theorem cons_succ (r : Grade) (ρ : Usage Γ) (i : Fin Γ.length) :
    cons (A := A) r ρ i.succ = ρ i := rfl

@[simp] theorem head_cons (r : Grade) (ρ : Usage Γ) : head (cons (A := A) r ρ) = r := rfl

@[simp] theorem tail_cons (r : Grade) (ρ : Usage Γ) : tail (cons (A := A) r ρ) = ρ := rfl

theorem le_refl (ρ : Usage Γ) : LE ρ ρ := fun i => Grade.le_refl (ρ i)

theorem le_trans {ρ σ τ : Usage Γ} (hρσ : LE ρ σ) (hστ : LE σ τ) : LE ρ τ :=
  fun i => Grade.le_trans (hρσ i) (hστ i)

end Usage

/--
An intrinsically typed presentation of FlowSTLC.
`Term Γ ρ A` is simultaneously a term and a derivation of `Γ @ ρ |- t : A`.
The `approx` constructor has the report's security-specific direction `ρ' <= ρ`.
-/
inductive Term : (Γ : Ctx) -> Usage Γ -> Ty -> Type where
  | var (i : Fin Γ.length) : Term Γ (Usage.single i) (Γ.get i)
  | lam (body : Term (A :: Γ) ρ B) :
      Term Γ (Usage.tail ρ) (.arr (Usage.head ρ) A B)
  | app (fn : Term Γ ρf (.arr r A B)) (arg : Term Γ ρa A) :
      Term Γ (Usage.add ρf (Usage.scale r ρa)) B
  | promote (r : Grade) (term : Term Γ ρ A) :
      Term Γ (Usage.scale r ρ) (.box r A)
  | letBox (boxed : Term Γ ρs (.box r A))
      (body : Term (A :: Γ) (Usage.cons r ρb) B) :
      Term Γ (Usage.add ρs ρb) B
  | approx (term : Term Γ ρ A) (allowed : Usage.LE ρ' ρ) : Term Γ ρ' A
  | record (left : Term Γ ρl A) (right : Term Γ ρr B) :
      Term Γ (Usage.add ρl ρr) (.record A B)
  | first (record : Term Γ ρ (.record A B)) : Term Γ ρ A
  | second (record : Term Γ ρ (.record A B)) : Term Γ ρ B
  | true : Term Γ Usage.unused .bool
  | false : Term Γ Usage.unused .bool
  | ite (controlGrade : Grade) (publicControl : controlGrade ≤ .pub)
      (condition : Term Γ ρc .bool) (thenBranch : Term Γ ρt A)
      (elseBranch : Term Γ ρe A) :
      Term Γ (Usage.add (Usage.scale controlGrade ρc) (Usage.add ρt ρe)) A
  | zero : Term Γ Usage.unused .nat
  | succ (term : Term Γ ρ .nat) : Term Γ ρ .nat
  | pred (term : Term Γ ρ .nat) : Term Γ ρ .nat
  | isZero (term : Term Γ ρ .nat) : Term Γ ρ .bool
  | unit : Term Γ Usage.unused .unit
  | letUnit (unitTerm : Term Γ ρu .unit) (body : Term Γ ρb A) :
      Term Γ (Usage.add ρu ρb) A

/-- Type-indexed semantic values. Function values are total Lean functions. -/
def Val : Ty -> Type
  | .unit => PUnit
  | .bool => Bool
  | .nat => Nat
  | .record A B => Val A × Val B
  | .arr _ A B => Val A -> Val B
  | .box _ A => Val A

/-- A type-correct environment for a de Bruijn context. -/
def Env : Ctx -> Type
  | [] => PUnit
  | A :: Γ => Val A × Env Γ

namespace Env

def lookup : {Γ : Ctx} -> Env Γ -> (i : Fin Γ.length) -> Val (Γ.get i)
  | _ :: _, (value, _), ⟨0, _⟩ => value
  | _ :: _, (_, rest), ⟨n + 1, inBounds⟩ =>
      lookup rest ⟨n, Nat.lt_of_succ_lt_succ inBounds⟩

def empty : Env [] := PUnit.unit

def extend (value : Val A) (env : Env Γ) : Env (A :: Γ) := (value, env)

def AgreeExcept {Γ : Ctx} (e₁ e₂ : Env Γ) (except : Fin Γ.length) : Prop :=
  ∀ i, i ≠ except -> Env.lookup e₁ i = Env.lookup e₂ i

end Env

/-- Total, call-by-value denotational evaluation of a typing derivation. -/
def Term.eval : Term Γ ρ A -> Env Γ -> Val A
  | .var i, env => Env.lookup env i
  | .lam body, env => fun value => body.eval (Env.extend value env)
  | .app fn arg, env => fn.eval env (arg.eval env)
  | .promote _ term, env => term.eval env
  | .letBox boxed body, env => body.eval (Env.extend (boxed.eval env) env)
  | .approx term _, env => term.eval env
  | .record left right, env => (left.eval env, right.eval env)
  | .first pairTerm, env => (pairTerm.eval env).1
  | .second pairTerm, env => (pairTerm.eval env).2
  | .true, _ => Bool.true
  | .false, _ => Bool.false
  | .ite _ _ condition thenBranch elseBranch, env =>
      bif condition.eval env then thenBranch.eval env else elseBranch.eval env
  | .zero, _ => Nat.zero
  | .succ term, env => Nat.succ (term.eval env)
  | .pred term, env => Nat.pred (term.eval env)
  | .isZero term, env => Nat.beq (term.eval env) Nat.zero
  | .unit, _ => PUnit.unit
  | .letUnit unitTerm body, env =>
      let _ := unitTerm.eval env
      body.eval env

/-- Typed call-by-value big-step semantics. The result index is the static
type of the source term, so a derivation cannot produce an ill-typed value. -/
inductive Evaluates : {Γ : Ctx} -> {ρ : Usage Γ} -> {A : Ty} ->
    Term Γ ρ A -> Env Γ -> Val A -> Prop where
  | var (env : Env Γ) (i : Fin Γ.length) :
      Evaluates (.var i) env (Env.lookup env i)
  | lam (env : Env Γ) (body : Term (A :: Γ) ρ B) :
      Evaluates (.lam body) env (fun value => body.eval (Env.extend value env))
  | app (fn : Term Γ ρf (.arr r A B)) (arg : Term Γ ρa A) (env : Env Γ)
      (f : Val A -> Val B) (value : Val A)
      (fnEval : Evaluates fn env f) (argEval : Evaluates arg env value) :
      Evaluates (.app fn arg) env (f value)
  | promote (r : Grade) (term : Term Γ ρ A) (env : Env Γ) (value : Val A)
      (termEval : Evaluates term env value) :
      Evaluates (.promote r term) env value
  | letBox (boxed : Term Γ ρs (.box r A))
      (body : Term (A :: Γ) (Usage.cons r ρb) B) (env : Env Γ)
      (value : Val A) (result : Val B)
      (boxedEval : Evaluates boxed env value)
      (bodyEval : Evaluates body (Env.extend value env) result) :
      Evaluates (.letBox boxed body) env result
  | approx (term : Term Γ ρ A) (allowed : Usage.LE ρ' ρ)
      (env : Env Γ) (value : Val A) (termEval : Evaluates term env value) :
      Evaluates (.approx term allowed) env value
  | record (left : Term Γ ρl A) (right : Term Γ ρr B) (env : Env Γ)
      (leftValue : Val A) (rightValue : Val B)
      (leftEval : Evaluates left env leftValue)
      (rightEval : Evaluates right env rightValue) :
      Evaluates (.record left right) env (leftValue, rightValue)
  | first (pairTerm : Term Γ ρ (.record A B)) (env : Env Γ)
      (leftValue : Val A) (rightValue : Val B)
      (pairEval : Evaluates pairTerm env (leftValue, rightValue)) :
      Evaluates (.first pairTerm) env leftValue
  | second (pairTerm : Term Γ ρ (.record A B)) (env : Env Γ)
      (leftValue : Val A) (rightValue : Val B)
      (pairEval : Evaluates pairTerm env (leftValue, rightValue)) :
      Evaluates (.second pairTerm) env rightValue
  | true (env : Env Γ) : Evaluates (.true : Term Γ Usage.unused .bool) env Bool.true
  | false (env : Env Γ) : Evaluates (.false : Term Γ Usage.unused .bool) env Bool.false
  | iteTrue (controlGrade : Grade) (publicControl : controlGrade ≤ .pub)
      (condition : Term Γ ρc .bool) (thenBranch : Term Γ ρt A)
      (elseBranch : Term Γ ρe A) (env : Env Γ) (result : Val A)
      (conditionEval : Evaluates condition env Bool.true)
      (branchEval : Evaluates thenBranch env result) :
      Evaluates (.ite controlGrade publicControl condition thenBranch elseBranch) env result
  | iteFalse (controlGrade : Grade) (publicControl : controlGrade ≤ .pub)
      (condition : Term Γ ρc .bool) (thenBranch : Term Γ ρt A)
      (elseBranch : Term Γ ρe A) (env : Env Γ) (result : Val A)
      (conditionEval : Evaluates condition env Bool.false)
      (branchEval : Evaluates elseBranch env result) :
      Evaluates (.ite controlGrade publicControl condition thenBranch elseBranch) env result
  | zero (env : Env Γ) : Evaluates (.zero : Term Γ Usage.unused .nat) env Nat.zero
  | succ (term : Term Γ ρ .nat) (env : Env Γ) (value : Nat)
      (termEval : Evaluates term env value) :
      Evaluates (.succ term) env (Nat.succ value)
  | pred (term : Term Γ ρ .nat) (env : Env Γ) (value : Nat)
      (termEval : Evaluates term env value) :
      Evaluates (.pred term) env (Nat.pred value)
  | isZero (term : Term Γ ρ .nat) (env : Env Γ) (value : Nat)
      (termEval : Evaluates term env value) :
      Evaluates (.isZero term) env (Nat.beq value 0)
  | unit (env : Env Γ) : Evaluates (.unit : Term Γ Usage.unused .unit) env PUnit.unit
  | letUnit (unitTerm : Term Γ ρu .unit) (body : Term Γ ρb A)
      (env : Env Γ) (result : Val A)
      (unitEval : Evaluates unitTerm env PUnit.unit)
      (bodyEval : Evaluates body env result) :
      Evaluates (.letUnit unitTerm body) env result

end FlowSTLC
