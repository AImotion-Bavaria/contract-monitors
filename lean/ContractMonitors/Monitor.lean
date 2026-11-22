import ContractMonitors.Basic

/-!
# Monitors

A monitor is a deterministic state machine that consumes one observation per
tick and exposes a Boolean verdict (`true` = no violation so far observed at
this point).
-/

namespace ContractMonitors

/-- A runtime monitor over observations `σ`. -/
structure Monitor (σ : Type) where
  State : Type
  init : State
  step : State → σ → State
  ok : State → Bool

variable {σ : Type}

namespace Monitor

/-- State after consuming a prefix, starting from `s`. -/
def runFrom (M : Monitor σ) (s : M.State) (pre : Prefix σ) : M.State :=
  pre.foldl M.step s

/-- State after consuming a prefix. -/
def run (M : Monitor σ) (pre : Prefix σ) : M.State := M.runFrom M.init pre

/-- Verdict after consuming a prefix. -/
def verdict (M : Monitor σ) (pre : Prefix σ) : Bool := M.ok (M.run pre)

theorem run_append_singleton (M : Monitor σ) (pre : Prefix σ) (x : σ) :
    M.run (pre ++ [x]) = M.step (M.run pre) x := by
  simp [run, runFrom, List.foldl_append]

/-- **Monitor correctness (T1, specification).** The monitor's verdict
coincides with the prefix predicate on every finite observation. -/
def Correct (M : Monitor σ) (P : Prefix σ → Bool) : Prop :=
  ∀ pre, M.verdict pre = P pre

/-- A correct monitor never raises an alarm on a trace iff the trace
satisfies the induced safety property. -/
theorem Correct.no_alarm_iff {M : Monitor σ} {P : Prefix σ → Bool}
    (h : M.Correct P) (tr : Trace σ) :
    (∀ n, M.verdict (tr.take n) = true) ↔ Always P tr := by
  constructor
  · intro hv n; rw [← h]; exact hv n
  · intro hp n; rw [h]; exact hp n

/-- Two monitors running side by side; the joint verdict is the conjunction.
This models a centralised monitor evaluating several contracts at once. -/
def prod (M₁ M₂ : Monitor σ) : Monitor σ where
  State := M₁.State × M₂.State
  init := (M₁.init, M₂.init)
  step := fun s x => (M₁.step s.1 x, M₂.step s.2 x)
  ok := fun s => M₁.ok s.1 && M₂.ok s.2

theorem runFrom_prod (M₁ M₂ : Monitor σ) (s₁ : M₁.State) (s₂ : M₂.State)
    (pre : Prefix σ) :
    (prod M₁ M₂).runFrom (s₁, s₂) pre = (M₁.runFrom s₁ pre, M₂.runFrom s₂ pre) := by
  induction pre generalizing s₁ s₂ with
  | nil => rfl
  | cons x xs ih => exact ih (M₁.step s₁ x) (M₂.step s₂ x)

/-- **Centralised = federated (T2).** The verdict of the centralised monitor
is the conjunction of the verdicts of the individual monitors. -/
theorem verdict_prod (M₁ M₂ : Monitor σ) (pre : Prefix σ) :
    (prod M₁ M₂).verdict pre = (M₁.verdict pre && M₂.verdict pre) := by
  show (prod M₁ M₂).ok ((prod M₁ M₂).runFrom (M₁.init, M₂.init) pre) = _
  rw [runFrom_prod]; rfl

/-- Correctness is compositional. -/
theorem Correct.prod {M₁ M₂ : Monitor σ} {P₁ P₂ : Prefix σ → Bool}
    (h₁ : M₁.Correct P₁) (h₂ : M₂.Correct P₂) :
    (prod M₁ M₂).Correct (fun pre => P₁ pre && P₂ pre) := by
  intro pre; rw [verdict_prod, h₁, h₂]

end Monitor

end ContractMonitors
