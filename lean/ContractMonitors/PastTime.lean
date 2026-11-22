import ContractMonitors.Monitor

/-!
# A past-time contract language and its monitors

Past-time temporal formulas with bounded time windows over observations.
They are evaluated at the last position of a prefix, so every formula denotes
a prefix predicate and is monitorable without delay.

`synth` translates a formula into a state machine whose state consists of one
Boolean per temporal operator, one counter, bounded by the window length,
per bounded operator, and one stored observation per step atom. `synthMonitor_correct` states that its verdict
coincides with the semantics on every prefix.
-/

namespace ContractMonitors

/-- Past-time formulas with bounded windows. -/
inductive Fml (σ : Type) where
  | atom (p : σ → Bool)
  /-- `step q`: `q` relates the previous and the current observation. -/
  | step (q : σ → σ → Bool)
  | neg (φ : Fml σ)
  | conj (φ ψ : Fml σ)
  /-- `prev φ`: `φ` held one tick ago. -/
  | prev (φ : Fml σ)
  /-- `since φ ψ`: `ψ` held at some past tick and `φ` has held ever since. -/
  | since (φ ψ : Fml σ)
  /-- `onceWithin k φ`: `φ` held now or at one of the last `k` ticks. -/
  | onceWithin (k : Nat) (φ : Fml σ)

variable {σ : Type}

namespace Fml

/-- Truth at the most recent observation of a history given newest first. -/
def holdsRev : Fml σ → List σ → Bool
  | _, [] => false
  | .atom p, s :: _ => p s
  | .step _, [_] => false
  | .step q, s :: s' :: _ => q s' s
  | .neg φ, s :: rest => !(φ.holdsRev (s :: rest))
  | .conj φ ψ, s :: rest => φ.holdsRev (s :: rest) && ψ.holdsRev (s :: rest)
  | .prev φ, _ :: rest => φ.holdsRev rest
  | .since φ ψ, s :: rest =>
      ψ.holdsRev (s :: rest) ||
        (φ.holdsRev (s :: rest) && (Fml.since φ ψ).holdsRev rest)
  | .onceWithin 0 φ, s :: rest => φ.holdsRev (s :: rest)
  | .onceWithin (k + 1) φ, s :: rest =>
      φ.holdsRev (s :: rest) || (Fml.onceWithin k φ).holdsRev rest
termination_by φ l => (φ, l.length)

/-- The prefix predicate denoted by a formula. The empty prefix is fine. -/
def holds (φ : Fml σ) (pre : Prefix σ) : Bool :=
  pre.isEmpty || φ.holdsRev pre.reverse

/-- `once φ`: `φ` held at some past tick (including now). -/
def once (φ : Fml σ) : Fml σ := .since (.atom fun _ => true) φ

/-- `hist φ`: `φ` has held at every tick so far. -/
def hist (φ : Fml σ) : Fml σ := .neg (once (.neg φ))

/-- `histWithin k φ`: `φ` has held now and at each of the last `k` ticks. -/
def histWithin (k : Nat) (φ : Fml σ) : Fml σ := .neg (.onceWithin k (.neg φ))

end Fml

/-- Semantics of a bounded window over an arbitrary truth function. -/
def withinSpec (f : List σ → Bool) : Nat → List σ → Bool
  | _, [] => false
  | 0, x :: rest => f (x :: rest)
  | j + 1, x :: rest => f (x :: rest) || withinSpec f j rest

theorem Fml.holdsRev_onceWithin (φ : Fml σ) (k : Nat) (l : List σ) :
    (Fml.onceWithin k φ).holdsRev l = withinSpec φ.holdsRev k l := by
  induction k generalizing l with
  | zero => cases l <;> simp [Fml.holdsRev, withinSpec]
  | succ k ih => cases l <;> simp [Fml.holdsRev, withinSpec, ih]

/-! ## State machines -/

/-- A machine that emits one truth value per consumed observation. -/
structure Machine (σ : Type) where
  State : Type
  init : State
  step : State → σ → State × Bool

namespace Machine

/-- State after consuming a history given newest first. -/
def stateRev (m : Machine σ) : List σ → m.State
  | [] => m.init
  | x :: rest => (m.step (m.stateRev rest) x).1

/-- Output for the most recent observation of a history given newest first. -/
def outRev (m : Machine σ) : List σ → Bool
  | [] => false
  | x :: rest => (m.step (m.stateRev rest) x).2

def atom (p : σ → Bool) : Machine σ where
  State := Unit
  init := ()
  step := fun _ x => ((), p x)

/-- Stores the previous observation. -/
def step2 (q : σ → σ → Bool) : Machine σ where
  State := Option σ
  init := none
  step := fun s x => (some x, match s with | none => false | some y => q y x)

def neg (m : Machine σ) : Machine σ where
  State := m.State
  init := m.init
  step := fun s x => ((m.step s x).1, !(m.step s x).2)

def conj (m n : Machine σ) : Machine σ where
  State := m.State × n.State
  init := (m.init, n.init)
  step := fun s x =>
    (((m.step s.1 x).1, (n.step s.2 x).1), (m.step s.1 x).2 && (n.step s.2 x).2)

/-- Stores the previous output of `m`. -/
def prev (m : Machine σ) : Machine σ where
  State := m.State × Bool
  init := (m.init, false)
  step := fun s x => (((m.step s.1 x).1, (m.step s.1 x).2), s.2)

/-- Stores its own previous output. -/
def since (m n : Machine σ) : Machine σ where
  State := m.State × n.State × Bool
  init := (m.init, n.init, false)
  step := fun s x =>
    let v := (n.step s.2.1 x).2 || ((m.step s.1 x).2 && s.2.2)
    (((m.step s.1 x).1, (n.step s.2.1 x).1, v), v)

/-- Counter update: ticks since `m` last emitted `true`, saturating at `k + 1`. -/
def tick (k : Nat) (hit : Bool) (c : Nat) : Nat :=
  if hit then 0 else min (c + 1) (k + 1)

/-- Counts the ticks since `m` last emitted `true`. -/
def within (k : Nat) (m : Machine σ) : Machine σ where
  State := m.State × Nat
  init := (m.init, k + 1)
  step := fun s x =>
    (((m.step s.1 x).1, tick k (m.step s.1 x).2 s.2),
      decide (tick k (m.step s.1 x).2 s.2 ≤ k))

/-! ### Combinator lemmas -/

theorem stateRev_neg (m : Machine σ) (l : List σ) :
    (neg m).stateRev l = m.stateRev l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    exact congrArg (fun s => (m.step s x).1) ih

theorem outRev_neg_cons (m : Machine σ) (x : σ) (rest : List σ) :
    (neg m).outRev (x :: rest) = !(m.outRev (x :: rest)) :=
  congrArg (fun s => !(m.step s x).2) (stateRev_neg m rest)

theorem stateRev_conj (m n : Machine σ) (l : List σ) :
    (conj m n).stateRev l = (m.stateRev l, n.stateRev l) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    exact congrArg (fun s => ((conj m n).step s x).1) ih

theorem outRev_conj_cons (m n : Machine σ) (x : σ) (rest : List σ) :
    (conj m n).outRev (x :: rest) = (m.outRev (x :: rest) && n.outRev (x :: rest)) :=
  congrArg (fun s => ((conj m n).step s x).2) (stateRev_conj m n rest)

theorem stateRev_prev (m : Machine σ) (l : List σ) :
    (prev m).stateRev l = (m.stateRev l, m.outRev l) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    exact congrArg (fun s => ((prev m).step s x).1) ih

theorem outRev_prev_cons (m : Machine σ) (x : σ) (rest : List σ) :
    (prev m).outRev (x :: rest) = m.outRev rest :=
  congrArg (fun s => ((prev m).step s x).2) (stateRev_prev m rest)

theorem stateRev_since (m n : Machine σ) (l : List σ) :
    (since m n).stateRev l = (m.stateRev l, n.stateRev l, (since m n).outRev l) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    show ((since m n).step ((since m n).stateRev rest) x).1 =
      (m.stateRev (x :: rest), n.stateRev (x :: rest),
        ((since m n).step ((since m n).stateRev rest) x).2)
    rw [ih]; rfl

theorem outRev_since_cons (m n : Machine σ) (x : σ) (rest : List σ) :
    (since m n).outRev (x :: rest) =
      (n.outRev (x :: rest) || (m.outRev (x :: rest) && (since m n).outRev rest)) :=
  congrArg (fun s => ((since m n).step s x).2) (stateRev_since m n rest)

/-- The counter kept by `within`, as a function of the history. -/
def ctr (k : Nat) (f : List σ → Bool) : List σ → Nat
  | [] => k + 1
  | x :: rest => tick k (f (x :: rest)) (ctr k f rest)

theorem stateRev_within (k : Nat) (m : Machine σ) (l : List σ) :
    (within k m).stateRev l = (m.stateRev l, ctr k m.outRev l) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    exact congrArg (fun s => ((within k m).step s x).1) ih

theorem outRev_within_cons (k : Nat) (m : Machine σ) (x : σ) (rest : List σ) :
    (within k m).outRev (x :: rest) = decide (ctr k m.outRev (x :: rest) ≤ k) :=
  congrArg (fun s => ((within k m).step s x).2) (stateRev_within k m rest)

/-- **Bounded memory.** The counter never exceeds the window length plus one. -/
theorem ctr_le (k : Nat) (f : List σ → Bool) (l : List σ) : ctr k f l ≤ k + 1 := by
  cases l with
  | nil => exact Nat.le_refl _
  | cons x rest =>
    show tick k (f (x :: rest)) (ctr k f rest) ≤ k + 1
    unfold tick
    split
    · exact Nat.zero_le _
    · exact Nat.min_le_right _ _

theorem ctr_le_iff (k : Nat) (f : List σ → Bool) (l : List σ) (j : Nat) (hj : j ≤ k) :
    ctr k f l ≤ j ↔ withinSpec f j l = true := by
  induction l generalizing j with
  | nil => simp [ctr, withinSpec]; omega
  | cons x rest ih =>
    show tick k (f (x :: rest)) (ctr k f rest) ≤ j ↔ _
    unfold tick
    cases hf : f (x :: rest) with
    | true => cases j <;> simp [withinSpec, hf]
    | false =>
      cases j with
      | zero => simp [withinSpec, hf]
      | succ j =>
        have := ih j (by omega)
        simp only [withinSpec, hf, Bool.false_or, ← this]
        simp
        omega

theorem outRev_within (k : Nat) (m : Machine σ) (l : List σ) :
    (within k m).outRev l = withinSpec m.outRev k l := by
  cases l with
  | nil => cases k <;> rfl
  | cons x rest =>
    rw [outRev_within_cons, Bool.eq_iff_iff, decide_eq_true_iff]
    exact ctr_le_iff k m.outRev (x :: rest) k (Nat.le_refl k)

/-- Wrap a machine as a monitor: the verdict is the last output, and `true`
before the first observation. -/
def toMonitor (m : Machine σ) : Monitor σ where
  State := m.State × Bool
  init := (m.init, true)
  step := fun s x => m.step s.1 x
  ok := fun s => s.2

theorem toMonitor_run_reverse (m : Machine σ) (l : List σ) :
    m.toMonitor.run l.reverse = (m.stateRev l, l.isEmpty || m.outRev l) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.reverse_cons, Monitor.run_append_singleton, ih]
    rfl

end Machine

/-! ## Synthesis -/

/-- **Monitor synthesis.** One combinator per operator. -/
def synth : Fml σ → Machine σ
  | .atom p => Machine.atom p
  | .step q => Machine.step2 q
  | .neg φ => Machine.neg (synth φ)
  | .conj φ ψ => Machine.conj (synth φ) (synth ψ)
  | .prev φ => Machine.prev (synth φ)
  | .since φ ψ => Machine.since (synth φ) (synth ψ)
  | .onceWithin k φ => Machine.within k (synth φ)

theorem synth_outRev (φ : Fml σ) : ∀ l, (synth φ).outRev l = φ.holdsRev l := by
  induction φ with
  | atom p =>
    intro l; cases l <;> simp [synth, Machine.atom, Machine.outRev, Fml.holdsRev]
  | step q =>
    intro l
    cases l with
    | nil => simp [Machine.outRev, Fml.holdsRev]
    | cons x rest =>
      cases rest <;>
        simp [synth, Machine.step2, Machine.outRev, Machine.stateRev, Fml.holdsRev]
  | neg φ ih =>
    intro l
    cases l with
    | nil => simp [Machine.outRev, Fml.holdsRev]
    | cons x rest => simp [synth, Machine.outRev_neg_cons, ih, Fml.holdsRev]
  | conj φ ψ ihφ ihψ =>
    intro l
    cases l with
    | nil => simp [Machine.outRev, Fml.holdsRev]
    | cons x rest => simp [synth, Machine.outRev_conj_cons, ihφ, ihψ, Fml.holdsRev]
  | prev φ ih =>
    intro l
    cases l with
    | nil => simp [Machine.outRev, Fml.holdsRev]
    | cons x rest => simp [synth, Machine.outRev_prev_cons, ih, Fml.holdsRev]
  | since φ ψ ihφ ihψ =>
    intro l
    induction l with
    | nil => simp [Machine.outRev, Fml.holdsRev]
    | cons x rest ihl =>
      have h := Machine.outRev_since_cons (synth φ) (synth ψ) x rest
      simp only [synth] at ihl ⊢
      rw [h, ihl, ihφ, ihψ]
      simp [Fml.holdsRev]
  | onceWithin k φ ih =>
    intro l
    have hf : (synth φ).outRev = φ.holdsRev := funext ih
    simp only [synth]
    rw [Machine.outRev_within, hf, Fml.holdsRev_onceWithin]

/-- The monitor synthesised from a formula. -/
def synthMonitor (φ : Fml σ) : Monitor σ := (synth φ).toMonitor

/-- **Monitor correctness (T1).** The synthesised monitor's verdict coincides
with the semantics of the formula on every prefix. -/
theorem synthMonitor_correct (φ : Fml σ) : (synthMonitor φ).Correct φ.holds := by
  intro pre
  have h := Machine.toMonitor_run_reverse (synth φ) pre.reverse
  rw [List.reverse_reverse] at h
  show ((synth φ).toMonitor.run pre).2 = _
  rw [h]
  simp [Fml.holds, synth_outRev]

end ContractMonitors
