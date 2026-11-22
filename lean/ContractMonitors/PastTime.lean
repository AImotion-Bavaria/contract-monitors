import ContractMonitors.Monitor

/-!
# A past-time contract language and its monitors

Past-time temporal formulas with bounded time windows over observations.
They are evaluated at the last position of a prefix, so every formula denotes
a prefix predicate and is monitorable without delay.

`synth` translates a formula into a state machine whose state consists of one
Boolean per `prev` and `since`, one counter bounded by the window length per
`onceWithin`, `k` Booleans per `countWithin k`, and `k` stored observations
per `lag k`. `synthMonitor_correct` states that its verdict
coincides with the semantics on every prefix.
-/

namespace ContractMonitors

/-- Past-time formulas with bounded windows. -/
inductive Fml (σ : Type) where
  | atom (p : σ → Bool)
  /-- `lag k q`: `q` relates the observation `k` ticks ago and the current
  one. -/
  | lag (k : Nat) (q : σ → σ → Bool)
  | neg (φ : Fml σ)
  | conj (φ ψ : Fml σ)
  /-- `prev φ`: `φ` held one tick ago. -/
  | prev (φ : Fml σ)
  /-- `since φ ψ`: `ψ` held at some past tick and `φ` has held ever since. -/
  | since (φ ψ : Fml σ)
  /-- `onceWithin k φ`: `φ` held now or at one of the last `k` ticks. -/
  | onceWithin (k : Nat) (φ : Fml σ)
  /-- `countWithin k n φ`: `φ` held at least `n` times now and during the
  last `k` ticks. -/
  | countWithin (k n : Nat) (φ : Fml σ)

variable {σ : Type}

/-! ## Semantics

Histories are given newest first. Each temporal operator has a semantic
function over the truth functions of its operands. -/

/-- `q` relates the observation `k` positions back and the newest one. -/
def lagSpec (k : Nat) (q : σ → σ → Bool) : List σ → Bool
  | [] => false
  | s :: rest =>
    match (s :: rest)[k]? with
    | some y => q y s
    | none => false

/-- `g` held at some position and `f` at all positions since. -/
def sinceSpec (f g : List σ → Bool) : List σ → Bool
  | [] => false
  | s :: rest => g (s :: rest) || (f (s :: rest) && sinceSpec f g rest)

/-- `f` held at the newest position or one of the `k` before. -/
def withinSpec (f : List σ → Bool) : Nat → List σ → Bool
  | _, [] => false
  | 0, x :: rest => f (x :: rest)
  | j + 1, x :: rest => f (x :: rest) || withinSpec f j rest

/-- The truth values of `f` at all positions, newest first. -/
def vals (f : List σ → Bool) : List σ → List Bool
  | [] => []
  | s :: rest => f (s :: rest) :: vals f rest

/-- `f` held at least `n` times at the newest position and the `k` before. -/
def countSpec (k n : Nat) (f : List σ → Bool) : List σ → Bool
  | [] => false
  | s :: rest => decide (n ≤ ((vals f (s :: rest)).take (k + 1)).count true)

namespace Fml

/-- Truth at the most recent observation of a history given newest first. -/
def holdsRev : Fml σ → List σ → Bool
  | .atom p => fun l => match l with
    | [] => false
    | s :: _ => p s
  | .lag k q => lagSpec k q
  | .neg φ => fun l => match l with
    | [] => false
    | _ :: _ => !(φ.holdsRev l)
  | .conj φ ψ => fun l => φ.holdsRev l && ψ.holdsRev l
  | .prev φ => fun l => match l with
    | [] => false
    | _ :: rest => φ.holdsRev rest
  | .since φ ψ => sinceSpec φ.holdsRev ψ.holdsRev
  | .onceWithin k φ => withinSpec φ.holdsRev k
  | .countWithin k n φ => countSpec k n φ.holdsRev

/-- The prefix predicate denoted by a formula. The empty prefix is fine. -/
def holds (φ : Fml σ) (pre : Prefix σ) : Bool :=
  pre.isEmpty || φ.holdsRev pre.reverse

/-- `step q`: `q` relates the previous and the current observation. -/
def step (q : σ → σ → Bool) : Fml σ := .lag 1 q

/-- `once φ`: `φ` held at some past tick (including now). -/
def once (φ : Fml σ) : Fml σ := .since (.atom fun _ => true) φ

/-- `hist φ`: `φ` has held at every tick so far. -/
def hist (φ : Fml σ) : Fml σ := .neg (once (.neg φ))

/-- `histWithin k φ`: `φ` has held now and at each of the last `k` ticks. -/
def histWithin (k : Nat) (φ : Fml σ) : Fml σ := .neg (.onceWithin k (.neg φ))

end Fml

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

/-- Stores the last `k` observations, newest first. -/
def lag (k : Nat) (q : σ → σ → Bool) : Machine σ where
  State := List σ
  init := []
  step := fun buf x =>
    ((x :: buf).take k,
      match (x :: buf)[k]? with
      | some y => q y x
      | none => false)

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

/-- Stores the last `k` outputs of `m`, newest first. -/
def count (k n : Nat) (m : Machine σ) : Machine σ where
  State := m.State × List Bool
  init := (m.init, [])
  step := fun s x =>
    (((m.step s.1 x).1, ((m.step s.1 x).2 :: s.2).take k),
      decide (n ≤ ((m.step s.1 x).2 :: s.2).count true))

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

theorem take_cons_take {α : Type} (x : α) (l : List α) (k : Nat) :
    (x :: l.take k).take k = (x :: l).take k := by
  cases k with
  | zero => rfl
  | succ j => simp [List.take_take]

theorem stateRev_lag (k : Nat) (q : σ → σ → Bool) (l : List σ) :
    (lag k q).stateRev l = l.take k := by
  induction l with
  | nil => simp [stateRev, lag]
  | cons x rest ih =>
    show (x :: (lag k q).stateRev rest).take k = _
    rw [ih, take_cons_take]

/-- **Bounded memory.** A lag atom stores at most `k` observations. -/
theorem lag_buffer_le (k : Nat) (q : σ → σ → Bool) (l : List σ) :
    ((lag k q).stateRev l : List σ).length ≤ k := by
  rw [stateRev_lag]; exact List.length_take_le k l

theorem stateRev_count (k n : Nat) (m : Machine σ) (l : List σ) :
    (count k n m).stateRev l = (m.stateRev l, (vals m.outRev l).take k) := by
  induction l with
  | nil => simp [stateRev, count, vals]
  | cons x rest ih =>
    show ((m.step ((count k n m).stateRev rest).1 x).1,
        ((m.step ((count k n m).stateRev rest).1 x).2 ::
          ((count k n m).stateRev rest).2).take k) = _
    rw [ih]
    show (_, (m.outRev (x :: rest) :: (vals m.outRev rest).take k).take k) = _
    rw [take_cons_take]; rfl

/-- **Bounded memory.** A counting operator stores at most `k` bits. -/
theorem count_buffer_le (k n : Nat) (m : Machine σ) (l : List σ) :
    ((count k n m).stateRev l).2.length ≤ k := by
  rw [stateRev_count]; exact List.length_take_le k _

/-! ### Outputs as functions of the history -/

theorem outRev_atom (p : σ → Bool) :
    (atom p).outRev = fun l => match l with
      | [] => false
      | s :: _ => p s := by
  funext l; cases l <;> rfl

theorem outRev_lag (k : Nat) (q : σ → σ → Bool) : (lag k q).outRev = lagSpec k q := by
  funext l
  cases l with
  | nil => rfl
  | cons x rest =>
    show (match (x :: (lag k q).stateRev rest)[k]? with
      | some y => q y x
      | none => false) = lagSpec k q (x :: rest)
    rw [stateRev_lag]
    have : (x :: rest.take k)[k]? = (x :: rest)[k]? := by
      cases k with
      | zero => rfl
      | succ j => simp
    rw [this]; rfl

theorem outRev_neg (m : Machine σ) :
    (neg m).outRev = fun l => match l with
      | [] => false
      | _ :: _ => !(m.outRev l) := by
  funext l
  cases l with
  | nil => rfl
  | cons x rest => exact outRev_neg_cons m x rest

theorem outRev_conj (m n : Machine σ) :
    (conj m n).outRev = fun l => m.outRev l && n.outRev l := by
  funext l
  cases l with
  | nil => rfl
  | cons x rest => exact outRev_conj_cons m n x rest

theorem outRev_prev (m : Machine σ) :
    (prev m).outRev = fun l => match l with
      | [] => false
      | _ :: rest => m.outRev rest := by
  funext l
  cases l with
  | nil => rfl
  | cons x rest => exact outRev_prev_cons m x rest

theorem outRev_since (m n : Machine σ) :
    (since m n).outRev = sinceSpec m.outRev n.outRev := by
  funext l
  induction l with
  | nil => rfl
  | cons x rest ih => rw [outRev_since_cons, ih]; rfl

theorem outRev_within' (k : Nat) (m : Machine σ) :
    (within k m).outRev = withinSpec m.outRev k :=
  funext (outRev_within k m)

theorem outRev_count (k n : Nat) (m : Machine σ) :
    (count k n m).outRev = countSpec k n m.outRev := by
  funext l
  cases l with
  | nil => rfl
  | cons x rest =>
    show decide (n ≤ ((m.step ((count k n m).stateRev rest).1 x).2 ::
        ((count k n m).stateRev rest).2).count true) = _
    rw [stateRev_count]; rfl

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
  | .lag k q => Machine.lag k q
  | .neg φ => Machine.neg (synth φ)
  | .conj φ ψ => Machine.conj (synth φ) (synth ψ)
  | .prev φ => Machine.prev (synth φ)
  | .since φ ψ => Machine.since (synth φ) (synth ψ)
  | .onceWithin k φ => Machine.within k (synth φ)
  | .countWithin k n φ => Machine.count k n (synth φ)

theorem synth_outRev (φ : Fml σ) : (synth φ).outRev = φ.holdsRev := by
  induction φ with
  | atom p => exact Machine.outRev_atom p
  | lag k q => exact Machine.outRev_lag k q
  | neg φ ih =>
    show (Machine.neg (synth φ)).outRev = _
    rw [Machine.outRev_neg, ih]; rfl
  | conj φ ψ ihφ ihψ =>
    show (Machine.conj (synth φ) (synth ψ)).outRev = _
    rw [Machine.outRev_conj, ihφ, ihψ]; rfl
  | prev φ ih =>
    show (Machine.prev (synth φ)).outRev = _
    rw [Machine.outRev_prev, ih]; rfl
  | since φ ψ ihφ ihψ =>
    show (Machine.since (synth φ) (synth ψ)).outRev = _
    rw [Machine.outRev_since, ihφ, ihψ]; rfl
  | onceWithin k φ ih =>
    show (Machine.within k (synth φ)).outRev = _
    rw [Machine.outRev_within', ih]; rfl
  | countWithin k n φ ih =>
    show (Machine.count k n (synth φ)).outRev = _
    rw [Machine.outRev_count, ih]; rfl

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
