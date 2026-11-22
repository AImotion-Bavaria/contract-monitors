import ContractMonitors.Compositional

/-!
# Channels, interfaces, and local monitors

Observations are valuations of channels: per tick, every channel carries one
message or none (FOCUS: ⊥). A component has a syntactic interface `(I ▷ O)`.
Its assumption speaks about the input channels, its guarantee about input
and output channels. A monitor placed at the component sees exactly these
channels; `Monitor.Correct.localTo` shows that this is enough.
-/

namespace ContractMonitors

/-- A valuation of the channels `C` with messages `M` in one tick. -/
abbrev Val (C M : Type) := C → Option M

variable {C M : Type}

/-- Hide all channels outside `S`. -/
def Val.restrict (S : C → Bool) (v : Val C M) : Val C M :=
  fun c => if S c then v c else none

/-- A prefix predicate observes only the channels in `S`. -/
def Observes (S : C → Bool) (P : Prefix (Val C M) → Bool) : Prop :=
  ∀ pre, P (pre.map (Val.restrict S)) = P pre

namespace Monitor

/-- The monitor `Mon` placed so that it sees only the channels in `S`. -/
def localTo (S : C → Bool) (Mon : Monitor (Val C M)) : Monitor (Val C M) where
  State := Mon.State
  init := Mon.init
  step := fun s v => Mon.step s (v.restrict S)
  ok := Mon.ok

theorem runFrom_localTo (S : C → Bool) (Mon : Monitor (Val C M)) (s : Mon.State)
    (pre : Prefix (Val C M)) :
    (Mon.localTo S).runFrom s pre = Mon.runFrom s (pre.map (Val.restrict S)) := by
  induction pre generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (Mon.step s (x.restrict S))

theorem verdict_localTo (S : C → Bool) (Mon : Monitor (Val C M))
    (pre : Prefix (Val C M)) :
    (Mon.localTo S).verdict pre = Mon.verdict (pre.map (Val.restrict S)) :=
  congrArg Mon.ok (runFrom_localTo S Mon Mon.init pre)

/-- **Local monitoring.** A correct monitor for a predicate that observes
only `S` stays correct when it is fed only the channels in `S`. -/
theorem Correct.localTo {S : C → Bool} {Mon : Monitor (Val C M)}
    {P : Prefix (Val C M) → Bool} (h : Mon.Correct P) (hobs : Observes S P) :
    (Mon.localTo S).Correct P := by
  intro pre
  rw [verdict_localTo, h, hobs]

end Monitor

/-- Syntactic interface `(I ▷ O)`. -/
structure Iface (C : Type) where
  inp : C → Bool
  out : C → Bool

/-- All channels of an interface. -/
def Iface.chans (i : Iface C) : C → Bool := fun c => i.inp c || i.out c

/-- A monitorable contract attached to an interface: the assumption
constrains the inputs, the guarantee relates inputs and outputs. -/
structure IContract (C M : Type) extends PContract (Val C M) where
  iface : Iface C
  A_obs : Observes iface.inp A
  G_obs : Observes iface.chans G

namespace IContract

/-- The assumption monitor needs the input channels only. -/
theorem assumptionMonitor_local (c : IContract C M) {Mon : Monitor (Val C M)}
    (h : Mon.Correct c.A) : (Mon.localTo c.iface.inp).Correct c.A :=
  h.localTo c.A_obs

/-- The guarantee monitor needs the channels of the interface only. -/
theorem guaranteeMonitor_local (c : IContract C M) {Mon : Monitor (Val C M)}
    (h : Mon.Correct c.G) : (Mon.localTo c.iface.chans).Correct c.G :=
  h.localTo c.G_obs

end IContract

end ContractMonitors
