/-!
# Traces and prefixes

Time-synchronous stream model in the spirit of FOCUS: time is divided into
ticks, and a trace assigns one observation to every tick. An observation `σ`
is the valuation of all channels of the syntactic interface in that tick
(for a single channel with messages `M`, take `σ := Option M`, where `none`
plays the role of ⊥).
-/

namespace ContractMonitors

/-- An infinite behaviour: one observation per tick. -/
abbrev Trace (σ : Type) := Nat → σ

/-- A finite observation in chronological order (oldest first). -/
abbrev Prefix (σ : Type) := List σ

/-- The first `n` ticks of a trace. -/
def Trace.take {σ : Type} (tr : Trace σ) (n : Nat) : Prefix σ :=
  (List.range n).map tr

@[simp] theorem Trace.take_length {σ : Type} (tr : Trace σ) (n : Nat) :
    (tr.take n).length = n := by
  simp [Trace.take]

/-- A prefix predicate holds on a prefix and on all of its initial segments. -/
def HoldsUpTo {σ : Type} (P : Prefix σ → Bool) (pre : Prefix σ) : Prop :=
  ∀ n, n ≤ pre.length → P (pre.take n) = true

/-- A safety property given by a decidable predicate on prefixes:
the trace is fine iff every finite prefix is fine. -/
def Always {σ : Type} (P : Prefix σ → Bool) : Trace σ → Prop :=
  fun tr => ∀ n, P (tr.take n) = true

end ContractMonitors
