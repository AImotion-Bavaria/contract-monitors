import ContractMonitors.PastTime

/-!
# Contract patterns

Formula schemas from which the contracts of the running example are built.
Each schema is an ordinary formula, so `synthMonitor_correct` applies to all
of them.
-/

namespace ContractMonitors

variable {σ : Type}

namespace Fml

/-- The formula that holds at every position. -/
def tt : Fml σ := .atom fun _ => true

/-- `impl φ ψ`: if `φ` then `ψ`. -/
def impl (φ ψ : Fml σ) : Fml σ := .neg (.conj φ (.neg ψ))

/-- `prevN k φ`: `φ` held exactly `k` ticks ago. -/
def prevN : Nat → Fml σ → Fml σ
  | 0, φ => φ
  | k + 1, φ => .prev (prevN k φ)

/-- **Invariant.** `p` holds for the current observation. -/
def invariant (p : σ → Bool) : Fml σ := .atom p

/-- **Liveliness.** `φ` holds at least once in every window of `k + 1`
ticks, checked once `k` ticks have elapsed. -/
def aliveWithin (k : Nat) (φ : Fml σ) : Fml σ :=
  impl (prevN k tt) (.onceWithin k φ)

/-- **Response.** Every request is answered within `k` ticks: if a request
occurred exactly `k` ticks ago, a response occurred since then. -/
def respondsWithin (k : Nat) (req resp : Fml σ) : Fml σ :=
  impl (prevN k req) (.onceWithin k resp)

/-- `bad` has held at each of the last `k + 1` ticks. -/
def sustained (k : Nat) (bad : Fml σ) : Fml σ :=
  .conj (prevN k tt) (histWithin k bad)

/-- **Bounded duration.** `bad` never holds for more than `k` consecutive
ticks. -/
def notLongerThan (k : Nat) (bad : Fml σ) : Fml σ := .neg (sustained k bad)

/-- **Bounded step.** From the second tick on, consecutive observations are
related by `q`. -/
def stepBounded (q : σ → σ → Bool) : Fml σ := impl (.prev tt) (.step q)

/-- **Provenance.** Whenever `out` holds, `src` held within the last `k`
ticks. -/
def backedBy (k : Nat) (out src : Fml σ) : Fml σ := impl out (.onceWithin k src)

end Fml

end ContractMonitors
