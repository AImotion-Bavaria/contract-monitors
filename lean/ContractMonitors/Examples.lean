import ContractMonitors.PastTime

/-!
# Examples

Contract patterns expressed in the past-time language, with executable
checks (`#guard`) that the synthesised monitor agrees with the semantics on
sample prefixes.
-/

namespace ContractMonitors

variable {σ : Type}

namespace Fml

/-- `impl φ ψ`: if `φ` then `ψ`. -/
def impl (φ ψ : Fml σ) : Fml σ := .neg (.conj φ (.neg ψ))

/-- `prevN k φ`: `φ` held exactly `k` ticks ago. -/
def prevN : Nat → Fml σ → Fml σ
  | 0, φ => φ
  | k + 1, φ => .prev (prevN k φ)

/-- **Response time.** Every request is answered within `k` ticks: if a
request occurred exactly `k` ticks ago, a response occurred since then. -/
def respondsWithin (k : Nat) (req resp : Fml σ) : Fml σ :=
  impl (prevN k req) (.onceWithin k resp)

/-- **Liveliness.** `φ` holds at least once in every window of `k + 1` ticks,
checked once `k` ticks have elapsed. -/
def aliveWithin (k : Nat) (φ : Fml σ) : Fml σ :=
  impl (prevN k (.atom fun _ => true)) (.onceWithin k φ)

end Fml

/-- Observation of a toy component: a request flag and a response flag. -/
structure Obs where
  req : Bool
  resp : Bool

def idle : Obs := ⟨false, false⟩
def request : Obs := ⟨true, false⟩
def response : Obs := ⟨false, true⟩

/-- Requests are answered within two ticks. -/
def latency : Fml Obs :=
  Fml.respondsWithin 2 (.atom Obs.req) (.atom Obs.resp)

-- Semantics.
#guard latency.holds [request, idle, response]
#guard latency.holds [request, idle, idle] == false
#guard latency.holds [request, idle, idle, response]
#guard latency.holds [idle, idle, idle, idle]

-- The synthesised monitor gives the same verdicts.
#guard (synthMonitor latency).verdict [request, idle, response]
#guard (synthMonitor latency).verdict [request, idle, idle] == false
#guard (synthMonitor latency).verdict [request, idle, idle, response]
#guard (synthMonitor latency).verdict [idle, idle, idle, idle]

/-- A response at least every third tick. -/
def alive : Fml Obs := Fml.aliveWithin 2 (.atom Obs.resp)

#guard (synthMonitor alive).verdict [idle, idle]
#guard (synthMonitor alive).verdict [idle, idle, response]
#guard (synthMonitor alive).verdict [idle, idle, idle] == false
#guard (synthMonitor alive).verdict [response, idle, idle, idle] == false

end ContractMonitors
