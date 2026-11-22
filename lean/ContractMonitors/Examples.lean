import ContractMonitors.Patterns

/-!
# Examples

The contract patterns instantiated for a toy perception stage, with
executable checks (`#guard`) that the synthesised monitor gives the expected
verdicts on sample prefixes.
-/

namespace ContractMonitors

/-- Observation of a perception stage in one tick. -/
structure Obs where
  /-- An input (e.g. a point cloud) arrived. -/
  inp : Bool := false
  /-- An output (e.g. an object list) was published. -/
  out : Bool := false
  /-- Number of objects in the output. -/
  count : Nat := 0
  /-- Lowest confidence in the output, in percent. -/
  conf : Nat := 100

def idle : Obs := {}
def input : Obs := { inp := true }
def output (count : Nat := 1) (conf : Nat := 100) : Obs :=
  { out := true, count := count, conf := conf }

def verdict (φ : Fml Obs) (pre : List Obs) : Bool := (synthMonitor φ).verdict pre

/-- Response: inputs are answered within two ticks. -/
def latency : Fml Obs := Fml.respondsWithin 2 (.atom (·.inp)) (.atom (·.out))

#guard verdict latency [input, idle, output]
#guard verdict latency [input, idle, idle] == false
#guard verdict latency [input, idle, idle, output]
#guard verdict latency [idle, idle, idle, idle]
#guard latency.holds [input, idle, idle] == false

/-- Liveliness: an output at least every third tick. -/
def alive : Fml Obs := Fml.aliveWithin 2 (.atom (·.out))

#guard verdict alive [idle, idle]
#guard verdict alive [idle, idle, output]
#guard verdict alive [idle, idle, idle] == false
#guard verdict alive [output, idle, idle, idle] == false

/-- Invariant: at most 200 objects. -/
def range : Fml Obs := Fml.invariant (·.count ≤ 200)

#guard verdict range [output 3, output 200]
#guard verdict range [output 3, output 201] == false

/-- Bounded duration: confidence is not below 50 % for more than two
consecutive ticks. -/
def confidence : Fml Obs := Fml.notLongerThan 2 (.atom (·.conf < 50))

#guard verdict confidence [output 1 40, output 1 40]
#guard verdict confidence [output 1 40, output 1 40, output 1 40] == false
#guard verdict confidence [output 1 40, output 1 40, output 1 90, output 1 40]

/-- Bounded step: the object count changes by at most two per tick. -/
def consistency : Fml Obs :=
  Fml.stepBounded fun a b => b.count ≤ a.count + 2 && a.count ≤ b.count + 2

#guard verdict consistency [output 5]
#guard verdict consistency [output 5, output 7, output 6]
#guard verdict consistency [output 5, output 9] == false

/-- Bounded duration over a step atom: the output is not frozen for more
than two consecutive ticks. -/
def notFrozen : Fml Obs :=
  Fml.notLongerThan 2 (.step fun a b => a.count == b.count && a.conf == b.conf)

#guard verdict notFrozen [output 5, output 5, output 5]
#guard verdict notFrozen [output 5, output 5, output 5, output 5] == false
#guard verdict notFrozen [output 5, output 5, output 6, output 6, output 6]

/-- Bounded drift: over three ticks the object count changes by at most
three. -/
def drift : Fml Obs :=
  Fml.driftBounded 3 fun a b => b.count ≤ a.count + 3 && a.count ≤ b.count + 3

#guard verdict drift [output 5, output 6, output 7]
#guard verdict drift [output 5, output 6, output 7, output 8]
#guard verdict drift [output 5, output 6, output 7, output 9] == false

/-- Rate: at least two outputs in every window of four ticks. -/
def rate : Fml Obs := Fml.atLeastWithin 3 2 (.atom (·.out))

#guard verdict rate [output, idle, idle]
#guard verdict rate [output, idle, output, idle]
#guard verdict rate [output, idle, idle, idle] == false
#guard verdict rate [output, idle, output, idle, idle, idle] == false

/-- Bounded rate: at most two outputs in every window of three ticks. -/
def burst : Fml Obs := Fml.atMostWithin 2 2 (.atom (·.out))

#guard verdict burst [output, output, idle, output]
#guard verdict burst [output, output, output] == false

/-- Provenance: an output is backed by an input within the last two ticks. -/
def provenance : Fml Obs := Fml.backedBy 2 (.atom (·.out)) (.atom (·.inp))

#guard verdict provenance [input, idle, output]
#guard verdict provenance [input, idle, idle, output] == false

end ContractMonitors
