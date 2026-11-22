import ContractMonitors.Patterns

/-!
# Contracts of the perception pipeline

The running example: a perception system with the components detection,
tracking, and prediction. Observations are valuations of named integer
signals; a signal without a value in a tick is absent.

Signals (set by the adapter):
* events, present only in the tick a message arrives:
  `cloud`, `det`, `trk`, `pred`, and `<channel>.changed` (1 if the message
  differs from the previous one on the channel, else 0);
* latched values, holding the content of the most recent message:
  `cloud.points`, `det.count`, `det.minconf`, `trk.count`, `pred.count`,
  `pred.maxspeed`, `odd`.

All bounds are parameters; windows are given in ticks.
-/

namespace ContractMonitors.Perception

/-- The signals that carry a value in a tick. -/
abbrev Sig := List (String × Int)

/-- The value of a signal, if present. -/
def val (n : String) (o : Sig) : Option Int := o.lookup n

/-- The signal carries a value. -/
def present (n : String) : Fml Sig := .atom fun o => (val n o).isSome

/-- The signal carries the value `v`. -/
def equals (n : String) (v : Int) : Fml Sig := .atom fun o => val n o == some v

/-- If the signal carries a value, the value satisfies `p`. -/
def whenPresent (n : String) (p : Int → Bool) : Fml Sig :=
  .atom fun o => match val n o with
    | some v => p v
    | none => true

/-- The signal carries a value that satisfies `p`. -/
def presentAnd (n : String) (p : Int → Bool) : Fml Sig :=
  .atom fun o => match val n o with
    | some v => p v
    | none => false

/-- If the signal carries a value in two consecutive ticks, the values are
related by `q`. -/
def stepOn (n : String) (q : Int → Int → Bool) : Sig → Sig → Bool :=
  fun a b => match val n a, val n b with
    | some x, some y => q x y
    | _, _ => true

/-- Bounds of the contracts. Windows are in ticks. -/
structure Params where
  /-- A point cloud arrives at least every `kIn + 1` ticks. -/
  kIn : Nat := 12
  /-- Response windows of the components. -/
  kDet : Nat := 5
  kTrk : Nat := 4
  kPred : Nat := 4
  /-- Low confidence lasts at most `kConf` ticks. -/
  kConf : Nat := 30
  /-- A channel carries a changed message at least every `kFrozen + 1` ticks. -/
  kFrozen : Nat := 35
  /-- An output is backed by an input within the last `kProv` ticks. -/
  kProv : Nat := 10
  minPoints : Int := 1000
  maxObjects : Int := 100
  /-- Largest change of an object count between consecutive ticks. -/
  maxStep : Int := 3
  /-- Lowest acceptable confidence, per mille. -/
  minConf : Int := 300
  /-- Largest plausible speed, in mm/s. -/
  maxSpeed : Int := 60000

/-- Response window of the system: the sum of the component windows. -/
def Params.kSys (p : Params) : Nat := p.kDet + p.kTrk + p.kPred

/-- A named assumption or guarantee of one party. -/
structure Spec where
  name : String
  /-- `system`, `det`, `trk`, or `pred`. -/
  component : String
  /-- `A` or `G`. -/
  role : String
  fml : Fml Sig

section
variable (p : Params)

def countStep (n : String) : Fml Sig :=
  Fml.stepBounded (stepOn n fun x y => y ≤ x + p.maxStep && x ≤ y + p.maxStep)

def notFrozen (channel : String) : Fml Sig :=
  Fml.aliveWithin p.kFrozen (equals (channel ++ ".changed") 1)

/-- What every consumer of the point cloud assumes. -/
def cloudAssumptions (component : String) : List Spec :=
  [ ⟨component ++ ".A.input_alive", component, "A", Fml.aliveWithin p.kIn (present "cloud")⟩,
    ⟨component ++ ".A.input_valid", component, "A",
      whenPresent "cloud.points" (fun v => p.minPoints ≤ v)⟩,
    ⟨component ++ ".A.input_not_frozen", component, "A", notFrozen p "cloud"⟩ ]

/-- Contracts of the system and its three components. The assumption of a
component repeats the guarantees of its predecessor on the shared channel. -/
def specs : List Spec :=
  -- system
  cloudAssumptions p "system" ++
  [ ⟨"system.A.odd", "system", "A", whenPresent "odd" (fun v => v == 1)⟩,
    ⟨"system.G.response", "system", "G",
      Fml.respondsWithin p.kSys (present "cloud") (present "pred")⟩,
    ⟨"system.G.speed", "system", "G",
      whenPresent "pred.maxspeed" (fun v => v ≤ p.maxSpeed)⟩ ] ++
  -- detection
  cloudAssumptions p "det" ++
  [ ⟨"det.G.response", "det", "G",
      Fml.respondsWithin p.kDet (present "cloud") (present "det")⟩,
    ⟨"det.G.count", "det", "G", whenPresent "det.count" (fun v => v ≤ p.maxObjects)⟩,
    ⟨"det.G.step", "det", "G", countStep p "det.count"⟩,
    ⟨"det.G.confidence", "det", "G",
      Fml.notLongerThan p.kConf (presentAnd "det.minconf" (fun v => v < p.minConf))⟩,
    ⟨"det.G.not_frozen", "det", "G", notFrozen p "det"⟩,
    ⟨"det.G.provenance", "det", "G",
      Fml.backedBy p.kProv (present "det") (present "cloud")⟩ ] ++
  -- tracking
  [ ⟨"trk.A.input_alive", "trk", "A", Fml.aliveWithin (p.kIn + p.kDet) (present "det")⟩,
    ⟨"trk.A.input_count", "trk", "A", whenPresent "det.count" (fun v => v ≤ p.maxObjects)⟩,
    ⟨"trk.A.input_step", "trk", "A", countStep p "det.count"⟩,
    ⟨"trk.A.input_not_frozen", "trk", "A", notFrozen p "det"⟩,
    ⟨"trk.G.response", "trk", "G",
      Fml.respondsWithin p.kTrk (present "det") (present "trk")⟩,
    ⟨"trk.G.step", "trk", "G", countStep p "trk.count"⟩,
    ⟨"trk.G.not_frozen", "trk", "G", notFrozen p "trk"⟩,
    ⟨"trk.G.provenance", "trk", "G",
      Fml.backedBy p.kProv (present "trk") (present "det")⟩ ] ++
  -- prediction
  [ ⟨"pred.A.input_alive", "pred", "A",
      Fml.aliveWithin (p.kIn + p.kDet + p.kTrk) (present "trk")⟩,
    ⟨"pred.A.input_step", "pred", "A", countStep p "trk.count"⟩,
    ⟨"pred.A.input_not_frozen", "pred", "A", notFrozen p "trk"⟩,
    ⟨"pred.G.response", "pred", "G",
      Fml.respondsWithin p.kPred (present "trk") (present "pred")⟩,
    ⟨"pred.G.speed", "pred", "G", whenPresent "pred.maxspeed" (fun v => v ≤ p.maxSpeed)⟩,
    ⟨"pred.G.not_frozen", "pred", "G", notFrozen p "pred"⟩,
    ⟨"pred.G.provenance", "pred", "G",
      Fml.backedBy p.kProv (present "pred") (present "trk")⟩ ]

end

end ContractMonitors.Perception
