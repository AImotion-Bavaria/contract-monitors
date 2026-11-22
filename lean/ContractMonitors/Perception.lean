import ContractMonitors.Compositional
import ContractMonitors.Extendable
import ContractMonitors.Temporal

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

/-- An assumption or guarantee with its label. -/
abbrev Clause := String × Fml Sig

def countStep (n : String) : Fml Sig :=
  Fml.stepBounded (stepOn n fun x y => y ≤ x + p.maxStep && x ≤ y + p.maxStep)

def notFrozen (channel : String) : Fml Sig :=
  Fml.aliveWithin p.kFrozen (equals (channel ++ ".changed") 1)

def cloudAlive : Fml Sig := Fml.aliveWithin p.kIn (present "cloud")
def cloudValid : Fml Sig := whenPresent "cloud.points" (fun v => p.minPoints ≤ v)
def detCount : Fml Sig := whenPresent "det.count" (fun v => v ≤ p.maxObjects)
def predSpeed : Fml Sig := whenPresent "pred.maxspeed" (fun v => v ≤ p.maxSpeed)
def detResponse : Fml Sig := Fml.respondsWithin p.kDet (present "cloud") (present "det")
def trkResponse : Fml Sig := Fml.respondsWithin p.kTrk (present "det") (present "trk")
def predResponse : Fml Sig := Fml.respondsWithin p.kPred (present "trk") (present "pred")

/-- What every consumer of the point cloud assumes. -/
def cloudA : List Clause :=
  [ ("input_alive", cloudAlive p),
    ("input_valid", cloudValid p),
    ("input_not_frozen", notFrozen p "cloud") ]

def sysA : List Clause :=
  cloudA p ++ [ ("odd", whenPresent "odd" (fun v => v == 1)) ]

def sysG : List Clause :=
  [ ("response", Fml.respondsWithin p.kSys (present "cloud") (present "pred")),
    ("speed", predSpeed p) ]

def detA : List Clause := cloudA p

def detG : List Clause :=
  [ ("response", detResponse p),
    ("count", detCount p),
    ("step", countStep p "det.count"),
    ("confidence",
      Fml.notLongerThan p.kConf (presentAnd "det.minconf" (fun v => v < p.minConf))),
    ("not_frozen", notFrozen p "det"),
    ("provenance", Fml.backedBy p.kProv (present "det") (present "cloud")) ]

/-- The assumptions of tracking repeat guarantees of detection, except for
liveliness of its input, which follows from liveliness of the point cloud
and the response of detection. -/
def trkA : List Clause :=
  [ ("input_alive", Fml.aliveWithin (p.kIn + p.kDet) (present "det")),
    ("input_count", detCount p),
    ("input_step", countStep p "det.count"),
    ("input_not_frozen", notFrozen p "det") ]

def trkG : List Clause :=
  [ ("response", trkResponse p),
    ("step", countStep p "trk.count"),
    ("not_frozen", notFrozen p "trk"),
    ("provenance", Fml.backedBy p.kProv (present "trk") (present "det")) ]

def predA : List Clause :=
  [ ("input_alive", Fml.aliveWithin (p.kIn + p.kDet + p.kTrk) (present "trk")),
    ("input_step", countStep p "trk.count"),
    ("input_not_frozen", notFrozen p "trk") ]

def predG : List Clause :=
  [ ("response", predResponse p),
    ("speed", predSpeed p),
    ("not_frozen", notFrozen p "pred"),
    ("provenance", Fml.backedBy p.kProv (present "pred") (present "trk")) ]

/-- Name the clauses of one party. -/
def tag (component role : String) (l : List Clause) : List Spec :=
  l.map fun c => ⟨component ++ "." ++ role ++ "." ++ c.1, component, role, c.2⟩

/-- All monitored assumptions and guarantees. The executable `monitor` runs
one synthesised monitor per entry. -/
def specs : List Spec :=
  tag "system" "A" (sysA p) ++ tag "system" "G" (sysG p) ++
  tag "det" "A" (detA p) ++ tag "det" "G" (detG p) ++
  tag "trk" "A" (trkA p) ++ tag "trk" "G" (trkG p) ++
  tag "pred" "A" (predA p) ++ tag "pred" "G" (predG p)

/-! ## The contracts and their refinement -/

/-- All formulas of a list hold. -/
def allHold (l : List Clause) : Prefix Sig → Bool :=
  fun pre => l.all fun c => c.2.holds pre

/-- The monitorable contract with the given assumptions and guarantees. -/
def mk (a g : List Clause) : PContract Sig := ⟨allHold a, allHold g⟩

/-- The contract of the perception system. -/
def system : PContract Sig := mk (sysA p) (sysG p)

/-- The components of the perception system. -/
inductive Comp where
  | det | trk | pred

/-- The contracts of the components. -/
def component : Comp → PContract Sig
  | .det => mk (detA p) (detG p)
  | .trk => mk (trkA p) (trkG p)
  | .pred => mk (predA p) (predG p)

end

theorem always_allHold (l : List Clause) (tr : Trace Sig) :
    Always (allHold l) tr ↔ ∀ c ∈ l, Always c.2.holds tr := by
  unfold Always allHold
  simp only [List.all_eq_true]
  exact ⟨fun h c hc n => h n c hc, fun h n c hc => h c hc n⟩

open Contract in
/-- If the system assumption holds and every component keeps its saturated
guarantee, then every component assumption and every component guarantee
holds. The argument follows the chain: detection is assumed to receive
what the system is assumed to receive, and each further component is
assumed to receive what its predecessor guarantees. -/
theorem chain (p : Params) (tr : Trace Sig)
    (hA : Always (system p).A tr)
    (hG : ∀ i, (component p i).toContract.Gs tr) :
    (∀ i, Always (component p i).A tr) ∧ (∀ i, Always (component p i).G tr) := by
  have sA := (always_allHold _ tr).1 hA
  -- detection
  have dA : Always (component p .det).A tr :=
    (always_allHold _ tr).2 fun c hc => sA c (by simp [sysA, detA] at *; exact Or.inl hc)
  have dG := (always_allHold _ tr).1 (hG .det dA)
  have cloud_alive : Always (cloudAlive p).holds tr :=
    sA ("input_alive", cloudAlive p) (by simp [sysA, cloudA])
  have det_resp : Always (detResponse p).holds tr :=
    dG ("response", detResponse p) (by simp [detG])
  have det_alive := Fml.aliveWithin_chain cloud_alive det_resp
  -- tracking
  have tA : Always (component p .trk).A tr := by
    refine (always_allHold _ tr).2 fun c hc => ?_
    simp only [trkA, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact det_alive
    · exact dG ("count", detCount p) (by simp [detG])
    · exact dG ("step", countStep p "det.count") (by simp [detG])
    · exact dG ("not_frozen", notFrozen p "det") (by simp [detG])
  have tG := (always_allHold _ tr).1 (hG .trk tA)
  have trk_resp : Always (trkResponse p).holds tr :=
    tG ("response", trkResponse p) (by simp [trkG])
  have trk_alive := Fml.aliveWithin_chain det_alive trk_resp
  -- prediction
  have pA : Always (component p .pred).A tr := by
    refine (always_allHold _ tr).2 fun c hc => ?_
    simp only [predA, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact trk_alive
    · exact tG ("step", countStep p "trk.count") (by simp [trkG])
    · exact tG ("not_frozen", notFrozen p "trk") (by simp [trkG])
  exact ⟨fun i => by cases i <;> assumption,
    fun i => by cases i <;> first | exact hG .det dA | exact hG .trk tA | exact hG .pred pA⟩

open Contract in
/-- **The component contracts refine the system contract.** This is the
design-time premise of the theorems on refinement-preserving monitoring,
proved for the contracts that the executable monitors. It holds for all
values of the bounds. -/
theorem refines (p : Params) :
    Contract.compFamily (fun i => (component p i).toContract) ≼ (system p).toContract := by
  refine ⟨fun tr hA => ?_, fun tr hA hG => ?_⟩
  · by_cases hg : ∀ i, (component p i).toContract.Gs tr
    · exact Or.inl (chain p tr hA hg).1
    · exact Or.inr hg
  · have h := (chain p tr hA hG).2
    have dG := (always_allHold _ tr).1 (h .det)
    have tG := (always_allHold _ tr).1 (h .trk)
    have pG := (always_allHold _ tr).1 (h .pred)
    have r₁ : Always (detResponse p).holds tr := dG ("response", detResponse p) (by simp [detG])
    have r₂ : Always (trkResponse p).holds tr := tG ("response", trkResponse p) (by simp [trkG])
    have r₃ : Always (predResponse p).holds tr := pG ("response", predResponse p) (by simp [predG])
    refine (always_allHold _ tr).2 fun c hc => ?_
    simp only [sysG, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact Fml.respondsWithin_chain (Fml.respondsWithin_chain r₁ r₂) r₃
    · exact pG ("speed", predSpeed p) (by simp [predG])

/-- **System guarantee from silent component monitors.** For the perception
contracts: if the synthesised monitors of the component guarantees never
raise an alarm and the system assumption holds, the system guarantee holds.
No monitor of the system guarantee is needed. -/
theorem system_guarantee_of_silent_monitors (p : Params) (Ms : Comp → Monitor Sig)
    (hM : ∀ i, (Ms i).Correct (component p i).G)
    (tr : Trace Sig)
    (h : ∀ i n, (Ms i).verdict (tr.take n) = true)
    (hA : Always (system p).A tr) :
    Always (system p).G tr :=
  system_guarantee_of_no_alarm_family (refines p) hM tr h hA

/-! ## Extendability

The side condition of the prefix version. It holds because there is a
*safe observation*: a valuation after which every clause of the system
assumption and of the component guarantees is true, whatever was observed
before. In the safe observation a message arrives on every channel, differs
from its predecessor, and carries no content that a bound could reject. -/

/-- The safe observation. -/
def safe : Sig :=
  [("cloud", 1), ("cloud.changed", 1), ("det", 1), ("det.changed", 1),
   ("trk", 1), ("trk.changed", 1), ("pred", 1), ("pred.changed", 1)]

theorem impl_of_right {φ ψ : Fml Sig} {x : Sig} {l : List Sig}
    (h : ψ.holdsRev (x :: l) = true) : (Fml.impl φ ψ).holdsRev (x :: l) = true := by
  simp [Fml.impl, Fml.holdsRev, h]

theorem within_of_now {φ : Fml Sig} (k : Nat) {x : Sig} {l : List Sig}
    (h : φ.holdsRev (x :: l) = true) : (Fml.onceWithin k φ).holdsRev (x :: l) = true := by
  cases k <;> simp [Fml.holdsRev, withinSpec, h]

theorem alive_safe (k : Nat) {φ : Fml Sig} {x : Sig} {l : List Sig}
    (h : φ.holdsRev (x :: l) = true) : (Fml.aliveWithin k φ).holdsRev (x :: l) = true :=
  impl_of_right (within_of_now k h)

theorem responds_safe (k : Nat) (req : Fml Sig) {φ : Fml Sig} {x : Sig} {l : List Sig}
    (h : φ.holdsRev (x :: l) = true) :
    (Fml.respondsWithin k req φ).holdsRev (x :: l) = true :=
  impl_of_right (within_of_now k h)

theorem backed_safe (k : Nat) (out : Fml Sig) {φ : Fml Sig} {x : Sig} {l : List Sig}
    (h : φ.holdsRev (x :: l) = true) : (Fml.backedBy k out φ).holdsRev (x :: l) = true :=
  impl_of_right (within_of_now k h)

/-- A step bound on a signal holds when the signal is absent now. -/
theorem step_safe (n : String) (q : Int → Int → Bool) (x : Sig) (l : List Sig)
    (h : val n x = none) :
    (Fml.stepBounded (stepOn n q)).holdsRev (x :: l) = true := by
  cases l with
  | nil => simp [Fml.stepBounded, Fml.impl, Fml.holdsRev, Fml.tt]
  | cons y l =>
    apply impl_of_right
    simp [Fml.step, Fml.holdsRev, lagSpec, stepOn, h]

/-- A bound on the duration of `bad` holds when `bad` is false now. -/
theorem notLonger_safe (k : Nat) (bad : Fml Sig) (x : Sig) (l : List Sig)
    (h : bad.holdsRev (x :: l) = false) :
    (Fml.notLongerThan k bad).holdsRev (x :: l) = true := by
  have : (Fml.onceWithin k (Fml.neg bad)).holdsRev (x :: l) = true :=
    within_of_now k (by simp [Fml.holdsRev, h])
  show (!((Fml.prevN k Fml.tt).holdsRev (x :: l) &&
    !(Fml.onceWithin k (Fml.neg bad)).holdsRev (x :: l))) = true
  rw [this]; simp

/-- Every clause of the system assumption and of the component guarantees
holds whenever the safe observation is the most recent one. -/
theorem safe_holds (p : Params) (l : List Sig) (c : Clause)
    (hc : c ∈ sysA p ++ detG p ++ trkG p ++ predG p) :
    c.2.holdsRev (safe :: l) = true := by
  simp only [sysA, cloudA, detG, trkG, predG, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hc
  rcases hc with ((((rfl | rfl | rfl) | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)
  -- system assumption
  · exact alive_safe _ rfl
  · rfl
  · exact alive_safe _ rfl
  · rfl
  -- detection
  · exact responds_safe _ _ rfl
  · rfl
  · exact step_safe _ _ _ _ rfl
  · exact notLonger_safe _ _ _ _ rfl
  · exact alive_safe _ rfl
  · exact backed_safe _ _ rfl
  -- tracking
  · exact responds_safe _ _ rfl
  · exact step_safe _ _ _ _ rfl
  · exact alive_safe _ rfl
  · exact backed_safe _ _ rfl
  -- prediction
  · exact responds_safe _ _ rfl
  · rfl
  · exact alive_safe _ rfl
  · exact backed_safe _ _ rfl

theorem allHold_snoc_safe (p : Params) (w : Prefix Sig) (l : List Clause)
    (hl : ∀ c ∈ l, c ∈ sysA p ++ detG p ++ trkG p ++ predG p) :
    allHold l (w ++ [safe]) = true := by
  unfold allHold
  rw [List.all_eq_true]
  intro c hc
  simp [Fml.holds, safe_holds p w.reverse c (hl c hc)]

/-- **The perception contracts are extendable.** -/
theorem extendable (p : Params) :
    Extendable (fun w => (system p).A w = true ∧ ∀ i, (component p i).G w = true) := by
  apply extendable_of_noDeadEnd
  intro w _
  refine ⟨safe, allHold_snoc_safe p w _ fun c hc => by simp [hc], fun i => ?_⟩
  cases i <;> exact allHold_snoc_safe p w _ fun c hc => by simp [hc]

/-- **System guarantee on a finite observation.** For the perception
contracts: if the synthesised monitors of the component guarantees have
been silent and the system assumption has held on the observed prefix, the
system guarantee holds on that prefix. -/
theorem system_guarantee_on_prefix (p : Params) (Ms : Comp → Monitor Sig)
    (hM : ∀ i, (Ms i).Correct (component p i).G)
    (w : Prefix Sig)
    (h : ∀ i, HoldsUpTo (Ms i).verdict w)
    (hA : HoldsUpTo (system p).A w) :
    (system p).G w = true :=
  system_guarantee_on_prefix_family (refines p) (extendable p) hM w h hA

end ContractMonitors.Perception
