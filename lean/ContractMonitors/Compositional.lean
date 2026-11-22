import ContractMonitors.Contract
import ContractMonitors.Monitor

/-!
# Monitoring along the refinement hierarchy

Contracts whose assumption and guarantee are safety properties given by
prefix predicates can be monitored. This file connects design-time
refinement with runtime verdicts.
-/

namespace ContractMonitors

open Contract

/-- A monitorable contract: assumption and guarantee are prefix predicates. -/
structure PContract (σ : Type) where
  A : Prefix σ → Bool
  G : Prefix σ → Bool

variable {σ : Type}

/-- The trace-level contract induced by a monitorable contract. -/
def PContract.toContract (c : PContract σ) : Contract σ where
  A := Always c.A
  G := Always c.G

/-- **Refinement-preserving monitoring (T3, trace version).**

Design time: the composition of the component contracts refines the system
contract. Runtime: correct monitors for the component guarantees never raise
an alarm on the observed trace. Then the system guarantee holds whenever the
system assumption does. No monitor for the system guarantee is needed. -/
theorem system_guarantee_of_no_component_alarm
    {c c₁ c₂ : PContract σ} {M₁ M₂ : Monitor σ}
    (href : (c₁.toContract ⊗ c₂.toContract) ≼ c.toContract)
    (hM₁ : M₁.Correct c₁.G) (hM₂ : M₂.Correct c₂.G)
    (tr : Trace σ)
    (h₁ : ∀ n, M₁.verdict (tr.take n) = true)
    (h₂ : ∀ n, M₂.verdict (tr.take n) = true)
    (hA : Always c.A tr) :
    Always c.G tr := by
  have g₁ : Always c₁.G tr := (hM₁.no_alarm_iff tr).1 h₁
  have g₂ : Always c₂.G tr := (hM₂.no_alarm_iff tr).1 h₂
  exact href.2 tr hA ⟨fun _ => g₁, fun _ => g₂⟩

/-- The same statement for any number of components. -/
theorem system_guarantee_of_no_alarm_family {ι : Type}
    {c : PContract σ} {cs : ι → PContract σ} {Ms : ι → Monitor σ}
    (href : Contract.compFamily (fun i => (cs i).toContract) ≼ c.toContract)
    (hM : ∀ i, (Ms i).Correct (cs i).G)
    (tr : Trace σ)
    (h : ∀ i n, (Ms i).verdict (tr.take n) = true)
    (hA : Always c.A tr) :
    Always c.G tr :=
  href.2 tr hA fun i _ => ((hM i).no_alarm_iff tr).1 (h i)

/-- A prefix predicate is extendable: every prefix on which it has held
throughout is the beginning of a trace on which it holds forever. -/
def Extendable (P : Prefix σ → Prop) : Prop :=
  ∀ pre, (∀ n, n ≤ pre.length → P (pre.take n)) →
    ∃ tr : Trace σ, tr.take pre.length = pre ∧ ∀ n, P (tr.take n)

/-- **Refinement-preserving monitoring (T3, prefix version).**

What can be concluded at runtime, after a finite observation: if the
component monitors have been silent and the system assumption has held on
the observed prefix, the system guarantee holds on that prefix. The
conclusion needs the side condition that the conjunction of the system
assumption and the component guarantees is extendable. -/
theorem system_guarantee_on_prefix_family {ι : Type}
    {c : PContract σ} {cs : ι → PContract σ} {Ms : ι → Monitor σ}
    (href : Contract.compFamily (fun i => (cs i).toContract) ≼ c.toContract)
    (hext : Extendable (fun p => c.A p = true ∧ ∀ i, (cs i).G p = true))
    (hM : ∀ i, (Ms i).Correct (cs i).G)
    (pre : Prefix σ)
    (h : ∀ i, HoldsUpTo (Ms i).verdict pre)
    (hA : HoldsUpTo c.A pre) :
    c.G pre = true := by
  obtain ⟨tr, htake, hall⟩ := hext pre fun n hn =>
    ⟨hA n hn, fun i => by rw [← hM i]; exact h i n hn⟩
  have hG : Always c.G tr :=
    href.2 tr (fun n => (hall n).1) fun i _ n => (hall n).2 i
  have := hG pre.length
  rwa [htake] at this

/-- The prefix version for two components. -/
theorem system_guarantee_on_prefix
    {c c₁ c₂ : PContract σ} {M₁ M₂ : Monitor σ}
    (href : (c₁.toContract ⊗ c₂.toContract) ≼ c.toContract)
    (hext : Extendable (fun p => c.A p = true ∧ c₁.G p = true ∧ c₂.G p = true))
    (hM₁ : M₁.Correct c₁.G) (hM₂ : M₂.Correct c₂.G)
    (pre : Prefix σ)
    (h₁ : HoldsUpTo M₁.verdict pre) (h₂ : HoldsUpTo M₂.verdict pre)
    (hA : HoldsUpTo c.A pre) :
    c.G pre = true := by
  obtain ⟨tr, htake, hall⟩ := hext pre fun n hn =>
    ⟨hA n hn, by rw [← hM₁]; exact h₁ n hn, by rw [← hM₂]; exact h₂ n hn⟩
  have hG : Always c.G tr :=
    href.2 tr (fun n => (hall n).1)
      ⟨fun _ n => (hall n).2.1, fun _ n => (hall n).2.2⟩
  have := hG pre.length
  rwa [htake] at this

/-! ## Extendability cannot be dropped -/

namespace Counterexample

/-- System contract: no assumption; the guarantee holds for the empty
prefix only. -/
def sys : PContract Unit := ⟨fun _ => true, fun p => p.isEmpty⟩

/-- Component 1: its guarantee holds for prefixes of length at most one and
can therefore not be kept forever. -/
def comp₁ : PContract Unit := ⟨fun _ => true, fun p => decide (p.length ≤ 1)⟩

/-- Component 2: trivial. -/
def comp₂ : PContract Unit := ⟨fun _ => true, fun _ => true⟩

/-- The refinement holds, but only vacuously: no trace satisfies the
guarantee of component 1 forever. -/
theorem refines : (comp₁.toContract ⊗ comp₂.toContract) ≼ sys.toContract := by
  refine ⟨fun tr _ => Or.inl ⟨fun _ => rfl, fun _ => rfl⟩, fun tr _ hG => ?_⟩
  have h := hG.1 (fun _ => rfl) 2
  simp [comp₁] at h

/-- **Extendability is necessary.** All hypotheses of
`system_guarantee_on_prefix` except extendability hold for the prefix of
length one, yet the system guarantee is violated on it. -/
theorem extendability_needed :
    (comp₁.toContract ⊗ comp₂.toContract) ≼ sys.toContract ∧
    HoldsUpTo comp₁.G [()] ∧ HoldsUpTo comp₂.G [()] ∧ HoldsUpTo sys.A [()] ∧
    sys.G [()] = false := by
  refine ⟨refines, ?_, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  intro n hn
  have : n = 0 ∨ n = 1 := by simp at hn; omega
  rcases this with rfl | rfl <;> rfl

end Counterexample

/-! ## Blame -/

/-- A component (set of behaviours `K`) satisfies a monitorable contract at
every finite stage: as long as the assumption has held, the guarantee holds. -/
def PContract.PSat (K : Trace σ → Prop) (c : PContract σ) : Prop :=
  ∀ tr, K tr → ∀ n, (∀ m, m ≤ n → c.A (tr.take m) = true) → c.G (tr.take n) = true

/-- Stagewise satisfaction implies satisfaction of the induced contract. -/
theorem PContract.PSat.sat {K : Trace σ → Prop} {c : PContract σ} (h : c.PSat K) :
    Contract.Sat K c.toContract :=
  fun tr hk hA n => h tr hk n fun m _ => hA m

/-- **No false blame (T4).** For a component that satisfies its contract,
the guarantee monitor stays silent as long as the assumption monitor has
been silent. -/
theorem no_false_blame {K : Trace σ → Prop} {c : PContract σ} {MA MG : Monitor σ}
    (hK : c.PSat K) (hMA : MA.Correct c.A) (hMG : MG.Correct c.G)
    (tr : Trace σ) (htr : K tr) (n : Nat)
    (hA : ∀ m, m ≤ n → MA.verdict (tr.take m) = true) :
    MG.verdict (tr.take n) = true := by
  rw [hMG]
  exact hK tr htr n (fun m hm => by rw [← hMA]; exact hA m hm)

/-- **Blame is justified (T4).** An alarm of the guarantee monitor while the
assumption monitor has been silent shows that the component violates its
contract. -/
theorem component_at_fault {K : Trace σ → Prop} {c : PContract σ} {MA MG : Monitor σ}
    (hMA : MA.Correct c.A) (hMG : MG.Correct c.G)
    (tr : Trace σ) (htr : K tr) (n : Nat)
    (hA : ∀ m, m ≤ n → MA.verdict (tr.take m) = true)
    (hG : MG.verdict (tr.take n) = false) :
    ¬ c.PSat K := by
  intro hK
  have := no_false_blame hK hMA hMG tr htr n hA
  rw [hG] at this
  exact Bool.noConfusion this

end ContractMonitors
