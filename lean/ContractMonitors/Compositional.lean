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

/-- A prefix predicate is extendable: every prefix on which it has held
throughout is the beginning of a trace on which it holds forever. -/
def Extendable (P : Prefix σ → Bool) : Prop :=
  ∀ pre, HoldsUpTo P pre → ∃ tr : Trace σ, tr.take pre.length = pre ∧ Always P tr

/-- **Refinement-preserving monitoring (T3, prefix version).**

What can be concluded at runtime, after a finite observation: if the
component monitors have been silent and the system assumption has held on
the observed prefix, the system guarantee holds on that prefix. The
conclusion needs the side condition that the conjunction of the system
assumption and the component guarantees is extendable. -/
theorem system_guarantee_on_prefix
    {c c₁ c₂ : PContract σ} {M₁ M₂ : Monitor σ}
    (href : (c₁.toContract ⊗ c₂.toContract) ≼ c.toContract)
    (hext : Extendable (fun p => c.A p && (c₁.G p && c₂.G p)))
    (hM₁ : M₁.Correct c₁.G) (hM₂ : M₂.Correct c₂.G)
    (pre : Prefix σ)
    (h₁ : HoldsUpTo M₁.verdict pre) (h₂ : HoldsUpTo M₂.verdict pre)
    (hA : HoldsUpTo c.A pre) :
    c.G pre = true := by
  have hall : HoldsUpTo (fun p => c.A p && (c₁.G p && c₂.G p)) pre := by
    intro n hn
    have a := hA n hn
    have g₁ := h₁ n hn
    have g₂ := h₂ n hn
    rw [hM₁] at g₁
    rw [hM₂] at g₂
    simp [a, g₁, g₂]
  obtain ⟨tr, htake, halways⟩ := hext pre hall
  have split : ∀ n, c.A (tr.take n) = true ∧ c₁.G (tr.take n) = true ∧
      c₂.G (tr.take n) = true := by
    intro n
    have := halways n
    simpa using this
  have hG : Always c.G tr :=
    href.2 tr (fun n => (split n).1)
      ⟨fun _ n => (split n).2.1, fun _ n => (split n).2.2⟩
  have := hG pre.length
  rwa [htake] at this

/-! ## Blame -/

/-- A component (set of behaviours `K`) satisfies a monitorable contract at
every finite stage: as long as the assumption has held, the guarantee holds. -/
def PContract.PSat (K : Trace σ → Prop) (c : PContract σ) : Prop :=
  ∀ tr, K tr → ∀ n, (∀ m, m ≤ n → c.A (tr.take m) = true) → c.G (tr.take n) = true

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
