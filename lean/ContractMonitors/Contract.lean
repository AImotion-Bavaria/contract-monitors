import ContractMonitors.Basic

/-!
# Assume/guarantee contracts, refinement, composition

Contracts are pairs of trace predicates. Nothing here depends on the level of
the hierarchy (system of systems, system, component): the same definitions
and theorems apply at every level.
-/

namespace ContractMonitors

/-- An assume/guarantee contract over observations `σ`. -/
structure Contract (σ : Type) where
  /-- Assumption on the environment. -/
  A : Trace σ → Prop
  /-- Guarantee of the component, owed when the assumption holds. -/
  G : Trace σ → Prop

variable {σ : Type}

namespace Contract

/-- Saturated guarantee `A ⟹ G`. -/
def Gs (c : Contract σ) : Trace σ → Prop := fun tr => c.A tr → c.G tr

/-- A component (set of behaviours `K`) satisfies a contract. -/
def Sat (K : Trace σ → Prop) (c : Contract σ) : Prop :=
  ∀ tr, K tr → c.A tr → c.G tr

/-- `c'` refines `c`: weaker assumption, and under the abstract assumption a
stronger guarantee. -/
def Refines (c' c : Contract σ) : Prop :=
  (∀ tr, c.A tr → c'.A tr) ∧ (∀ tr, c.A tr → c'.G tr → c.G tr)

@[inherit_doc] scoped infix:50 " ≼ " => Refines

theorem Refines.refl (c : Contract σ) : c ≼ c :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem Refines.trans {c₁ c₂ c₃ : Contract σ} (h₁₂ : c₁ ≼ c₂) (h₂₃ : c₂ ≼ c₃) :
    c₁ ≼ c₃ :=
  ⟨fun tr h => h₁₂.1 tr (h₂₃.1 tr h),
   fun tr hA hG => h₂₃.2 tr hA (h₁₂.2 tr (h₂₃.1 tr hA) hG)⟩

/-- Refinement is sound: every implementation of the refined contract
implements the abstract one. -/
theorem Sat.of_refines {K : Trace σ → Prop} {c' c : Contract σ}
    (h : c' ≼ c) (hK : Sat K c') : Sat K c :=
  fun tr hk hA => h.2 tr hA (hK tr hk (h.1 tr hA))

/-- Parallel composition over a shared observation alphabet. -/
def comp (c₁ c₂ : Contract σ) : Contract σ where
  A := fun tr => (c₁.A tr ∧ c₂.A tr) ∨ ¬ (c₁.Gs tr ∧ c₂.Gs tr)
  G := fun tr => c₁.Gs tr ∧ c₂.Gs tr

@[inherit_doc] scoped infixl:70 " ⊗ " => comp

/-- Composing implementations implements the composed contract. -/
theorem Sat.comp {K₁ K₂ : Trace σ → Prop} {c₁ c₂ : Contract σ}
    (h₁ : Sat K₁ c₁) (h₂ : Sat K₂ c₂) :
    Sat (fun tr => K₁ tr ∧ K₂ tr) (c₁ ⊗ c₂) :=
  fun tr hk _ => ⟨h₁ tr hk.1, h₂ tr hk.2⟩

theorem Gs.of_refines {c' c : Contract σ} (h : c' ≼ c) (tr : Trace σ)
    (hg : c'.Gs tr) : c.Gs tr :=
  fun hA => h.2 tr hA (hg (h.1 tr hA))

/-- Independent implementability: composition is monotone in refinement. -/
theorem comp_mono {c₁ c₁' c₂ c₂' : Contract σ} (h₁ : c₁' ≼ c₁) (h₂ : c₂' ≼ c₂) :
    (c₁' ⊗ c₂') ≼ (c₁ ⊗ c₂) := by
  refine ⟨fun tr hA => ?_, fun tr _ hG => ?_⟩
  · cases hA with
    | inl h => exact Or.inl ⟨h₁.1 tr h.1, h₂.1 tr h.2⟩
    | inr h =>
      exact Or.inr fun hg =>
        h ⟨Gs.of_refines h₁ tr hg.1, Gs.of_refines h₂ tr hg.2⟩
  · exact ⟨Gs.of_refines h₁ tr hG.1, Gs.of_refines h₂ tr hG.2⟩

end Contract

end ContractMonitors
