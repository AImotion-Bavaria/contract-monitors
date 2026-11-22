import ContractMonitors.Patterns

/-!
# Reasoning about patterns on traces

To prove that concrete contracts refine each other, the patterns are
characterised by statements about the positions of a trace. `φ.at tr t`
states that `φ` holds at tick `t` of `tr` (ticks are counted from zero).

The characterisations lead to two chaining rules: response windows add up
along a chain of components, and so do liveliness and response.
-/

namespace ContractMonitors

variable {σ : Type}

/-- The history of a trace up to and including tick `t`, newest first. -/
def Trace.hist (tr : Trace σ) : Nat → List σ
  | 0 => [tr 0]
  | t + 1 => tr (t + 1) :: Trace.hist tr t

theorem Trace.hist_eq (tr : Trace σ) (t : Nat) :
    tr.hist t = (tr.take (t + 1)).reverse := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show tr (t + 1) :: tr.hist t = _
    rw [ih]
    simp [Trace.take, List.range_succ]

theorem Trace.hist_drop (tr : Trace σ) (t i : Nat) (h : i ≤ t) :
    (tr.hist t).drop i = tr.hist (t - i) := by
  induction i generalizing t with
  | zero => rfl
  | succ i ih =>
    cases t with
    | zero => omega
    | succ t =>
      show (tr.hist t).drop i = _
      rw [ih t (by omega)]
      congr 1
      omega

namespace Fml

/-- `φ` holds at tick `t` of the trace. -/
def «at» (φ : Fml σ) (tr : Trace σ) (t : Nat) : Prop :=
  φ.holdsRev (tr.hist t) = true

/-- A formula holds throughout a trace iff it holds at every tick. -/
theorem always_iff (φ : Fml σ) (tr : Trace σ) :
    Always φ.holds tr ↔ ∀ t, φ.at tr t := by
  constructor
  · intro h t
    have := h (t + 1)
    unfold Fml.holds at this
    rw [← Trace.hist_eq] at this
    have hne : (tr.take (t + 1)).isEmpty = false := by
      simp [Trace.take, List.range_succ]
    simpa [hne, Fml.at] using this
  · intro h n
    cases n with
    | zero => rfl
    | succ t =>
      unfold Fml.holds
      rw [← Trace.hist_eq]
      have := h t
      unfold Fml.at at this
      simp [this]

theorem holdsRev_nil (φ : Fml σ) : φ.holdsRev [] = false := by
  induction φ with
  | conj φ ψ ih _ => simp [holdsRev, ih]
  | onceWithin k φ _ => cases k <;> rfl
  | _ => rfl

theorem at_tt (tr : Trace σ) (t : Nat) : (tt : Fml σ).at tr t := by
  cases t <;> rfl

theorem at_impl (φ ψ : Fml σ) (tr : Trace σ) (t : Nat) :
    (impl φ ψ).at tr t ↔ (φ.at tr t → ψ.at tr t) := by
  unfold Fml.at impl
  cases t <;> simp [Trace.hist, holdsRev] <;>
    cases φ.holdsRev _ <;> simp

theorem at_prevN (k : Nat) (φ : Fml σ) (tr : Trace σ) (t : Nat) :
    (prevN k φ).at tr t ↔ k ≤ t ∧ φ.at tr (t - k) := by
  induction k generalizing t with
  | zero => simp [prevN]
  | succ k ih =>
    cases t with
    | zero =>
      simp [Fml.at, prevN, Trace.hist, holdsRev, holdsRev_nil]
    | succ t =>
      have : (prevN (k + 1) φ).at tr (t + 1) ↔ (prevN k φ).at tr t := by
        simp [Fml.at, prevN, Trace.hist, holdsRev]
      rw [this, ih t]
      have e : t + 1 - (k + 1) = t - k := by omega
      rw [e]
      constructor
      · intro ⟨a, b⟩; exact ⟨by omega, b⟩
      · intro ⟨a, b⟩; exact ⟨by omega, b⟩

theorem withinSpec_hist (f : List σ → Bool) (k : Nat) (tr : Trace σ) (t : Nat) :
    withinSpec f k (tr.hist t) = true ↔ ∃ i, i ≤ k ∧ i ≤ t ∧ f (tr.hist (t - i)) = true := by
  induction k generalizing t with
  | zero =>
    cases t <;> simp [Trace.hist, withinSpec]
  | succ k ih =>
    cases t with
    | zero =>
      simp only [Trace.hist, withinSpec, Bool.or_eq_true]
      constructor
      · intro h
        cases h with
        | inl h => exact ⟨0, by omega, by omega, h⟩
        | inr h => cases k <;> simp at h
      · intro ⟨i, _, hi, h⟩
        have : i = 0 := by omega
        subst this
        exact Or.inl h
    | succ t =>
      simp only [Trace.hist, withinSpec, Bool.or_eq_true]
      rw [ih t]
      constructor
      · intro h
        cases h with
        | inl h => exact ⟨0, by omega, by omega, h⟩
        | inr h =>
          obtain ⟨i, h1, h2, h3⟩ := h
          refine ⟨i + 1, by omega, by omega, ?_⟩
          have e : t + 1 - (i + 1) = t - i := by omega
          rw [e]; exact h3
      · intro ⟨i, h1, h2, h3⟩
        cases i with
        | zero => exact Or.inl h3
        | succ i =>
          refine Or.inr ⟨i, by omega, by omega, ?_⟩
          have e : t + 1 - (i + 1) = t - i := by omega
          rw [e] at h3; exact h3

theorem at_onceWithin (k : Nat) (φ : Fml σ) (tr : Trace σ) (t : Nat) :
    (Fml.onceWithin k φ).at tr t ↔ ∃ i, i ≤ k ∧ i ≤ t ∧ φ.at tr (t - i) :=
  withinSpec_hist φ.holdsRev k tr t

/-- **Response on traces.** Every request is followed by a response at most
`k` ticks later. -/
theorem always_respondsWithin (k : Nat) (req resp : Fml σ) (tr : Trace σ) :
    Always (respondsWithin k req resp).holds tr ↔
      ∀ s, req.at tr s → ∃ d, d ≤ k ∧ resp.at tr (s + d) := by
  rw [always_iff]
  constructor
  · intro h s hs
    have := (at_impl _ _ tr (s + k)).1 (h (s + k))
      ((at_prevN k req tr (s + k)).2 ⟨by omega, by simpa using hs⟩)
    obtain ⟨i, h1, _, h3⟩ := (at_onceWithin k resp tr (s + k)).1 this
    refine ⟨k - i, by omega, ?_⟩
    have e : s + k - i = s + (k - i) := by omega
    rw [e] at h3; exact h3
  · intro h t
    refine (at_impl _ _ tr t).2 fun hp => ?_
    obtain ⟨hk, hreq⟩ := (at_prevN k req tr t).1 hp
    obtain ⟨d, hd, hresp⟩ := h (t - k) hreq
    refine (at_onceWithin k resp tr t).2 ⟨k - d, by omega, by omega, ?_⟩
    have e : t - (k - d) = t - k + d := by omega
    rw [e]; exact hresp

/-- **Liveliness on traces.** From every tick on, `φ` holds at most `k`
ticks later. -/
theorem always_aliveWithin (k : Nat) (φ : Fml σ) (tr : Trace σ) :
    Always (aliveWithin k φ).holds tr ↔ ∀ s, ∃ d, d ≤ k ∧ φ.at tr (s + d) := by
  rw [always_iff]
  constructor
  · intro h s
    have := (at_impl _ _ tr (s + k)).1 (h (s + k))
      ((at_prevN k tt tr (s + k)).2 ⟨by omega, at_tt tr _⟩)
    obtain ⟨i, h1, _, h3⟩ := (at_onceWithin k φ tr (s + k)).1 this
    refine ⟨k - i, by omega, ?_⟩
    have e : s + k - i = s + (k - i) := by omega
    rw [e] at h3; exact h3
  · intro h t
    refine (at_impl _ _ tr t).2 fun hp => ?_
    obtain ⟨hk, _⟩ := (at_prevN k tt tr t).1 hp
    obtain ⟨d, hd, hφ⟩ := h (t - k)
    refine (at_onceWithin k φ tr t).2 ⟨k - d, by omega, by omega, ?_⟩
    have e : t - (k - d) = t - k + d := by omega
    rw [e]; exact hφ

/-- **Response windows add up.** -/
theorem respondsWithin_chain {j k : Nat} {a b c : Fml σ} {tr : Trace σ}
    (h₁ : Always (respondsWithin j a b).holds tr)
    (h₂ : Always (respondsWithin k b c).holds tr) :
    Always (respondsWithin (j + k) a c).holds tr := by
  rw [always_respondsWithin] at *
  intro s hs
  obtain ⟨d, hd, hb⟩ := h₁ s hs
  obtain ⟨e, he, hc⟩ := h₂ (s + d) hb
  exact ⟨d + e, by omega, by rw [← Nat.add_assoc]; exact hc⟩

/-- **Liveliness is passed on by a responsive component.** -/
theorem aliveWithin_chain {j k : Nat} {a b : Fml σ} {tr : Trace σ}
    (h₁ : Always (aliveWithin j a).holds tr)
    (h₂ : Always (respondsWithin k a b).holds tr) :
    Always (aliveWithin (j + k) b).holds tr := by
  rw [always_aliveWithin] at *
  rw [always_respondsWithin] at h₂
  intro s
  obtain ⟨d, hd, ha⟩ := h₁ s
  obtain ⟨e, he, hb⟩ := h₂ (s + d) ha
  exact ⟨d + e, by omega, by rw [← Nat.add_assoc]; exact hb⟩

end Fml

end ContractMonitors
