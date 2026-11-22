import ContractMonitors.Compositional

/-!
# Extendability = absence of dead ends

`Extendable P` quantifies over infinite traces. This file shows that it is
equivalent to a condition on finite prefixes only: whenever `P` has held
throughout a prefix, some next observation keeps it true. For a correct
monitor this is a statement about its alarm-free runs.
-/

namespace ContractMonitors

variable {σ : Type} {P : Prefix σ → Prop}

/-- `P` holds for a prefix and all of its initial segments. -/
def Thru (P : Prefix σ → Prop) (w : Prefix σ) : Prop :=
  ∀ n, n ≤ w.length → P (w.take n)

/-- No dead ends: whenever `P` has held throughout a prefix, there is a next
observation for which it still holds. -/
def NoDeadEnd (P : Prefix σ → Prop) : Prop :=
  ∀ w, Thru P w → ∃ x, P (w ++ [x])

theorem Thru.snoc {w : Prefix σ} {x : σ} (hw : Thru P w) (hx : P (w ++ [x])) :
    Thru P (w ++ [x]) := by
  intro n hn
  by_cases h : n ≤ w.length
  · rw [List.take_append_of_le_length h]; exact hw n h
  · have hlen : n = (w ++ [x]).length := by
      simp at hn ⊢; omega
    rw [hlen, List.take_length]; exact hx

namespace Extend

/-- Extend a good prefix by one chosen observation. -/
noncomputable def step (h : NoDeadEnd P) (w : {w : Prefix σ // Thru P w}) :
    {w : Prefix σ // Thru P w} :=
  ⟨w.1 ++ [Classical.choose (h w.1 w.2)],
    w.2.snoc (Classical.choose_spec (h w.1 w.2))⟩

/-- The chain of good prefixes starting at `w0`. -/
noncomputable def seq (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w}) :
    Nat → {w : Prefix σ // Thru P w}
  | 0 => w0
  | n + 1 => step h (seq h w0 n)

theorem seq_length (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w}) (n : Nat) :
    (seq h w0 n).1.length = w0.1.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [seq, step, ih, Nat.add_assoc]

/-- Earlier members of the chain are initial segments of later ones. -/
theorem seq_take (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w}) (n m : Nat) :
    (seq h w0 (n + m)).1.take (seq h w0 n).1.length = (seq h w0 n).1 := by
  induction m with
  | zero => exact List.take_length
  | succ m ih =>
    show ((seq h w0 (n + m)).1 ++ [_]).take _ = _
    rw [List.take_append_of_le_length (by simp [seq_length])]
    exact ih

/-- The infinite trace that all members of the chain are prefixes of. -/
noncomputable def limit (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w}) : Trace σ :=
  fun k => (seq h w0 (k + 1)).1[k]'(by rw [seq_length]; omega)

theorem seq_getElem? (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w})
    (i n : Nat) (hin : i < n) :
    (seq h w0 n).1[i]? = some (limit h w0 i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = (i + 1) + m := ⟨n - (i + 1), by omega⟩
  have hl : i < (seq h w0 (i + 1)).1.length := by rw [seq_length]; omega
  have key := seq_take h w0 (i + 1) m
  have : (seq h w0 (i + 1)).1[i]? = (seq h w0 (i + 1 + m)).1[i]? := by
    conv => lhs; rw [← key]
    rw [List.getElem?_take]
    simp [hl]
  rw [← this]
  exact List.getElem?_eq_getElem hl

theorem limit_take (h : NoDeadEnd P) (w0 : {w : Prefix σ // Thru P w}) (n : Nat) :
    (limit h w0).take n = (seq h w0 n).1.take n := by
  apply List.ext_getElem?
  intro i
  by_cases hin : i < n
  · simp [Trace.take, hin, seq_getElem? h w0 i n hin]
  · simp [Trace.take, hin]
    have := seq_length h w0 n
    omega

end Extend

/-- Absence of dead ends suffices for extendability. -/
theorem extendable_of_noDeadEnd (h : NoDeadEnd P) : Extendable P := by
  intro pre hpre
  refine ⟨Extend.limit h ⟨pre, hpre⟩, ?_, fun n => ?_⟩
  · rw [Extend.limit_take]
    have := Extend.seq_take h ⟨pre, hpre⟩ 0 pre.length
    simpa [Extend.seq] using this
  · rw [Extend.limit_take]
    exact (Extend.seq h ⟨pre, hpre⟩ n).2 n (by rw [Extend.seq_length]; omega)

/-- Extendability rules out dead ends. -/
theorem noDeadEnd_of_extendable (h : Extendable P) : NoDeadEnd P := by
  intro w hw
  obtain ⟨tr, htake, hall⟩ := h w hw
  refine ⟨tr w.length, ?_⟩
  have hsucc : tr.take (w.length + 1) = tr.take w.length ++ [tr w.length] := by
    simp [Trace.take, List.range_succ]
  have := hall (w.length + 1)
  rwa [hsucc, htake] at this

/-- **Extendability is the absence of dead ends.** -/
theorem extendable_iff_noDeadEnd : Extendable P ↔ NoDeadEnd P :=
  ⟨noDeadEnd_of_extendable, extendable_of_noDeadEnd⟩

/-- **Checking extendability on a monitor.** If, after every alarm-free run
of a correct monitor, some observation leads to a non-alarm verdict, the
monitored predicate is extendable. -/
theorem Monitor.Correct.extendable {M : Monitor σ} {Q : Prefix σ → Bool}
    (h : M.Correct Q)
    (hdead : ∀ w, HoldsUpTo M.verdict w → ∃ x, M.verdict (w ++ [x]) = true) :
    Extendable (fun p => Q p = true) := by
  apply extendable_of_noDeadEnd
  intro w hw
  obtain ⟨x, hx⟩ := hdead w (fun n hn => by rw [h]; exact hw n hn)
  exact ⟨x, show Q (w ++ [x]) = true by rw [← h]; exact hx⟩

end ContractMonitors
