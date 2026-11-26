import FormalConjectures.OptimizationConstants.«6a»

/-! The power set of a singleton gives the upper bound for the union-closed sets constant. -/

open Finset Constant6a

theorem OMA.solution : type_of% @Constant6a.c6a_upper_bound := by
  unfold C6a
  apply csSup_le
  · refine ⟨0, ?_⟩
    intro A _ _
    exact ⟨0, by simp⟩
  · intro c hc
    let family : Finset (Finset ℕ) := {∅, {0}}
    have hne : family ≠ {∅} := by decide
    have hclosed : ∀ X ∈ family, ∀ Y ∈ family, X ∪ Y ∈ family := by decide
    obtain ⟨i, hi⟩ := hc family hne hclosed
    have hcard : family.card = 2 := by decide
    rw [hcard] at hi
    by_cases h : i = 0
    · subst i
      have hfreq : (family.filter (fun X => 0 ∈ X)).card = 1 := by decide
      rw [hfreq] at hi
      norm_num at hi ⊢
      linarith
    · have hfreq : (family.filter (fun X => i ∈ X)).card = 0 := by
        simp [family, Finset.filter_insert, h]
      rw [hfreq] at hi
      norm_num at hi ⊢
      linarith
