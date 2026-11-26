import FormalConjectures.Paper.MonochromaticQuantumGraph
import Mathlib.Data.Fintype.Pigeonhole

/-! Each monochromatic assignment must have a nonzero perfect matching.
Two distinct colors cannot use the same matching: taking one of its edges
in each color gives a nonzero term in a mixed assignment of total weight
zero. There are just three perfect matchings of four vertices. -/

open MonochromaticQuantumGraph
open scoped NNReal Matrix

theorem OMA.solution : type_of% @MonochromaticQuantumGraph.eqSystem4_no_solution_nnreal_ge4 := by
  intro D hD
  rintro ⟨W, hW⟩
  let w (i j : Fin 4) (x y : Fin D) := W (mkEdge i j x y)
  have eqn (a b c d : Fin D) :
      w 0 1 a b * w 2 3 c d + (w 0 2 a c * w 1 3 b d + w 0 3 a d * w 1 2 b c) =
        if a = b ∧ b = c ∧ c = d then 1 else 0 := by
    simpa [w, pmSumN, pmSumList, pmSumListAux, vertices, allEqual, allEqualList, add_assoc]
      using hW ![a, b, c, d]
  let supported (x : Fin D) : Fin 3 → Prop :=
    ![w 0 1 x x ≠ 0 ∧ w 2 3 x x ≠ 0,
      w 0 2 x x ≠ 0 ∧ w 1 3 x x ≠ 0,
      w 0 3 x x ≠ 0 ∧ w 1 2 x x ≠ 0]
  have exists_matching (x : Fin D) : ∃ k, supported x k := by
    by_contra! h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    change ¬ (_ ≠ 0 ∧ _ ≠ 0) at h0 h1 h2
    have hm := eqn x x x x
    simp only [and_self, if_true] at hm
    have z (a b : ℝ≥0) (h : ¬ (a ≠ 0 ∧ b ≠ 0)) : a*b = 0 := by
      by_cases ha : a = 0
      · simp [ha]
      · have hb : b = 0 := by by_contra hb; exact h ⟨ha, hb⟩
        simp [hb]
    simpa [z _ _ h0, z _ _ h1, z _ _ h2] using hm
  choose f hf using exists_matching
  obtain ⟨x, y, hxy, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp only [Fintype.card_fin]; omega)
  have hx := hf x
  have hy : supported y (f x) := he ▸ hf y
  generalize hk : f x = k at hx hy
  fin_cases k
  · change _ ≠ 0 ∧ _ ≠ 0 at hx hy
    have hm := eqn x x y y
    simp [hxy] at hm
    exact hm.1.elim hx.1 hy.2
  · change _ ≠ 0 ∧ _ ≠ 0 at hx hy
    have hm := eqn x y x y
    simp [hxy] at hm
    exact hm.2.1.elim hx.1 hy.2
  · change _ ≠ 0 ∧ _ ≠ 0 at hx hy
    have hm := eqn x y y x
    simp [hxy] at hm
    exact hm.2.2.elim hx.1 hy.2
