import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1

/-! Eleven pairs of consecutive integers suffice for the cubic character bound.
All their prime factors belong to {2,3,7,11,13}, so the common search checks
only 3^5 assignments. Each individual factorization is checked separately. -/

private lemma forms : ∀ (x2 x3 x7 x11 x13 : ZMod 3),
    ([].sum (α:=ZMod 3)=0 ∧ [x2].sum=0) ∨
    ([x2,x3].sum=0 ∧ [x7].sum=0) ∨
    ([x7].sum=0 ∧ [x2,x2,x2].sum=0) ∨
    ([x2,x2,x2].sum=0 ∧ [x3,x3].sum=0) ∨
    ([x11].sum=0 ∧ [x2,x2,x3].sum=0) ∨
    ([x2,x2,x3].sum=0 ∧ [x13].sum=0) ∨
    ([x3,x7].sum=0 ∧ [x2,x11].sum=0) ∨
    ([x2,x13].sum=0 ∧ [x3,x3,x3].sum=0) ∨
    ([x3,x3,x3].sum=0 ∧ [x2,x2,x7].sum=0) ∨
    ([x3,x3,x7].sum=0 ∧ [x2,x2,x2,x2,x2,x2].sum=0) ∨
    ([x7,x11].sum=0 ∧ [x2,x3,x13].sum=0) := by decide +kernel

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  intro w
  rcases forms (w 2) (w 3) (w 7) (w 11) (w 13) with h|h|h|h|h|h|h|h|h|h|h
  · refine ⟨1,by decide,?_,?_⟩
    · rw [show (1 : ℕ).primeFactorsList = [] by decide +kernel]
      exact h.1
    · rw [show (2 : ℕ).primeFactorsList = [2] by decide +kernel]
      exact h.2
  · refine ⟨6,by decide,?_,?_⟩
    · rw [show (6 : ℕ).primeFactorsList = [2, 3] by decide +kernel]
      exact h.1
    · rw [show (7 : ℕ).primeFactorsList = [7] by decide +kernel]
      exact h.2
  · refine ⟨7,by decide,?_,?_⟩
    · rw [show (7 : ℕ).primeFactorsList = [7] by decide +kernel]
      exact h.1
    · rw [show (8 : ℕ).primeFactorsList = [2, 2, 2] by decide +kernel]
      exact h.2
  · refine ⟨8,by decide,?_,?_⟩
    · rw [show (8 : ℕ).primeFactorsList = [2, 2, 2] by decide +kernel]
      exact h.1
    · rw [show (9 : ℕ).primeFactorsList = [3, 3] by decide +kernel]
      exact h.2
  · refine ⟨11,by decide,?_,?_⟩
    · rw [show (11 : ℕ).primeFactorsList = [11] by decide +kernel]
      exact h.1
    · rw [show (12 : ℕ).primeFactorsList = [2, 2, 3] by decide +kernel]
      exact h.2
  · refine ⟨12,by decide,?_,?_⟩
    · rw [show (12 : ℕ).primeFactorsList = [2, 2, 3] by decide +kernel]
      exact h.1
    · rw [show (13 : ℕ).primeFactorsList = [13] by decide +kernel]
      exact h.2
  · refine ⟨21,by decide,?_,?_⟩
    · rw [show (21 : ℕ).primeFactorsList = [3, 7] by decide +kernel]
      exact h.1
    · rw [show (22 : ℕ).primeFactorsList = [2, 11] by decide +kernel]
      exact h.2
  · refine ⟨26,by decide,?_,?_⟩
    · rw [show (26 : ℕ).primeFactorsList = [2, 13] by decide +kernel]
      exact h.1
    · rw [show (27 : ℕ).primeFactorsList = [3, 3, 3] by decide +kernel]
      exact h.2
  · refine ⟨27,by decide,?_,?_⟩
    · rw [show (27 : ℕ).primeFactorsList = [3, 3, 3] by decide +kernel]
      exact h.1
    · rw [show (28 : ℕ).primeFactorsList = [2, 2, 7] by decide +kernel]
      exact h.2
  · refine ⟨63,by decide,?_,?_⟩
    · rw [show (63 : ℕ).primeFactorsList = [3, 3, 7] by decide +kernel]
      exact h.1
    · rw [show (64 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 2] by decide +kernel]
      exact h.2
  · refine ⟨77,by decide,?_,?_⟩
    · rw [show (77 : ℕ).primeFactorsList = [7, 11] by decide +kernel]
      exact h.1
    · rw [show (78 : ℕ).primeFactorsList = [2, 3, 13] by decide +kernel]
      exact h.2
