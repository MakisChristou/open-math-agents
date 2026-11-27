import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1

/-! A finite decision tree for the quartic case-vector search. Each row gives
the two linear forms obtained by factoring its consecutive integers. Splitting
on prime weights modulo four proves that a listed row vanishes for every
assignment. All factorizations and leaf computations are kernel checked. -/

namespace OMA.QuarticCases


private def goal (w : ℕ → ZMod 4) : Prop :=
  ∃ n ∈ Finset.Icc 1 1224, (n.primeFactorsList.map w).sum = 0 ∧
    ((n+1).primeFactorsList.map w).sum = 0

private theorem cases4 : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide +kernel


private theorem f1 (w : ℕ → ZMod 4) : ((1 : ℕ).primeFactorsList.map w).sum = 0 := by simp

private theorem f2 (w : ℕ → ZMod 4) : ((2 : ℕ).primeFactorsList.map w).sum = 1 * w 2 := by
  rw [show (2 : ℕ).primeFactorsList = [2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 := by ring
    _ = _ := by
      rfl

private theorem f3 (w : ℕ → ZMod 4) : ((3 : ℕ).primeFactorsList.map w).sum = 1 * w 3 := by
  rw [show (3 : ℕ).primeFactorsList = [3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f4 (w : ℕ → ZMod 4) : ((4 : ℕ).primeFactorsList.map w).sum = 2 * w 2 := by
  rw [show (4 : ℕ).primeFactorsList = [2, 2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 := by ring
    _ = _ := by
      rfl

private theorem f5 (w : ℕ → ZMod 4) : ((5 : ℕ).primeFactorsList.map w).sum = 1 * w 5 := by
  rw [show (5 : ℕ).primeFactorsList = [5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f6 (w : ℕ → ZMod 4) : ((6 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 3 := by
  rw [show (6 : ℕ).primeFactorsList = [2, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f7 (w : ℕ → ZMod 4) : ((7 : ℕ).primeFactorsList.map w).sum = 1 * w 7 := by
  rw [show (7 : ℕ).primeFactorsList = [7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f9 (w : ℕ → ZMod 4) : ((9 : ℕ).primeFactorsList.map w).sum = 2 * w 3 := by
  rw [show (9 : ℕ).primeFactorsList = [3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f10 (w : ℕ → ZMod 4) : ((10 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 5 := by
  rw [show (10 : ℕ).primeFactorsList = [2, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f11 (w : ℕ → ZMod 4) : ((11 : ℕ).primeFactorsList.map w).sum = 1 * w 11 := by
  rw [show (11 : ℕ).primeFactorsList = [11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f12 (w : ℕ → ZMod 4) : ((12 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 3 := by
  rw [show (12 : ℕ).primeFactorsList = [2, 2, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f13 (w : ℕ → ZMod 4) : ((13 : ℕ).primeFactorsList.map w).sum = 1 * w 13 := by
  rw [show (13 : ℕ).primeFactorsList = [13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f14 (w : ℕ → ZMod 4) : ((14 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 7 := by
  rw [show (14 : ℕ).primeFactorsList = [2, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f15 (w : ℕ → ZMod 4) : ((15 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 5 := by
  rw [show (15 : ℕ).primeFactorsList = [3, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f16 (w : ℕ → ZMod 4) : ((16 : ℕ).primeFactorsList.map w).sum = 0 := by
  rw [show (16 : ℕ).primeFactorsList = [2, 2, 2, 2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 4 * w 2 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul]

private theorem f17 (w : ℕ → ZMod 4) : ((17 : ℕ).primeFactorsList.map w).sum = 1 * w 17 := by
  rw [show (17 : ℕ).primeFactorsList = [17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f20 (w : ℕ → ZMod 4) : ((20 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 5 := by
  rw [show (20 : ℕ).primeFactorsList = [2, 2, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f21 (w : ℕ → ZMod 4) : ((21 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 7 := by
  rw [show (21 : ℕ).primeFactorsList = [3, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f22 (w : ℕ → ZMod 4) : ((22 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 11 := by
  rw [show (22 : ℕ).primeFactorsList = [2, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f24 (w : ℕ → ZMod 4) : ((24 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 3 := by
  rw [show (24 : ℕ).primeFactorsList = [2, 2, 2, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f25 (w : ℕ → ZMod 4) : ((25 : ℕ).primeFactorsList.map w).sum = 2 * w 5 := by
  rw [show (25 : ℕ).primeFactorsList = [5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f26 (w : ℕ → ZMod 4) : ((26 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 13 := by
  rw [show (26 : ℕ).primeFactorsList = [2, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f27 (w : ℕ → ZMod 4) : ((27 : ℕ).primeFactorsList.map w).sum = 3 * w 3 := by
  rw [show (27 : ℕ).primeFactorsList = [3, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f28 (w : ℕ → ZMod 4) : ((28 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 7 := by
  rw [show (28 : ℕ).primeFactorsList = [2, 2, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f33 (w : ℕ → ZMod 4) : ((33 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 11 := by
  rw [show (33 : ℕ).primeFactorsList = [3, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f34 (w : ℕ → ZMod 4) : ((34 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 17 := by
  rw [show (34 : ℕ).primeFactorsList = [2, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f35 (w : ℕ → ZMod 4) : ((35 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 7 := by
  rw [show (35 : ℕ).primeFactorsList = [5, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f36 (w : ℕ → ZMod 4) : ((36 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 2 * w 3 := by
  rw [show (36 : ℕ).primeFactorsList = [2, 2, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 2 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f39 (w : ℕ → ZMod 4) : ((39 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 13 := by
  rw [show (39 : ℕ).primeFactorsList = [3, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f40 (w : ℕ → ZMod 4) : ((40 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 5 := by
  rw [show (40 : ℕ).primeFactorsList = [2, 2, 2, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f41 (w : ℕ → ZMod 4) : ((41 : ℕ).primeFactorsList.map w).sum = 1 * w 41 := by
  rw [show (41 : ℕ).primeFactorsList = [41] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 41 := by ring
    _ = _ := by
      rfl

private theorem f48 (w : ℕ → ZMod 4) : ((48 : ℕ).primeFactorsList.map w).sum = 1 * w 3 := by
  rw [show (48 : ℕ).primeFactorsList = [2, 2, 2, 2, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 4 * w 2 + 1 * w 3 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul, zero_add]

private theorem f49 (w : ℕ → ZMod 4) : ((49 : ℕ).primeFactorsList.map w).sum = 2 * w 7 := by
  rw [show (49 : ℕ).primeFactorsList = [7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f50 (w : ℕ → ZMod 4) : ((50 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 2 * w 5 := by
  rw [show (50 : ℕ).primeFactorsList = [2, 5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 2 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f51 (w : ℕ → ZMod 4) : ((51 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 17 := by
  rw [show (51 : ℕ).primeFactorsList = [3, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f52 (w : ℕ → ZMod 4) : ((52 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 13 := by
  rw [show (52 : ℕ).primeFactorsList = [2, 2, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f54 (w : ℕ → ZMod 4) : ((54 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 3 * w 3 := by
  rw [show (54 : ℕ).primeFactorsList = [2, 3, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 3 * w 3 := by ring
    _ = _ := by
      rfl

private theorem f55 (w : ℕ → ZMod 4) : ((55 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 11 := by
  rw [show (55 : ℕ).primeFactorsList = [5, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f56 (w : ℕ → ZMod 4) : ((56 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 7 := by
  rw [show (56 : ℕ).primeFactorsList = [2, 2, 2, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f63 (w : ℕ → ZMod 4) : ((63 : ℕ).primeFactorsList.map w).sum = 2 * w 3 + 1 * w 7 := by
  rw [show (63 : ℕ).primeFactorsList = [3, 3, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f64 (w : ℕ → ZMod 4) : ((64 : ℕ).primeFactorsList.map w).sum = 2 * w 2 := by
  rw [show (64 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 6 * w 2 := by ring
    _ = _ := by
      simp only [show (6 : ZMod 4) = 2 by decide]

private theorem f65 (w : ℕ → ZMod 4) : ((65 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 13 := by
  rw [show (65 : ℕ).primeFactorsList = [5, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f77 (w : ℕ → ZMod 4) : ((77 : ℕ).primeFactorsList.map w).sum = 1 * w 7 + 1 * w 11 := by
  rw [show (77 : ℕ).primeFactorsList = [7, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 7 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f78 (w : ℕ → ZMod 4) : ((78 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 3 + 1 * w 13 := by
  rw [show (78 : ℕ).primeFactorsList = [2, 3, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 3 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f80 (w : ℕ → ZMod 4) : ((80 : ℕ).primeFactorsList.map w).sum = 1 * w 5 := by
  rw [show (80 : ℕ).primeFactorsList = [2, 2, 2, 2, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 4 * w 2 + 1 * w 5 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul, zero_add]

private theorem f81 (w : ℕ → ZMod 4) : ((81 : ℕ).primeFactorsList.map w).sum = 0 := by
  rw [show (81 : ℕ).primeFactorsList = [3, 3, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 4 * w 3 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul]

private theorem f82 (w : ℕ → ZMod 4) : ((82 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 41 := by
  rw [show (82 : ℕ).primeFactorsList = [2, 41] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 41 := by ring
    _ = _ := by
      rfl

private theorem f84 (w : ℕ → ZMod 4) : ((84 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 3 + 1 * w 7 := by
  rw [show (84 : ℕ).primeFactorsList = [2, 2, 3, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 3 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f85 (w : ℕ → ZMod 4) : ((85 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 17 := by
  rw [show (85 : ℕ).primeFactorsList = [5, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f90 (w : ℕ → ZMod 4) : ((90 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 2 * w 3 + 1 * w 5 := by
  rw [show (90 : ℕ).primeFactorsList = [2, 3, 3, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 2 * w 3 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f91 (w : ℕ → ZMod 4) : ((91 : ℕ).primeFactorsList.map w).sum = 1 * w 7 + 1 * w 13 := by
  rw [show (91 : ℕ).primeFactorsList = [7, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 7 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f98 (w : ℕ → ZMod 4) : ((98 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 2 * w 7 := by
  rw [show (98 : ℕ).primeFactorsList = [2, 7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 2 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f99 (w : ℕ → ZMod 4) : ((99 : ℕ).primeFactorsList.map w).sum = 2 * w 3 + 1 * w 11 := by
  rw [show (99 : ℕ).primeFactorsList = [3, 3, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f100 (w : ℕ → ZMod 4) : ((100 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 2 * w 5 := by
  rw [show (100 : ℕ).primeFactorsList = [2, 2, 5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 2 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f104 (w : ℕ → ZMod 4) : ((104 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 13 := by
  rw [show (104 : ℕ).primeFactorsList = [2, 2, 2, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f105 (w : ℕ → ZMod 4) : ((105 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 5 + 1 * w 7 := by
  rw [show (105 : ℕ).primeFactorsList = [3, 5, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 5 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f119 (w : ℕ → ZMod 4) : ((119 : ℕ).primeFactorsList.map w).sum = 1 * w 7 + 1 * w 17 := by
  rw [show (119 : ℕ).primeFactorsList = [7, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 7 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f120 (w : ℕ → ZMod 4) : ((120 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 3 + 1 * w 5 := by
  rw [show (120 : ℕ).primeFactorsList = [2, 2, 2, 3, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 3 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f121 (w : ℕ → ZMod 4) : ((121 : ℕ).primeFactorsList.map w).sum = 2 * w 11 := by
  rw [show (121 : ℕ).primeFactorsList = [11, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f135 (w : ℕ → ZMod 4) : ((135 : ℕ).primeFactorsList.map w).sum = 3 * w 3 + 1 * w 5 := by
  rw [show (135 : ℕ).primeFactorsList = [3, 3, 3, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 3 + 1 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f136 (w : ℕ → ZMod 4) : ((136 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 17 := by
  rw [show (136 : ℕ).primeFactorsList = [2, 2, 2, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f153 (w : ℕ → ZMod 4) : ((153 : ℕ).primeFactorsList.map w).sum = 2 * w 3 + 1 * w 17 := by
  rw [show (153 : ℕ).primeFactorsList = [3, 3, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f154 (w : ℕ → ZMod 4) : ((154 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 7 + 1 * w 11 := by
  rw [show (154 : ℕ).primeFactorsList = [2, 7, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 7 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f168 (w : ℕ → ZMod 4) : ((168 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 3 + 1 * w 7 := by
  rw [show (168 : ℕ).primeFactorsList = [2, 2, 2, 3, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 3 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f169 (w : ℕ → ZMod 4) : ((169 : ℕ).primeFactorsList.map w).sum = 2 * w 13 := by
  rw [show (169 : ℕ).primeFactorsList = [13, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f175 (w : ℕ → ZMod 4) : ((175 : ℕ).primeFactorsList.map w).sum = 2 * w 5 + 1 * w 7 := by
  rw [show (175 : ℕ).primeFactorsList = [5, 5, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 5 + 1 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f176 (w : ℕ → ZMod 4) : ((176 : ℕ).primeFactorsList.map w).sum = 1 * w 11 := by
  rw [show (176 : ℕ).primeFactorsList = [2, 2, 2, 2, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 4 * w 2 + 1 * w 11 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul, zero_add]

private theorem f195 (w : ℕ → ZMod 4) : ((195 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 5 + 1 * w 13 := by
  rw [show (195 : ℕ).primeFactorsList = [3, 5, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 5 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f196 (w : ℕ → ZMod 4) : ((196 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 2 * w 7 := by
  rw [show (196 : ℕ).primeFactorsList = [2, 2, 7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 2 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f220 (w : ℕ → ZMod 4) : ((220 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 1 * w 5 + 1 * w 11 := by
  rw [show (220 : ℕ).primeFactorsList = [2, 2, 5, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 1 * w 5 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f221 (w : ℕ → ZMod 4) : ((221 : ℕ).primeFactorsList.map w).sum = 1 * w 13 + 1 * w 17 := by
  rw [show (221 : ℕ).primeFactorsList = [13, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 13 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f224 (w : ℕ → ZMod 4) : ((224 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 7 := by
  rw [show (224 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 5 * w 2 + 1 * w 7 := by ring
    _ = _ := by
      simp only [show (5 : ZMod 4) = 1 by decide]

private theorem f225 (w : ℕ → ZMod 4) : ((225 : ℕ).primeFactorsList.map w).sum = 2 * w 3 + 2 * w 5 := by
  rw [show (225 : ℕ).primeFactorsList = [3, 3, 5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 + 2 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f245 (w : ℕ → ZMod 4) : ((245 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 2 * w 7 := by
  rw [show (245 : ℕ).primeFactorsList = [5, 7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 2 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f246 (w : ℕ → ZMod 4) : ((246 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 3 + 1 * w 41 := by
  rw [show (246 : ℕ).primeFactorsList = [2, 3, 41] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 3 + 1 * w 41 := by ring
    _ = _ := by
      rfl

private theorem f255 (w : ℕ → ZMod 4) : ((255 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 1 * w 5 + 1 * w 17 := by
  rw [show (255 : ℕ).primeFactorsList = [3, 5, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 1 * w 5 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f256 (w : ℕ → ZMod 4) : ((256 : ℕ).primeFactorsList.map w).sum = 0 := by
  rw [show (256 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 2, 2, 2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 8 * w 2 := by ring
    _ = _ := by
      simp only [show (8 : ZMod 4) = 0 by decide, zero_mul]

private theorem f286 (w : ℕ → ZMod 4) : ((286 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 11 + 1 * w 13 := by
  rw [show (286 : ℕ).primeFactorsList = [2, 11, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 11 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f287 (w : ℕ → ZMod 4) : ((287 : ℕ).primeFactorsList.map w).sum = 1 * w 7 + 1 * w 41 := by
  rw [show (287 : ℕ).primeFactorsList = [7, 41] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 7 + 1 * w 41 := by ring
    _ = _ := by
      rfl

private theorem f324 (w : ℕ → ZMod 4) : ((324 : ℕ).primeFactorsList.map w).sum = 2 * w 2 := by
  rw [show (324 : ℕ).primeFactorsList = [2, 2, 3, 3, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 4 * w 3 := by ring
    _ = _ := by
      simp only [show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

private theorem f325 (w : ℕ → ZMod 4) : ((325 : ℕ).primeFactorsList.map w).sum = 2 * w 5 + 1 * w 13 := by
  rw [show (325 : ℕ).primeFactorsList = [5, 5, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 5 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f351 (w : ℕ → ZMod 4) : ((351 : ℕ).primeFactorsList.map w).sum = 3 * w 3 + 1 * w 13 := by
  rw [show (351 : ℕ).primeFactorsList = [3, 3, 3, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 3 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f352 (w : ℕ → ZMod 4) : ((352 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 11 := by
  rw [show (352 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 5 * w 2 + 1 * w 11 := by ring
    _ = _ := by
      simp only [show (5 : ZMod 4) = 1 by decide]

private theorem f374 (w : ℕ → ZMod 4) : ((374 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 11 + 1 * w 17 := by
  rw [show (374 : ℕ).primeFactorsList = [2, 11, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 11 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f375 (w : ℕ → ZMod 4) : ((375 : ℕ).primeFactorsList.map w).sum = 1 * w 3 + 3 * w 5 := by
  rw [show (375 : ℕ).primeFactorsList = [3, 5, 5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 3 + 3 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f384 (w : ℕ → ZMod 4) : ((384 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 3 := by
  rw [show (384 : ℕ).primeFactorsList = [2, 2, 2, 2, 2, 2, 2, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 7 * w 2 + 1 * w 3 := by ring
    _ = _ := by
      simp only [show (7 : ZMod 4) = 3 by decide]

private theorem f385 (w : ℕ → ZMod 4) : ((385 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 7 + 1 * w 11 := by
  rw [show (385 : ℕ).primeFactorsList = [5, 7, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 7 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f440 (w : ℕ → ZMod 4) : ((440 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 5 + 1 * w 11 := by
  rw [show (440 : ℕ).primeFactorsList = [2, 2, 2, 5, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 5 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f441 (w : ℕ → ZMod 4) : ((441 : ℕ).primeFactorsList.map w).sum = 2 * w 3 + 2 * w 7 := by
  rw [show (441 : ℕ).primeFactorsList = [3, 3, 7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 3 + 2 * w 7 := by ring
    _ = _ := by
      rfl

private theorem f442 (w : ℕ → ZMod 4) : ((442 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 1 * w 13 + 1 * w 17 := by
  rw [show (442 : ℕ).primeFactorsList = [2, 13, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 1 * w 13 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f594 (w : ℕ → ZMod 4) : ((594 : ℕ).primeFactorsList.map w).sum = 1 * w 2 + 3 * w 3 + 1 * w 11 := by
  rw [show (594 : ℕ).primeFactorsList = [2, 3, 3, 3, 11] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 2 + 3 * w 3 + 1 * w 11 := by ring
    _ = _ := by
      rfl

private theorem f595 (w : ℕ → ZMod 4) : ((595 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 7 + 1 * w 17 := by
  rw [show (595 : ℕ).primeFactorsList = [5, 7, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 7 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f675 (w : ℕ → ZMod 4) : ((675 : ℕ).primeFactorsList.map w).sum = 3 * w 3 + 2 * w 5 := by
  rw [show (675 : ℕ).primeFactorsList = [3, 3, 3, 5, 5] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 3 + 2 * w 5 := by ring
    _ = _ := by
      rfl

private theorem f676 (w : ℕ → ZMod 4) : ((676 : ℕ).primeFactorsList.map w).sum = 2 * w 2 + 2 * w 13 := by
  rw [show (676 : ℕ).primeFactorsList = [2, 2, 13, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 2 + 2 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f728 (w : ℕ → ZMod 4) : ((728 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 1 * w 7 + 1 * w 13 := by
  rw [show (728 : ℕ).primeFactorsList = [2, 2, 2, 7, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 1 * w 7 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f729 (w : ℕ → ZMod 4) : ((729 : ℕ).primeFactorsList.map w).sum = 2 * w 3 := by
  rw [show (729 : ℕ).primeFactorsList = [3, 3, 3, 3, 3, 3] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 6 * w 3 := by ring
    _ = _ := by
      simp only [show (6 : ZMod 4) = 2 by decide]

private theorem f935 (w : ℕ → ZMod 4) : ((935 : ℕ).primeFactorsList.map w).sum = 1 * w 5 + 1 * w 11 + 1 * w 17 := by
  rw [show (935 : ℕ).primeFactorsList = [5, 11, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 1 * w 5 + 1 * w 11 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f936 (w : ℕ → ZMod 4) : ((936 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 2 * w 3 + 1 * w 13 := by
  rw [show (936 : ℕ).primeFactorsList = [2, 2, 2, 3, 3, 13] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 2 * w 3 + 1 * w 13 := by ring
    _ = _ := by
      rfl

private theorem f1224 (w : ℕ → ZMod 4) : ((1224 : ℕ).primeFactorsList.map w).sum = 3 * w 2 + 2 * w 3 + 1 * w 17 := by
  rw [show (1224 : ℕ).primeFactorsList = [2, 2, 2, 3, 3, 17] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 3 * w 2 + 2 * w 3 + 1 * w 17 := by ring
    _ = _ := by
      rfl

private theorem f1225 (w : ℕ → ZMod 4) : ((1225 : ℕ).primeFactorsList.map w).sum = 2 * w 5 + 2 * w 7 := by
  rw [show (1225 : ℕ).primeFactorsList = [5, 5, 7, 7] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = 2 * w 5 + 2 * w 7 := by ring
    _ = _ := by
      rfl

set_option maxRecDepth 10000 in
private theorem win1 (w : ℕ → ZMod 4) (a : 0 = (0 : ZMod 4))
    (b : 1 * w 2 = (0 : ZMod 4)) : goal w :=
  ⟨1, by decide, (f1 w).trans a, (f2 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win3 (w : ℕ → ZMod 4) (a : 1 * w 3 = (0 : ZMod 4))
    (b : 2 * w 2 = (0 : ZMod 4)) : goal w :=
  ⟨3, by decide, (f3 w).trans a, (f4 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win4 (w : ℕ → ZMod 4) (a : 2 * w 2 = (0 : ZMod 4))
    (b : 1 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨4, by decide, (f4 w).trans a, (f5 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win5 (w : ℕ → ZMod 4) (a : 1 * w 5 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 3 = (0 : ZMod 4)) : goal w :=
  ⟨5, by decide, (f5 w).trans a, (f6 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win6 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 3 = (0 : ZMod 4))
    (b : 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨6, by decide, (f6 w).trans a, (f7 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win9 (w : ℕ → ZMod 4) (a : 2 * w 3 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨9, by decide, (f9 w).trans a, (f10 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win10 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 5 = (0 : ZMod 4))
    (b : 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨10, by decide, (f10 w).trans a, (f11 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win12 (w : ℕ → ZMod 4) (a : 2 * w 2 + 1 * w 3 = (0 : ZMod 4))
    (b : 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨12, by decide, (f12 w).trans a, (f13 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win13 (w : ℕ → ZMod 4) (a : 1 * w 13 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨13, by decide, (f13 w).trans a, (f14 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win15 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 5 = (0 : ZMod 4))
    (b : 0 = (0 : ZMod 4)) : goal w :=
  ⟨15, by decide, (f15 w).trans a, (f16 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win16 (w : ℕ → ZMod 4) (a : 0 = (0 : ZMod 4))
    (b : 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨16, by decide, (f16 w).trans a, (f17 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win20 (w : ℕ → ZMod 4) (a : 2 * w 2 + 1 * w 5 = (0 : ZMod 4))
    (b : 1 * w 3 + 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨20, by decide, (f20 w).trans a, (f21 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win21 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 7 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨21, by decide, (f21 w).trans a, (f22 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win24 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 3 = (0 : ZMod 4))
    (b : 2 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨24, by decide, (f24 w).trans a, (f25 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win25 (w : ℕ → ZMod 4) (a : 2 * w 5 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨25, by decide, (f25 w).trans a, (f26 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win26 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 13 = (0 : ZMod 4))
    (b : 3 * w 3 = (0 : ZMod 4)) : goal w :=
  ⟨26, by decide, (f26 w).trans a, (f27 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win27 (w : ℕ → ZMod 4) (a : 3 * w 3 = (0 : ZMod 4))
    (b : 2 * w 2 + 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨27, by decide, (f27 w).trans a, (f28 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win33 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 11 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨33, by decide, (f33 w).trans a, (f34 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win35 (w : ℕ → ZMod 4) (a : 1 * w 5 + 1 * w 7 = (0 : ZMod 4))
    (b : 2 * w 2 + 2 * w 3 = (0 : ZMod 4)) : goal w :=
  ⟨35, by decide, (f35 w).trans a, (f36 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win39 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 13 = (0 : ZMod 4))
    (b : 3 * w 2 + 1 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨39, by decide, (f39 w).trans a, (f40 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win40 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 5 = (0 : ZMod 4))
    (b : 1 * w 41 = (0 : ZMod 4)) : goal w :=
  ⟨40, by decide, (f40 w).trans a, (f41 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win48 (w : ℕ → ZMod 4) (a : 1 * w 3 = (0 : ZMod 4))
    (b : 2 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨48, by decide, (f48 w).trans a, (f49 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win49 (w : ℕ → ZMod 4) (a : 2 * w 7 = (0 : ZMod 4))
    (b : 1 * w 2 + 2 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨49, by decide, (f49 w).trans a, (f50 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win50 (w : ℕ → ZMod 4) (a : 1 * w 2 + 2 * w 5 = (0 : ZMod 4))
    (b : 1 * w 3 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨50, by decide, (f50 w).trans a, (f51 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win51 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 17 = (0 : ZMod 4))
    (b : 2 * w 2 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨51, by decide, (f51 w).trans a, (f52 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win54 (w : ℕ → ZMod 4) (a : 1 * w 2 + 3 * w 3 = (0 : ZMod 4))
    (b : 1 * w 5 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨54, by decide, (f54 w).trans a, (f55 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win55 (w : ℕ → ZMod 4) (a : 1 * w 5 + 1 * w 11 = (0 : ZMod 4))
    (b : 3 * w 2 + 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨55, by decide, (f55 w).trans a, (f56 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win63 (w : ℕ → ZMod 4) (a : 2 * w 3 + 1 * w 7 = (0 : ZMod 4))
    (b : 2 * w 2 = (0 : ZMod 4)) : goal w :=
  ⟨63, by decide, (f63 w).trans a, (f64 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win64 (w : ℕ → ZMod 4) (a : 2 * w 2 = (0 : ZMod 4))
    (b : 1 * w 5 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨64, by decide, (f64 w).trans a, (f65 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win77 (w : ℕ → ZMod 4) (a : 1 * w 7 + 1 * w 11 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 3 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨77, by decide, (f77 w).trans a, (f78 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win80 (w : ℕ → ZMod 4) (a : 1 * w 5 = (0 : ZMod 4))
    (b : 0 = (0 : ZMod 4)) : goal w :=
  ⟨80, by decide, (f80 w).trans a, (f81 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win81 (w : ℕ → ZMod 4) (a : 0 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 41 = (0 : ZMod 4)) : goal w :=
  ⟨81, by decide, (f81 w).trans a, (f82 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win84 (w : ℕ → ZMod 4) (a : 2 * w 2 + 1 * w 3 + 1 * w 7 = (0 : ZMod 4))
    (b : 1 * w 5 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨84, by decide, (f84 w).trans a, (f85 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win90 (w : ℕ → ZMod 4) (a : 1 * w 2 + 2 * w 3 + 1 * w 5 = (0 : ZMod 4))
    (b : 1 * w 7 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨90, by decide, (f90 w).trans a, (f91 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win98 (w : ℕ → ZMod 4) (a : 1 * w 2 + 2 * w 7 = (0 : ZMod 4))
    (b : 2 * w 3 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨98, by decide, (f98 w).trans a, (f99 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win99 (w : ℕ → ZMod 4) (a : 2 * w 3 + 1 * w 11 = (0 : ZMod 4))
    (b : 2 * w 2 + 2 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨99, by decide, (f99 w).trans a, (f100 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win104 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 13 = (0 : ZMod 4))
    (b : 1 * w 3 + 1 * w 5 + 1 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨104, by decide, (f104 w).trans a, (f105 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win119 (w : ℕ → ZMod 4) (a : 1 * w 7 + 1 * w 17 = (0 : ZMod 4))
    (b : 3 * w 2 + 1 * w 3 + 1 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨119, by decide, (f119 w).trans a, (f120 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win120 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 3 + 1 * w 5 = (0 : ZMod 4))
    (b : 2 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨120, by decide, (f120 w).trans a, (f121 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win135 (w : ℕ → ZMod 4) (a : 3 * w 3 + 1 * w 5 = (0 : ZMod 4))
    (b : 3 * w 2 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨135, by decide, (f135 w).trans a, (f136 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win153 (w : ℕ → ZMod 4) (a : 2 * w 3 + 1 * w 17 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 7 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨153, by decide, (f153 w).trans a, (f154 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win168 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 3 + 1 * w 7 = (0 : ZMod 4))
    (b : 2 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨168, by decide, (f168 w).trans a, (f169 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win175 (w : ℕ → ZMod 4) (a : 2 * w 5 + 1 * w 7 = (0 : ZMod 4))
    (b : 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨175, by decide, (f175 w).trans a, (f176 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win195 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 5 + 1 * w 13 = (0 : ZMod 4))
    (b : 2 * w 2 + 2 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨195, by decide, (f195 w).trans a, (f196 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win220 (w : ℕ → ZMod 4) (a : 2 * w 2 + 1 * w 5 + 1 * w 11 = (0 : ZMod 4))
    (b : 1 * w 13 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨220, by decide, (f220 w).trans a, (f221 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win224 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 7 = (0 : ZMod 4))
    (b : 2 * w 3 + 2 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨224, by decide, (f224 w).trans a, (f225 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win245 (w : ℕ → ZMod 4) (a : 1 * w 5 + 2 * w 7 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 3 + 1 * w 41 = (0 : ZMod 4)) : goal w :=
  ⟨245, by decide, (f245 w).trans a, (f246 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win255 (w : ℕ → ZMod 4) (a : 1 * w 3 + 1 * w 5 + 1 * w 17 = (0 : ZMod 4))
    (b : 0 = (0 : ZMod 4)) : goal w :=
  ⟨255, by decide, (f255 w).trans a, (f256 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win286 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 11 + 1 * w 13 = (0 : ZMod 4))
    (b : 1 * w 7 + 1 * w 41 = (0 : ZMod 4)) : goal w :=
  ⟨286, by decide, (f286 w).trans a, (f287 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win324 (w : ℕ → ZMod 4) (a : 2 * w 2 = (0 : ZMod 4))
    (b : 2 * w 5 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨324, by decide, (f324 w).trans a, (f325 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win351 (w : ℕ → ZMod 4) (a : 3 * w 3 + 1 * w 13 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨351, by decide, (f351 w).trans a, (f352 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win374 (w : ℕ → ZMod 4) (a : 1 * w 2 + 1 * w 11 + 1 * w 17 = (0 : ZMod 4))
    (b : 1 * w 3 + 3 * w 5 = (0 : ZMod 4)) : goal w :=
  ⟨374, by decide, (f374 w).trans a, (f375 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win384 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 3 = (0 : ZMod 4))
    (b : 1 * w 5 + 1 * w 7 + 1 * w 11 = (0 : ZMod 4)) : goal w :=
  ⟨384, by decide, (f384 w).trans a, (f385 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win440 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 5 + 1 * w 11 = (0 : ZMod 4))
    (b : 2 * w 3 + 2 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨440, by decide, (f440 w).trans a, (f441 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win441 (w : ℕ → ZMod 4) (a : 2 * w 3 + 2 * w 7 = (0 : ZMod 4))
    (b : 1 * w 2 + 1 * w 13 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨441, by decide, (f441 w).trans a, (f442 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win594 (w : ℕ → ZMod 4) (a : 1 * w 2 + 3 * w 3 + 1 * w 11 = (0 : ZMod 4))
    (b : 1 * w 5 + 1 * w 7 + 1 * w 17 = (0 : ZMod 4)) : goal w :=
  ⟨594, by decide, (f594 w).trans a, (f595 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win675 (w : ℕ → ZMod 4) (a : 3 * w 3 + 2 * w 5 = (0 : ZMod 4))
    (b : 2 * w 2 + 2 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨675, by decide, (f675 w).trans a, (f676 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win728 (w : ℕ → ZMod 4) (a : 3 * w 2 + 1 * w 7 + 1 * w 13 = (0 : ZMod 4))
    (b : 2 * w 3 = (0 : ZMod 4)) : goal w :=
  ⟨728, by decide, (f728 w).trans a, (f729 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win935 (w : ℕ → ZMod 4) (a : 1 * w 5 + 1 * w 11 + 1 * w 17 = (0 : ZMod 4))
    (b : 3 * w 2 + 2 * w 3 + 1 * w 13 = (0 : ZMod 4)) : goal w :=
  ⟨935, by decide, (f935 w).trans a, (f936 w).trans b⟩

set_option maxRecDepth 10000 in
private theorem win1224 (w : ℕ → ZMod 4) (a : 3 * w 2 + 2 * w 3 + 1 * w 17 = (0 : ZMod 4))
    (b : 2 * w 5 + 2 * w 7 = (0 : ZMod 4)) : goal w :=
  ⟨1224, by decide, (f1224 w).trans a, (f1225 w).trans b⟩

private theorem part1 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 1) (h7 : w 7 = 1) (h13 : w 13 = 1) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win1224 w (by rw [h2, h3, h17]; decide) (by rw [h5, h7]; decide)
  · exact win935 w (by rw [h5, h11, h17]; decide) (by rw [h2, h3, h13]; decide)
  · exact win119 w (by rw [h7, h17]; decide) (by rw [h2, h3, h5]; decide)

private theorem part2 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 1) (h7 : w 7 = 1) (h13 : w 13 = 1) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact part1 w h2 h3 h5 h7 h13 h11
  · exact win120 w (by rw [h2, h3, h5]; decide) (by rw [h11]; decide)
  · exact win55 w (by rw [h5, h11]; decide) (by rw [h2, h7]; decide)

private theorem part3 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 1) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact part2 w h2 h3 h5 h7 h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win26 w (by rw [h2, h13]; decide) (by rw [h3]; decide)

private theorem part4 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 1) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win13 w (by rw [h13]; decide) (by rw [h2, h7]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)
  · exact win728 w (by rw [h2, h7, h13]; decide) (by rw [h3]; decide)
  · exact win26 w (by rw [h2, h13]; decide) (by rw [h3]; decide)

private theorem part5 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win48 w (by rw [h3]; decide) (by rw [h7]; decide)
  · exact part3 w h2 h3 h5 h7
  · exact win27 w (by rw [h3]; decide) (by rw [h2, h7]; decide)
  · exact part4 w h2 h3 h5 h7

private theorem part6 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 2) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)

private theorem part7 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win20 w (by rw [h2, h5]; decide) (by rw [h3, h7]; decide)
  · exact part6 w h2 h3 h5 h7
  · exact win27 w (by rw [h3]; decide) (by rw [h2, h7]; decide)
  · exact win224 w (by rw [h2, h7]; decide) (by rw [h3, h5]; decide)

private theorem part8 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 0) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact part5 w h2 h3 h5
  · exact part7 w h2 h3 h5
  · exact win9 w (by rw [h3]; decide) (by rw [h2, h5]; decide)

private theorem part9 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (_h7 : w 7 = 0) (h11 : w 11 = 0) (_h13 : w 13 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win374 w (by rw [h2, h11, h17]; decide) (by rw [h3, h5]; decide)

private theorem part10 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 0) (h11 : w 11 = 0) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win90 w (by rw [h2, h3, h5]; decide) (by rw [h7, h13]; decide)
  · exact part9 w h2 h3 h5 h7 h11 h13
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)

private theorem part11 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (_h7 : w 7 = 0) (h11 : w 11 = 1) (h13 : w 13 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win220 w (by rw [h2, h5, h11]; decide) (by rw [h13, h17]; decide)

private theorem part12 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 0) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win90 w (by rw [h2, h3, h5]; decide) (by rw [h7, h13]; decide)
  · exact part11 w h2 h3 h5 h7 h11 h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)

private theorem part13 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 0) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact part10 w h2 h3 h5 h7 h11
  · exact part12 w h2 h3 h5 h7 h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)

private theorem part14 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 1) (_h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win84 w (by rw [h2, h3, h7]; decide) (by rw [h5, h17]; decide)

private theorem part15 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win440 w (by rw [h2, h5, h11]; decide) (by rw [h3, h7]; decide)
  · exact part14 w h2 h3 h5 h7 h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)

private theorem part16 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 2) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win175 w (by rw [h5, h7]; decide) (by rw [h11]; decide)
  · exact win384 w (by rw [h2, h3]; decide) (by rw [h5, h7, h11]; decide)
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)

private theorem part17 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact part13 w h2 h3 h5 h7
  · exact part15 w h2 h3 h5 h7
  · exact part16 w h2 h3 h5 h7
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)

private theorem part18 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 1) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win24 w (by rw [h2, h3]; decide) (by rw [h5]; decide)
  · exact part17 w h2 h3 h5
  · exact win24 w (by rw [h2, h3]; decide) (by rw [h5]; decide)
  · exact win15 w (by rw [h3, h5]; decide) (by decide)

private theorem part19 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 2) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win12 w (by rw [h2, h3]; decide) (by rw [h13]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)

private theorem part20 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 2) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win80 w (by rw [h5]; decide) (by decide)
  · exact part19 w h2 h3 h5
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact win9 w (by rw [h3]; decide) (by rw [h2, h5]; decide)

private theorem part21 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 2) (h7 : w 7 = 3) (h13 : w 13 = 2) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win51 w (by rw [h3, h17]; decide) (by rw [h2, h13]; decide)
  · exact win84 w (by rw [h2, h3, h7]; decide) (by rw [h5, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)

private theorem part22 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 2) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win13 w (by rw [h13]; decide) (by rw [h2, h7]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)
  · exact part21 w h2 h3 h5 h7 h13
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)

private theorem part23 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact win20 w (by rw [h2, h5]; decide) (by rw [h3, h7]; decide)
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)
  · exact part22 w h2 h3 h5 h7

private theorem part24 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 2) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact win153 w (by rw [h3, h17]; decide) (by rw [h2, h7, h11]; decide)
  · exact win33 w (by rw [h3, h11]; decide) (by rw [h2, h17]; decide)

private theorem part25 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 2) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win351 w (by rw [h3, h13]; decide) (by rw [h2, h11]; decide)

private theorem part26 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 2) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact part24 w h2 h3 h5 h7 h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact part25 w h2 h3 h5 h7 h11

private theorem part27 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)
  · exact part26 w h2 h3 h5 h7
  · exact win224 w (by rw [h2, h7]; decide) (by rw [h3, h5]; decide)

private theorem part28 (w : ℕ → ZMod 4) (h2 : w 2 = 1) (h3 : w 3 = 3) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win5 w (by rw [h5]; decide) (by rw [h2, h3]; decide)
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact part23 w h2 h3 h5
  · exact part27 w h2 h3 h5

private theorem part29 (w : ℕ → ZMod 4) (h2 : w 2 = 1) : goal w := by
  rcases cases4 (w 3) with h3 | h3 | h3 | h3
  · exact part8 w h2 h3
  · exact part18 w h2 h3
  · exact part20 w h2 h3
  · exact part28 w h2 h3

private theorem part30 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 1) (h17 : w 17 = 1) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win441 w (by rw [h3, h7]; decide) (by rw [h2, h13, h17]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win64 w (by rw [h2]; decide) (by rw [h5, h13]; decide)

private theorem part31 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 1) (h17 : w 17 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact part30 w h2 h3 h5 h17 h7
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact win119 w (by rw [h7, h17]; decide) (by rw [h2, h3, h5]; decide)

private theorem part32 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact part31 w h2 h3 h5 h17
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact win50 w (by rw [h2, h5]; decide) (by rw [h3, h17]; decide)

private theorem part33 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) (h13 : w 13 = 1) (h7 : w 7 = 1) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 41) with h41 | h41 | h41 | h41
  · exact win40 w (by rw [h2, h5]; decide) (by rw [h41]; decide)
  · exact win245 w (by rw [h5, h7]; decide) (by rw [h2, h3, h41]; decide)
  · exact win81 w (by decide) (by rw [h2, h41]; decide)
  · exact win286 w (by rw [h2, h11, h13]; decide) (by rw [h7, h41]; decide)

private theorem part34 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) (h13 : w 13 = 1) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact part33 w h2 h3 h5 h13 h7 h11
  · exact win98 w (by rw [h2, h7]; decide) (by rw [h3, h11]; decide)
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)

private theorem part35 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) (_h13 : w 13 = 1) (h7 : w 7 = 3) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win33 w (by rw [h3, h11]; decide) (by rw [h2, h17]; decide)
  · exact win594 w (by rw [h2, h3, h11]; decide) (by rw [h5, h7, h17]; decide)

private theorem part36 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) (h13 : w 13 = 1) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)
  · exact win21 w (by rw [h3, h7]; decide) (by rw [h2, h11]; decide)
  · exact part35 w h2 h3 h5 h13 h7 h11

private theorem part37 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) (h13 : w 13 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win195 w (by rw [h3, h5, h13]; decide) (by rw [h2, h7]; decide)
  · exact part34 w h2 h3 h5 h13 h7
  · exact win63 w (by rw [h3, h7]; decide) (by rw [h2]; decide)
  · exact part36 w h2 h3 h5 h13 h7

private theorem part38 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win324 w (by rw [h2]; decide) (by rw [h5, h13]; decide)
  · exact part37 w h2 h3 h5 h13
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)

private theorem part39 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 1) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win4 w (by rw [h2]; decide) (by rw [h5]; decide)
  · exact part32 w h2 h3 h5
  · exact part38 w h2 h3 h5
  · exact win15 w (by rw [h3, h5]; decide) (by decide)

private theorem part40 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 2) (h5 : w 5 = 1) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)
  · exact win728 w (by rw [h2, h7, h13]; decide) (by rw [h3]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)
  · exact win64 w (by rw [h2]; decide) (by rw [h5, h13]; decide)

private theorem part41 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 2) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact part40 w h2 h3 h5 h7
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)

private theorem part42 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 2) (h5 : w 5 = 3) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)
  · exact win64 w (by rw [h2]; decide) (by rw [h5, h13]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)
  · exact win728 w (by rw [h2, h7, h13]; decide) (by rw [h3]; decide)

private theorem part43 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 2) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact part42 w h2 h3 h5 h7

private theorem part44 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 2) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win4 w (by rw [h2]; decide) (by rw [h5]; decide)
  · exact part41 w h2 h3 h5
  · exact win9 w (by rw [h3]; decide) (by rw [h2, h5]; decide)
  · exact part43 w h2 h3 h5

private theorem part45 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) (_h13 : w 13 = 3) (h7 : w 7 = 1) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win594 w (by rw [h2, h3, h11]; decide) (by rw [h5, h7, h17]; decide)
  · exact win33 w (by rw [h3, h11]; decide) (by rw [h2, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)

private theorem part46 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) (h13 : w 13 = 3) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact part45 w h2 h3 h5 h13 h7 h11
  · exact win21 w (by rw [h3, h7]; decide) (by rw [h2, h11]; decide)
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)

private theorem part47 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) (h13 : w 13 = 3) (h7 : w 7 = 3) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 41) with h41 | h41 | h41 | h41
  · exact win40 w (by rw [h2, h5]; decide) (by rw [h41]; decide)
  · exact win286 w (by rw [h2, h11, h13]; decide) (by rw [h7, h41]; decide)
  · exact win81 w (by decide) (by rw [h2, h41]; decide)
  · exact win245 w (by rw [h5, h7]; decide) (by rw [h2, h3, h41]; decide)

private theorem part48 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) (h13 : w 13 = 3) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)
  · exact win98 w (by rw [h2, h7]; decide) (by rw [h3, h11]; decide)
  · exact part47 w h2 h3 h5 h13 h7 h11

private theorem part49 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) (h13 : w 13 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win195 w (by rw [h3, h5, h13]; decide) (by rw [h2, h7]; decide)
  · exact part46 w h2 h3 h5 h13 h7
  · exact win63 w (by rw [h3, h7]; decide) (by rw [h2]; decide)
  · exact part48 w h2 h3 h5 h13 h7

private theorem part50 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win324 w (by rw [h2]; decide) (by rw [h5, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)
  · exact part49 w h2 h3 h5 h13

private theorem part51 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 3) (h17 : w 17 = 3) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win64 w (by rw [h2]; decide) (by rw [h5, h13]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win441 w (by rw [h3, h7]; decide) (by rw [h2, h13, h17]; decide)

private theorem part52 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 3) (h17 : w 17 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact win119 w (by rw [h7, h17]; decide) (by rw [h2, h3, h5]; decide)
  · exact win49 w (by rw [h7]; decide) (by rw [h2, h5]; decide)
  · exact part51 w h2 h3 h5 h17 h7

private theorem part53 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win50 w (by rw [h2, h5]; decide) (by rw [h3, h17]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)
  · exact part52 w h2 h3 h5 h17

private theorem part54 (w : ℕ → ZMod 4) (h2 : w 2 = 2) (h3 : w 3 = 3) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win4 w (by rw [h2]; decide) (by rw [h5]; decide)
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact part50 w h2 h3 h5
  · exact part53 w h2 h3 h5

private theorem part55 (w : ℕ → ZMod 4) (h2 : w 2 = 2) : goal w := by
  rcases cases4 (w 3) with h3 | h3 | h3 | h3
  · exact win3 w (by rw [h3]; decide) (by rw [h2]; decide)
  · exact part39 w h2 h3
  · exact part44 w h2 h3
  · exact part54 w h2 h3

private theorem part56 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 2) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)

private theorem part57 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win20 w (by rw [h2, h5]; decide) (by rw [h3, h7]; decide)
  · exact win224 w (by rw [h2, h7]; decide) (by rw [h3, h5]; decide)
  · exact win27 w (by rw [h3]; decide) (by rw [h2, h7]; decide)
  · exact part56 w h2 h3 h5 h7

private theorem part58 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 3) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win13 w (by rw [h13]; decide) (by rw [h2, h7]; decide)
  · exact win26 w (by rw [h2, h13]; decide) (by rw [h3]; decide)
  · exact win728 w (by rw [h2, h7, h13]; decide) (by rw [h3]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)

private theorem part59 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 3) (h7 : w 7 = 3) (h13 : w 13 = 3) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win119 w (by rw [h7, h17]; decide) (by rw [h2, h3, h5]; decide)
  · exact win935 w (by rw [h5, h11, h17]; decide) (by rw [h2, h3, h13]; decide)
  · exact win1224 w (by rw [h2, h3, h17]; decide) (by rw [h5, h7]; decide)

private theorem part60 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 3) (h7 : w 7 = 3) (h13 : w 13 = 3) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact win55 w (by rw [h5, h11]; decide) (by rw [h2, h7]; decide)
  · exact win120 w (by rw [h2, h3, h5]; decide) (by rw [h11]; decide)
  · exact part59 w h2 h3 h5 h7 h13 h11

private theorem part61 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 3) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win26 w (by rw [h2, h13]; decide) (by rw [h3]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact part60 w h2 h3 h5 h7 h13

private theorem part62 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win48 w (by rw [h3]; decide) (by rw [h7]; decide)
  · exact part58 w h2 h3 h5 h7
  · exact win27 w (by rw [h3]; decide) (by rw [h2, h7]; decide)
  · exact part61 w h2 h3 h5 h7

private theorem part63 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 0) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact win9 w (by rw [h3]; decide) (by rw [h2, h5]; decide)
  · exact part57 w h2 h3 h5
  · exact part62 w h2 h3 h5

private theorem part64 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 2) (h11 : w 11 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win351 w (by rw [h3, h13]; decide) (by rw [h2, h11]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)

private theorem part65 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 2) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win33 w (by rw [h3, h11]; decide) (by rw [h2, h17]; decide)
  · exact win153 w (by rw [h3, h17]; decide) (by rw [h2, h7, h11]; decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)

private theorem part66 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 1) (h7 : w 7 = 2) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win10 w (by rw [h2, h5]; decide) (by rw [h11]; decide)
  · exact part64 w h2 h3 h5 h7 h11
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact part65 w h2 h3 h5 h7 h11

private theorem part67 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 1) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact win224 w (by rw [h2, h7]; decide) (by rw [h3, h5]; decide)
  · exact part66 w h2 h3 h5 h7
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)

private theorem part68 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 2) (h7 : w 7 = 1) (h13 : w 13 = 2) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win84 w (by rw [h2, h3, h7]; decide) (by rw [h5, h17]; decide)
  · exact win51 w (by rw [h3, h17]; decide) (by rw [h2, h13]; decide)

private theorem part69 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 2) (h7 : w 7 = 1) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win13 w (by rw [h13]; decide) (by rw [h2, h7]; decide)
  · exact win25 w (by rw [h5]; decide) (by rw [h2, h13]; decide)
  · exact part68 w h2 h3 h5 h7 h13
  · exact win104 w (by rw [h2, h13]; decide) (by rw [h3, h5, h7]; decide)

private theorem part70 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) (h5 : w 5 = 2) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact win6 w (by rw [h2, h3]; decide) (by rw [h7]; decide)
  · exact part69 w h2 h3 h5 h7
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)
  · exact win20 w (by rw [h2, h5]; decide) (by rw [h3, h7]; decide)

private theorem part71 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 1) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win5 w (by rw [h5]; decide) (by rw [h2, h3]; decide)
  · exact part67 w h2 h3 h5
  · exact part70 w h2 h3 h5
  · exact win15 w (by rw [h3, h5]; decide) (by decide)

private theorem part72 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 2) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win12 w (by rw [h2, h3]; decide) (by rw [h13]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win675 w (by rw [h3, h5]; decide) (by rw [h2, h13]; decide)

private theorem part73 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 2) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win80 w (by rw [h5]; decide) (by decide)
  · exact win9 w (by rw [h3]; decide) (by rw [h2, h5]; decide)
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact part72 w h2 h3 h5

private theorem part74 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (_h7 : w 7 = 0) (h11 : w 11 = 0) (_h13 : w 13 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win374 w (by rw [h2, h11, h17]; decide) (by rw [h3, h5]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)

private theorem part75 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 0) (h11 : w 11 = 0) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win90 w (by rw [h2, h3, h5]; decide) (by rw [h7, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win77 w (by rw [h7, h11]; decide) (by rw [h2, h3, h13]; decide)
  · exact part74 w h2 h3 h5 h7 h11 h13

private theorem part76 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (_h7 : w 7 = 0) (h11 : w 11 = 3) (h13 : w 13 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win220 w (by rw [h2, h5, h11]; decide) (by rw [h13, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)

private theorem part77 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 0) (h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 13) with h13 | h13 | h13 | h13
  · exact win90 w (by rw [h2, h3, h5]; decide) (by rw [h7, h13]; decide)
  · exact win39 w (by rw [h3, h13]; decide) (by rw [h2, h5]; decide)
  · exact win168 w (by rw [h2, h3, h7]; decide) (by rw [h13]; decide)
  · exact part76 w h2 h3 h5 h7 h11 h13

private theorem part78 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 0) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact part75 w h2 h3 h5 h7 h11
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact part77 w h2 h3 h5 h7 h11

private theorem part79 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 2) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win175 w (by rw [h5, h7]; decide) (by rw [h11]; decide)
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact win384 w (by rw [h2, h3]; decide) (by rw [h5, h7, h11]; decide)

private theorem part80 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 3) (_h11 : w 11 = 3) : goal w := by
  rcases cases4 (w 17) with h17 | h17 | h17 | h17
  · exact win16 w (by decide) (by rw [h17]; decide)
  · exact win84 w (by rw [h2, h3, h7]; decide) (by rw [h5, h17]; decide)
  · exact win255 w (by rw [h3, h5, h17]; decide) (by decide)
  · exact win135 w (by rw [h3, h5]; decide) (by rw [h2, h17]; decide)

private theorem part81 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) (h7 : w 7 = 3) : goal w := by
  rcases cases4 (w 11) with h11 | h11 | h11 | h11
  · exact win440 w (by rw [h2, h5, h11]; decide) (by rw [h3, h7]; decide)
  · exact win54 w (by rw [h2, h3]; decide) (by rw [h5, h11]; decide)
  · exact win99 w (by rw [h3, h11]; decide) (by rw [h2, h5]; decide)
  · exact part80 w h2 h3 h5 h7 h11

private theorem part82 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) (h5 : w 5 = 3) : goal w := by
  rcases cases4 (w 7) with h7 | h7 | h7 | h7
  · exact part78 w h2 h3 h5 h7
  · exact win35 w (by rw [h5, h7]; decide) (by rw [h2, h3]; decide)
  · exact part79 w h2 h3 h5 h7
  · exact part81 w h2 h3 h5 h7

private theorem part83 (w : ℕ → ZMod 4) (h2 : w 2 = 3) (h3 : w 3 = 3) : goal w := by
  rcases cases4 (w 5) with h5 | h5 | h5 | h5
  · exact win24 w (by rw [h2, h3]; decide) (by rw [h5]; decide)
  · exact win15 w (by rw [h3, h5]; decide) (by decide)
  · exact win24 w (by rw [h2, h3]; decide) (by rw [h5]; decide)
  · exact part82 w h2 h3 h5

private theorem part84 (w : ℕ → ZMod 4) (h2 : w 2 = 3) : goal w := by
  rcases cases4 (w 3) with h3 | h3 | h3 | h3
  · exact part63 w h2 h3
  · exact part71 w h2 h3
  · exact part73 w h2 h3
  · exact part83 w h2 h3

private theorem part85 (w : ℕ → ZMod 4)  : goal w := by
  rcases cases4 (w 2) with h2 | h2 | h2 | h2
  · exact win1 w (by decide) (by rw [h2]; decide)
  · exact part29 w h2
  · exact part55 w h2
  · exact part84 w h2

end OMA.QuarticCases

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  intro w
  exact OMA.QuarticCases.part85 w
