import OMAReductions.R_oeis_a227864_R1

/-!
Every prime square in the stated range has a two-digit base expansion whose
reversal is prime. Each table entry is a base. A zero entry marks a composite
input, which is checked using its least prime factor.
-/
namespace ReversedSquares
open OMA.S_oeis_a227864 OMA.R_oeis_a227864_R1

private def reversedValue (p b : ℕ) : ℕ := (p ^ 2 % b) * b + p ^ 2 / b

private def check (p b : ℕ) : Bool :=
  if b = 0 then decide (p.minFac < p)
  else decide (p < b ∧ b ≤ p ^ 2 ∧ 2 ≤ reversedValue p b ∧
    (reversedValue p b).minFac = reversedValue p b)

private def checkList (lo : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => check lo b && checkList (lo + 1) bs

private def Covers (lo hi : ℕ) := ∀ p, lo ≤ p → p < hi → p.Prime →
  ∃ b : ℕ, 2 ≤ b ∧ (reversal b (p ^ 2)).Prime

private lemma verifyEntry {p b : ℕ} (hp : p.Prime) (h : check p b = true) :
    ∃ c : ℕ, 2 ≤ c ∧ (reversal c (p ^ 2)).Prime := by
  unfold check at h
  split at h
  · simp [hp.minFac_eq] at h
  · obtain ⟨lt, le, two, eq⟩ := of_decide_eq_true h
    refine ⟨b, hp.two_le.trans (Nat.le_of_lt lt), ?_⟩
    rw [two_digit_reversal p b hp.two_le lt le]
    exact Nat.prime_def_minFac.mpr ⟨two, eq⟩

private lemma coverList (lo : ℕ) (bs : List ℕ) (h : checkList lo bs = true) :
    Covers lo (lo + bs.length) := by
  induction bs generalizing lo with
  | nil => intro p hl hu; simp at hu; omega
  | cons b bs ih =>
    simp only [checkList, Bool.and_eq_true] at h
    intro p hl hu hp
    by_cases heq : p = lo
    · subst p
      exact verifyEntry hp h.1
    · apply ih (lo + 1) h.2 p (by omega) _ hp
      simp only [List.length_cons] at hu
      omega

private lemma join {lo mid hi : ℕ} (h₁ : Covers lo mid) (h₂ : Covers mid hi) : Covers lo hi :=
  fun p hl hu hp => if h : p < mid then h₁ p hl h hp else h₂ p (by omega) hu hp

private lemma block0 : Covers 3 67 :=
  coverList 3 [6, 0, 8, 0, 16, 0, 0, 0, 15, 0, 21, 0, 0, 0, 32, 0, 45, 0, 0, 0, 48, 0, 0, 0, 0, 0, 35, 0, 64, 0, 0, 0, 0, 0, 171, 0, 0, 0, 48, 0, 56, 0, 0, 0, 69, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 87, 0, 120, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block1 : Covers 67 131 :=
  coverList 67 [88, 0, 0, 0, 112, 0, 144, 0, 0, 0, 0, 0, 160, 0, 0, 0, 123, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 147, 0, 0, 0, 136, 0, 221, 0, 0, 0, 216, 0, 135, 0, 0, 0, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0] (by decide +kernel)

private lemma block2 : Covers 131 195 :=
  coverList 131 [143, 0, 0, 0, 0, 0, 368, 0, 161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200, 0, 304, 0, 0, 0, 0, 0, 1027, 0, 0, 0, 0, 0, 328, 0, 0, 0, 336, 0, 0, 0, 0, 0, 344, 0, 0, 0, 0, 0, 360, 0, 280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 384, 0, 291, 0] (by decide +kernel)

private lemma block3 : Covers 195 259 :=
  coverList 195 [0, 0, 392, 0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 265, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1344, 0, 0, 0, 339, 0, 437, 0, 0, 0, 377, 0, 0, 0, 0, 0, 255, 0, 363, 0, 0, 0, 0, 0, 0, 0, 0, 0, 875, 0, 0, 0, 0, 0, 512, 0] (by decide +kernel)

private lemma block4 : Covers 259 323 :=
  coverList 259 [0, 0, 0, 0, 393, 0, 0, 0, 0, 0, 2680, 0, 459, 0, 0, 0, 0, 0, 417, 0, 0, 0, 329, 0, 568, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 504, 0, 0, 0, 403, 0, 315, 0, 0, 0, 424, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block5 : Covers 323 387 :=
  coverList 323 [0, 0, 0, 0, 0, 0, 0, 0, 664, 0, 0, 0, 0, 0, 1183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 519, 0, 525, 0, 0, 0, 704, 0, 0, 0, 0, 0, 895, 0, 0, 0, 0, 0, 0, 0, 736, 0, 0, 0, 0, 0, 561, 0, 0, 0, 0, 0, 665, 0, 0, 0, 573, 0, 0, 0] (by decide +kernel)

private lemma block6 : Covers 387 451 :=
  coverList 387 [0, 0, 485, 0, 0, 0, 0, 0, 0, 0, 792, 0, 0, 0, 403, 0, 0, 0, 0, 0, 0, 0, 615, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 0, 840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1161, 0, 837, 0, 0, 0, 0, 0, 2640, 0, 0, 0, 629, 0, 0, 0, 0, 0, 1152, 0] (by decide +kernel)

private lemma block7 : Covers 451 515 :=
  coverList 451 [0, 0, 0, 0, 0, 0, 687, 0, 0, 0, 552, 0, 672, 0, 0, 0, 506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 511, 0, 0, 0, 0, 0, 0, 0, 489, 0, 0, 0, 735, 0, 0, 0, 0, 0, 0, 0, 664, 0, 0, 0, 1008, 0, 0, 0, 0, 0, 680, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block8 : Covers 515 579 :=
  coverList 515 [0, 0, 0, 0, 0, 0, 585, 0, 525, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1355, 0, 0, 0, 0, 0, 1781, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1251, 0, 0, 0, 0, 0, 1128, 0, 0, 0, 0, 0, 1520, 0, 715, 0, 0, 0, 0, 0, 2601, 0] (by decide +kernel)

private lemma block9 : Covers 579 643 :=
  coverList 579 [0, 0, 0, 0, 0, 0, 0, 0, 855, 0, 0, 0, 0, 0, 1184, 0, 0, 0, 0, 0, 897, 0, 688, 0, 0, 0, 0, 0, 1919, 0, 0, 0, 0, 0, 1224, 0, 0, 0, 721, 0, 744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 768, 0] (by decide +kernel)

private lemma block10 : Covers 643 707 :=
  coverList 643 [749, 0, 0, 0, 1296, 0, 0, 0, 0, 0, 872, 0, 0, 0, 0, 0, 705, 0, 993, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1011, 0, 0, 0, 679, 0, 0, 0, 0, 0, 792, 0, 0, 0, 0, 0, 0, 0, 920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2457, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block11 : Covers 707 771 :=
  coverList 707 [0, 0, 885, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1795, 0, 0, 0, 0, 0, 0, 0, 847, 0, 0, 0, 0, 0, 1464, 0, 0, 0, 0, 0, 1517, 0, 0, 0, 848, 0, 0, 0, 0, 0, 0, 0, 1504, 0, 0, 0, 0, 0, 3032, 0, 0, 0, 1520, 0, 0, 0, 0, 0, 0, 0, 1155, 0] (by decide +kernel)

private lemma block12 : Covers 771 835 :=
  coverList 771 [0, 0, 1544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1034, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1296, 0, 1015, 0, 0, 0, 0, 0, 0, 0, 0, 0, 984, 0, 1417, 0, 0, 0, 1357, 0, 920, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block13 : Covers 835 899 :=
  coverList 835 [0, 0, 0, 0, 1680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1491, 0, 0, 0, 1177, 0, 1032, 0, 0, 0, 2595, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1317, 0, 0, 0, 1440, 0, 1224, 0, 0, 0, 889, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block14 : Covers 899 963 :=
  coverList 899 [0, 0, 0, 0, 0, 0, 0, 0, 1208, 0, 0, 0, 1120, 0, 0, 0, 0, 0, 0, 0, 2160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 931, 0, 0, 0, 0, 0, 0, 0, 1008, 0, 0, 0, 1128, 0, 0, 0, 0, 0, 1032, 0, 0, 0, 0, 0, 1904, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block15 : Covers 963 1027 :=
  coverList 963 [0, 0, 0, 0, 1104, 0, 0, 0, 973, 0, 0, 0, 0, 0, 1952, 0, 0, 0, 0, 0, 1473, 0, 0, 0, 0, 0, 0, 0, 1395, 0, 0, 0, 0, 0, 1497, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1120, 0, 0, 0, 1352, 0, 0, 0, 0, 0, 1527, 0, 1241, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block16 : Covers 1027 1091 :=
  coverList 1027 [0, 0, 0, 0, 1648, 0, 1551, 0, 0, 0, 0, 0, 1248, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2096, 0, 1841, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2360, 0, 1121, 0, 0, 0, 0, 0, 2136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2176, 0, 0, 0] (by decide +kernel)

private lemma block17 : Covers 1091 1155 :=
  coverList 1091 [1365, 0, 2184, 0, 0, 0, 2192, 0, 0, 0, 0, 0, 1311, 0, 0, 0, 0, 0, 1385, 0, 0, 0, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 1496, 0, 0, 0, 0, 0, 1695, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304, 0, 5193, 0] (by decide +kernel)

private lemma block18 : Covers 1155 1219 :=
  coverList 1155 [0, 0, 0, 0, 0, 0, 0, 0, 1992, 0, 0, 0, 0, 0, 0, 0, 4680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4728, 0, 0, 0, 0, 0, 2376, 0, 0, 0, 0, 0, 3184, 0, 0, 0, 0, 0, 0, 0, 2400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2111, 0, 0, 0, 1653, 0] (by decide +kernel)

private lemma block19 : Covers 1219 1283 :=
  coverList 1219 [0, 0, 0, 0, 1872, 0, 0, 0, 0, 0, 4605, 0, 1312, 0, 0, 0, 0, 0, 4952, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2059, 0, 2552, 0, 0, 0] (by decide +kernel)

private lemma block20 : Covers 1283 1347 :=
  coverList 1283 [2568, 0, 0, 0, 0, 0, 1505, 0, 1615, 0, 0, 0, 0, 0, 1299, 0, 0, 0, 1400, 0, 2608, 0, 0, 0, 1595, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1977, 0, 2640, 0, 0, 0, 0, 0, 1411, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block21 : Covers 1347 1411 :=
  coverList 1347 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1632, 0, 0, 0, 0, 0, 6147, 0, 0, 0, 0, 0, 1832, 0, 0, 0, 0, 0, 0, 0, 3455, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3840, 0] (by decide +kernel)

private lemma block22 : Covers 1411 1475 :=
  coverList 1411 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2528, 0, 0, 0, 1736, 0, 1496, 0, 0, 0, 2864, 0, 0, 0, 0, 0, 6471, 0, 0, 0, 0, 0, 0, 0, 8688, 0, 0, 0, 5800, 0, 2904, 0, 0, 0, 0, 0, 3645, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3381, 0, 0, 0] (by decide +kernel)

private lemma block23 : Covers 1475 1539 :=
  coverList 1475 [0, 0, 0, 0, 0, 0, 1520, 0, 1729, 0, 0, 0, 2229, 0, 4619, 0, 0, 0, 3357, 0, 0, 0, 0, 0, 5992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2283, 0, 0, 0, 0, 0, 0, 0, 3447, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block24 : Covers 1539 1603 :=
  coverList 1539 [0, 0, 0, 0, 4112, 0, 0, 0, 0, 0, 2232, 0, 0, 0, 2037, 0, 0, 0, 0, 0, 1599, 0, 0, 0, 0, 0, 0, 0, 3136, 0, 0, 0, 1965, 0, 0, 0, 0, 0, 0, 0, 1581, 0, 0, 0, 2016, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2261, 0, 0, 0, 3200, 0] (by decide +kernel)

private lemma block25 : Covers 1603 1667 :=
  coverList 1603 [0, 0, 0, 0, 3216, 0, 1680, 0, 0, 0, 2152, 0, 0, 0, 0, 0, 3240, 0, 3240, 0, 0, 0, 0, 0, 2168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7461, 0, 0, 0, 0, 0, 3328, 0, 0, 0] (by decide +kernel)

private lemma block26 : Covers 1667 1731 :=
  coverList 1667 [2363, 0, 2505, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2961, 0, 0, 0, 3392, 0, 2264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2064, 0, 3017, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block27 : Covers 1731 1795 :=
  coverList 1731 [0, 0, 6936, 0, 0, 0, 0, 0, 0, 0, 3016, 0, 0, 0, 0, 0, 1843, 0, 0, 0, 0, 0, 14032, 0, 0, 0, 0, 0, 4395, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2667, 0, 0, 0, 0, 0, 2055, 0, 0, 0, 7003, 0, 2685, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block28 : Covers 1795 1859 :=
  coverList 1795 [0, 0, 0, 0, 0, 0, 3825, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2715, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3320, 0, 0, 0, 0, 0, 0, 0, 2928, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block29 : Covers 1859 1923 :=
  coverList 1859 [0, 0, 1960, 0, 0, 0, 0, 0, 2488, 0, 0, 0, 2720, 0, 8433, 0, 0, 0, 2504, 0, 2256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2065, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3800, 0, 0, 0, 0, 0, 7624, 0, 0, 0, 0, 0, 2629, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block30 : Covers 1923 1987 :=
  coverList 1923 [0, 0, 0, 0, 0, 0, 0, 0, 2760, 0, 3864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3896, 0, 2496, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2397, 0, 0, 0, 0, 0, 2365, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel)

private lemma block31 : Covers 1987 2001 :=
  coverList 1987 [2317, 0, 0, 0, 0, 0, 2715, 0, 0, 0, 18463, 0, 4000, 0] (by decide +kernel)

private lemma allCases : Covers 3 2001 :=
  (join (join (join (join (join block0 block1) (join block2 block3)) (join (join block4 block5) (join block6 block7))) (join (join (join block8 block9) (join block10 block11)) (join (join block12 block13) (join block14 block15)))) (join (join (join (join block16 block17) (join block18 block19)) (join (join block20 block21) (join block22 block23))) (join (join (join block24 block25) (join block26 block27)) (join (join block28 block29) (join block30 block31)))))

end ReversedSquares

theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  intro p hl hu hp
  exact ReversedSquares.allCases p hl (by omega) hp
