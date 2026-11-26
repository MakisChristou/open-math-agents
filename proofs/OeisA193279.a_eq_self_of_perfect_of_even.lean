import FormalConjectures.OEIS.«193279»

/-! Every integer up to an even perfect number is a sum of distinct proper divisors.
Write the number as a power of two times a Mersenne prime. The quotient
and remainder on division by that prime can each be expanded in binary. -/

namespace OMA.PerfectDivisors

open Finset ArithmeticFunction
open scoped sigma

/- The following three lemmas are from Aaron Anderson's Euclid–Euler proof in
Mathlib, Archive/Wiedijk100Theorems/PerfectNumbers.lean.
Copyright (c) 2020 Aaron Anderson. Released under the Apache 2.0 license. -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
  power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

lemma binary_repr (k v : ℕ) (hv : v < 2 ^ k) :
    ∃ s : Finset ℕ, (∀ x ∈ s, ∃ i < k, x = 2 ^ i) ∧ ∑ x ∈ s, x = v := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    exact ⟨∅, by simp, by simp [this]⟩
  | succ k ih =>
    by_cases h : v < 2 ^ k
    · obtain ⟨s, hs, rfl⟩ := ih v h
      refine ⟨s, ?_, rfl⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hs x hx
      exact ⟨i, by omega, rfl⟩
    · have hrem : v - 2 ^ k < 2 ^ k := by rw [pow_succ] at hv; omega
      obtain ⟨s, hs, hsum⟩ := ih _ hrem
      have hnew : 2 ^ k ∉ s := by
        intro hx
        obtain ⟨i, hi, he⟩ := hs _ hx
        exact (Nat.pow_lt_pow_right (by decide : 1 < 2) hi).ne he.symm
      refine ⟨insert (2 ^ k) s, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact ⟨k, by omega, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := hs _ hx
          exact ⟨i, by omega, rfl⟩
      · rw [sum_insert hnew, hsum]
        omega

lemma represent {k m v : ℕ} (hm : m = 2 ^ (k+1) - 1) (hbig : 2 ^ k < m)
    (hv : v < 2 ^ k * m) :
    ∃ s ⊆ (2 ^ k * m).properDivisors, ∑ x ∈ s, x = v := by
  have hmpos : 0 < m := lt_trans (by positivity : 0 < (2:ℕ)^k) hbig
  have hrem : v % m < 2 ^ (k+1) := lt_of_lt_of_le (Nat.mod_lt _ hmpos) (by omega)
  have hquot : v / m < 2 ^ k := (Nat.div_lt_iff_lt_mul hmpos).mpr hv
  obtain ⟨r, hr, hsr⟩ := binary_repr _ _ hrem
  obtain ⟨q, hq, hsq⟩ := binary_repr _ _ hquot
  let scale : ℕ ↪ ℕ := ⟨(m * ·), fun _ _ he => Nat.eq_of_mul_eq_mul_left hmpos he⟩
  have hrsmall (x) (hx : x ∈ r) : x ≤ 2 ^ k := by
    obtain ⟨i, hi, rfl⟩ := hr _ hx
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsep : Disjoint r (q.map scale) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx'
    obtain ⟨i, hi, rfl⟩ := hq _ hy
    have hle := hrsmall _ hx
    change m * 2 ^ i ≤ 2 ^ k at hle
    have hp : 0 < (2:ℕ)^i := by positivity
    nlinarith
  refine ⟨r ∪ q.map scale, ?_, ?_⟩
  · intro x hx
    apply Nat.mem_properDivisors.mpr
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := hr _ hx
      have hle : i ≤ k := by omega
      refine ⟨dvd_mul_of_dvd_left (pow_dvd_pow 2 hle) m, ?_⟩
      have hsize := Nat.pow_le_pow_right (by decide : 0 < 2) hle
      have hp : 0 < (2:ℕ)^k := by positivity
      nlinarith
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      obtain ⟨i, hi, rfl⟩ := hq _ hy
      change m * 2 ^ i ∣ 2 ^ k * m ∧ m * 2 ^ i < 2 ^ k * m
      rw [Nat.mul_comm m]
      exact ⟨mul_dvd_mul_right (pow_dvd_pow 2 hi.le) _,
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) hi) hmpos⟩
  · rw [sum_union hsep, sum_map]
    change (∑ x ∈ r, x) + ∑ x ∈ q, m * x = v
    rw [← mul_sum, hsr, hsq, Nat.mod_add_div]

end OMA.PerfectDivisors

open Finset OMA.PerfectDivisors in
theorem OMA.solution : type_of% @OeisA193279.a_eq_self_of_perfect_of_even := by
  intro n hp he
  obtain ⟨k, hmprime, hn⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  let m := mersenne (k+1)
  have hshape : n = 2 ^ k * m := hn
  have hm : m = 2 ^ (k+1) - 1 := rfl
  have hm2 : 2 ≤ m := hmprime.two_le
  have hbig : 2 ^ k < m := by rw [pow_succ] at hm; omega
  have htotal := (Nat.perfect_iff_sum_properDivisors hp.2).mp hp
  have hall : n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x) = range (n+1) := by
    ext v
    simp only [mem_image, mem_powerset, mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hle : ∑ x ∈ s, x ≤ ∑ x ∈ n.properDivisors, x := sum_le_sum_of_subset hs
      omega
    · intro hv
      by_cases h : v = n
      · exact ⟨n.properDivisors, Subset.rfl, htotal.trans h.symm⟩
      · have hlt : v < 2 ^ k * m := by omega
        obtain ⟨s, hs, hs'⟩ := represent hm hbig hlt
        exact ⟨s, hshape ▸ hs, hs'⟩
  simp [OeisA193279.a, hall]
