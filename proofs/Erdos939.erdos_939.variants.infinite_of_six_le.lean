import FormalConjectures.ErdosProblems.«939»
import Mathlib.Data.Nat.Choose.Sum

/-! Put d = 2(r-3). Subtracting the two binomial expansions of (X+1)^d
and (X-1)^d leaves exactly r-3 odd powers of X. Take X to be a large
r-th power of a multiple of every coefficient. Each odd-power term is
then r-powerful and coprime to (X-1)^d. The latter supplies the final
summand. Increasing X gives unbounded solutions.

This specializes the binomial construction recorded in the Erdős 939
forum. The choice of an even exponent avoids subdividing any summand. -/

namespace OMA.Powerful
open Finset Erdos939

def coeff (L i : ℕ) := 2 * (2*L).choose (2*i+1)
def term (L X i : ℕ) := coeff L i * X^(2*i+1)

lemma odd_sum (L : ℕ) (f : ℕ → ℤ) (he : ∀ i, f (2*i) = 0) :
    ∑ k ∈ range (2*L+1), f k = ∑ i ∈ range L, f (2*i+1) := by
  induction L with
  | zero => simpa using he 0
  | succ L ih =>
    rw [show 2*(L+1)+1 = (2*L+1+1)+1 by omega, sum_range_succ, sum_range_succ,
      show 2*L+1+1=2*(L+1) by omega, he, add_zero, ih, sum_range_succ]

lemma binomial (L X : ℕ) (hX : 1 ≤ X) :
    (X-1)^(2*L) + ∑ i ∈ range L, term L X i = (X+1)^(2*L) := by
  let z := (X:ℤ)
  let f (k : ℕ) := (z^k - (-z)^k) * ((2*L).choose k : ℤ)
  have ev (i : ℕ) : f (2*i) = 0 := by simp [f,pow_mul]
  have od (i : ℕ) : f (2*i+1) = (term L X i : ℤ) := by
    simp [f,term,coeff,z,pow_succ,pow_mul]
    ring
  have e : (z+1)^(2*L) - (-z+1)^(2*L) = ∑ k ∈ range (2*L+1), f k := by
    rw [add_pow,add_pow,← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    simp [f]
    ring
  rw [odd_sum L f ev] at e
  simp_rw [od] at e
  have neg : (-z+1)^(2*L) = (z-1)^(2*L) := by
    rw [show -z+1 = -(z-1) by ring]
    rw [pow_mul,pow_mul,neg_sq]
  rw [neg] at e
  zify [hX]
  dsimp [z] at e
  linarith only [e]

lemma full_pow {d r x : ℕ} (hr : r ≤ d) : r.Full (x^d) := by
  intro p hp
  have h := (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp)
  exact (pow_dvd_pow_of_dvd h r).trans (pow_dvd_pow x hr)

lemma full_term {c w r j : ℕ} (hc : c ∣ w) (hj : j ≠ 0) : r.Full (c*(w^r)^j) := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pw : p ∣ w := by
    rcases pp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact h.trans hc
    · exact pp.dvd_of_dvd_pow (pp.dvd_of_dvd_pow h)
  exact (pow_dvd_pow_of_dvd pw r).trans ((dvd_pow_self _ hj).trans (dvd_mul_left _ _))

lemma coeff_pos {L i : ℕ} (hi : i < L) : 0 < coeff L i :=
  Nat.mul_pos (by decide) (Nat.choose_pos (by omega))

lemma large {r : ℕ} (hr : 6 ≤ r) (T : ℕ) :
    ∃ S ∈ Erdos939Sums r, ∃ m ∈ S, T < m := by
  classical
  let L := r-3
  let B := ∏ i ∈ range L, coeff L i
  let w := B*(T+2)
  let X := w^r
  let A := (X-1)^(2*L)
  let vals := (range L).image (term L X)
  let S := insert A vals
  have hL : 0 < L := by dsimp [L]; omega
  have hdeg : r ≤ 2*L := by dsimp [L]; omega
  have bp : 0 < B := Finset.prod_pos (fun i hi => coeff_pos (mem_range.mp hi))
  have cpos {i : ℕ} (hi : i < L) := coeff_pos hi
  have divides {i : ℕ} (hi : i < L) : coeff L i ∣ B := Finset.dvd_prod_of_mem _ (mem_range.mpr hi)
  have wb : B < w := by dsimp [w]; nlinarith
  have wt : T < w := by dsimp [w]; nlinarith
  have wx : w ≤ X := Nat.le_self_pow (by omega : r ≠ 0) w
  have xbig : 1 < X := by omega
  have leterm {i : ℕ} (hi : i < L) : X ≤ term L X i :=
    (Nat.le_self_pow (by omega : 2*i+1 ≠ 0) X).trans
      (Nat.le_mul_of_pos_left _ (cpos hi))
  have cw {i : ℕ} (hi : i < L) : coeff L i ∣ w := (divides hi).trans (dvd_mul_right _ _)
  have copX : (X-1).Coprime X := (Nat.coprime_self_sub_left (by omega)).mpr (Nat.coprime_one_left X)
  have cop {i : ℕ} (hi : i < L) : A.Coprime (term L X i) := by
    have cx := (cw hi).trans (dvd_pow_self w (by omega : r ≠ 0))
    have hc := Nat.Coprime.of_dvd_right cx copX
    exact (hc.mul_right (copX.pow_right _)).pow_left _
  have absent : A ∉ vals := by
    intro hm
    obtain ⟨i,hi,e⟩ := mem_image.mp hm
    have hc := cop (mem_range.mp hi)
    rw [e] at hc
    have ha : A = 1 := by simpa only [Nat.gcd_self] using hc.gcd_eq_one
    have := leterm (mem_range.mp hi)
    omega
  have mono {i j : ℕ} (hi : i < j) (hj : j < L) : term L X i < term L X j := by
    have hci : coeff L i < X := (Nat.le_of_dvd bp (divides (hi.trans hj))).trans_lt (wb.trans_le wx)
    calc
      term L X i < X^(2*i+1) * X := by
        dsimp [term]
        rw [mul_comm (coeff L i)]
        exact Nat.mul_lt_mul_of_pos_left hci (by positivity)
      _ = X^(2*i+1+1) := (pow_succ _ _).symm
      _ ≤ X^(2*j+1) := pow_le_pow_right₀ (by omega) (by omega)
      _ ≤ term L X j := Nat.le_mul_of_pos_left _ (cpos hj)
  have inj : Set.InjOn (term L X) (↑(range L) : Set ℕ) := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact ((mono h (mem_range.mp hj)).ne e).elim
    · exact h
    · exact ((mono h (mem_range.mp hi)).ne e.symm).elim
  have total : ∑ s ∈ S, s = (X+1)^(2*L) := by
    rw [Finset.sum_insert absent, Finset.sum_image inj]
    exact binomial L X (by omega)
  have h0 : term L X 0 ∈ S := mem_insert_of_mem (mem_image_of_mem _ (mem_range.mpr hL))
  refine ⟨S, ?_, term L X 0, h0, wt.trans_le (wx.trans (leterm hL))⟩
  refine ⟨?_, ?_, total ▸ full_pow hdeg, ?_⟩
  · rw [Finset.card_insert_of_notMem absent, Finset.card_image_of_injOn inj, Finset.card_range]
    dsimp [L]
    omega
  · apply Nat.dvd_one.mp
    rw [← (cop hL).gcd_eq_one]
    exact Nat.dvd_gcd (Finset.gcd_dvd (mem_insert_self _ _)) (Finset.gcd_dvd h0)
  · intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact ⟨pow_pos (by omega) _,full_pow hdeg⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
      exact ⟨by have := leterm (mem_range.mp hi); omega, full_term (cw (mem_range.mp hi)) (by omega)⟩

end OMA.Powerful

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.infinite_of_six_le := by
  intro r hr hfin
  have hf := hfin.biUnion (t := fun S : Finset ℕ => (S : Set ℕ)) (fun S _ => S.finite_toSet)
  obtain ⟨T,hT⟩ := hf.bddAbove
  obtain ⟨S,hs,m,hm,hbig⟩ := OMA.Powerful.large hr T
  exact hbig.not_ge (hT (Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hs, hm⟩⟩))
