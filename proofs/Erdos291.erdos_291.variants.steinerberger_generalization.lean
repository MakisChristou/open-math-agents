import FormalConjectures.ErdosProblems.«291»

/-! Steinerberger's leading-digit criterion. Modulo a prime, the only terms of the
unreduced harmonic numerator that survive have index divisible by the highest
power of that prime up to the endpoint. Their sum is the shorter harmonic sum
multiplied by an integer coprime to the prime. -/

namespace OMA.LeadingDigit

open Finset Erdos291

lemma divides_L {i n : ℕ} (hi : i ∈ Icc 1 n) : i ∣ L n :=
  Finset.dvd_lcm (f := fun j : ℕ => j) hi

lemma multiples (q n : ℕ) (hq : 0 < q) :
    ((Icc 1 n).filter fun i => q ∣ i) = (Icc 1 (n/q)).image (q * ·) := by
  ext i
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨hi,hn⟩, j, rfl⟩
    refine ⟨j, ⟨?_, (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hn)⟩, rfl⟩
    by_contra! h
    have : j = 0 := by omega
    simp [this] at hi
  · rintro ⟨j, ⟨hj,hjn⟩, rfl⟩
    exact ⟨⟨Nat.mul_pos hq hj, by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hjn⟩,
      dvd_mul_right _ _⟩

lemma rational_numerator {p b u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) (hu₀ : u ≠ 0)
    {r : ℚ} (hr : r * u = b) : p ∣ b ↔ (p : ℤ) ∣ r.num := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hu' : ¬ (p : ℤ) ∣ (u : ℤ) := by exact_mod_cast hu
  have hfrac : r = Rat.divInt b u := by
    rw [Rat.divInt_eq_div]
    push_cast
    exact (eq_div_iff (by exact_mod_cast hu₀)).mpr hr
  have hden : (r.den : ℤ) ∣ (u : ℤ) := by rw [hfrac]; apply Rat.den_dvd
  have hd : ¬ (p : ℤ) ∣ (r.den : ℤ) := fun h => hu' (h.trans hden)
  have heq : r.num * (u:ℤ) = (b:ℤ) * r.den := by
    have eqQ := hr
    rw [← r.num_div_den] at eqQ
    have hd₀ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    field_simp [hd₀] at eqQ
    rw [mul_comm (b:ℤ)]
    exact_mod_cast eqQ
  rw [← Int.natCast_dvd_natCast]
  constructor
  · intro h
    have hmul : (p : ℤ) ∣ r.num * u := heq ▸ dvd_mul_of_dvd_left h _
    exact (hpz.dvd_mul.mp hmul).resolve_right hu'
  · intro h
    have hmul : (p : ℤ) ∣ (b:ℤ) * r.den := heq ▸ dvd_mul_of_dvd_left h _
    exact (hpz.dvd_mul.mp hmul).resolve_right hd

end OMA.LeadingDigit

open Finset Erdos291 OMA.LeadingDigit in
theorem OMA.solution : type_of% @Erdos291.erdos_291.variants.steinerberger_generalization := by
  intro n p hp hpn
  let q := p ^ Nat.log p n
  let k := n / q
  let M := L n
  let u := M / q
  let S := Icc 1 n
  let J := Icc 1 k
  let B := ∑ j ∈ J, u / j
  have hn : n ≠ 0 := by have := hp.pos; omega
  have hq : 0 < q := pow_pos hp.pos _
  have hqn : q ≤ n := Nat.pow_log_le_self p hn
  have hqM : q ∣ M := divides_L (mem_Icc.mpr ⟨hq,hqn⟩)
  have hM : M ≠ 0 := Nat.lcmUpto_ne_zero n
  have hu₀ : u ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hqM) hq).ne'
  have hu : ¬ p ∣ u := by
    intro h
    have hpow : p ^ (Nat.log p n + 1) ∣ M := by
      rw [pow_succ]
      exact (Nat.dvd_div_iff_mul_dvd hqM).mp h
    have hle := (hp.pow_dvd_iff_le_factorization hM).mp hpow
    change Nat.log p n + 1 ≤ (Nat.lcmUpto n).factorization p at hle
    rw [Nat.factorization_lcmUpto n hp] at hle
    omega
  have hjM (j : ℕ) (hj : j ∈ J) : q * j ∣ M := by
    obtain ⟨hj₀, hjk⟩ := mem_Icc.mp hj
    apply divides_L
    exact mem_Icc.mpr ⟨Nat.mul_pos hq hj₀, by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hjk⟩
  have hregular : p ∣ ∑ i ∈ S with ¬ q ∣ i, M / i := by
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨his, hqi⟩ := mem_filter.mp hi
    by_contra h
    have hc : q.Coprime (M/i) := (hp.coprime_iff_not_dvd.mpr h).pow_left _
    apply hqi
    apply hc.dvd_mul_right.mp
    rwa [Nat.mul_div_cancel' (divides_L his)]
  have hsum : (∑ i ∈ S with q ∣ i, M / i) = B := by
    rw [show (S.filter fun i => q ∣ i) = J.image (q * ·) from multiples q n hq]
    rw [sum_image (fun x _ y _ he => Nat.eq_of_mul_eq_mul_left hq he)]
    apply sum_congr rfl
    intro j _
    exact (Nat.div_div_eq_div_mul M q j).symm
  have ha : p ∣ a n ↔ p ∣ B := by
    change p ∣ ∑ i ∈ S, M / i ↔ _
    rw [← sum_filter_add_sum_filter_not S (fun i => q ∣ i), hsum, Nat.dvd_add_left hregular]
  have hrat : (∑ i ∈ J, (1:ℚ)/i) * u = B := by
    dsimp only [B]
    rw [sum_mul, Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    have hd : j ∣ u := (Nat.dvd_div_iff_mul_dvd hqM).mpr (hjM j hj)
    have hj₀ : 0 < j := (mem_Icc.mp hj).1
    rw [Nat.cast_div hd (by positivity)]
    ring
  change p ∣ Nat.gcd (a n) M ↔ (p:ℤ) ∣ (∑ i ∈ J, (1:ℚ)/i).num
  rw [Nat.dvd_gcd_iff, and_iff_left (divides_L (mem_Icc.mpr ⟨hp.pos,hpn⟩)), ha]
  exact rational_numerator hp hu hu₀ hrat
