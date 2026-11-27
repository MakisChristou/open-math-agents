import FormalConjectures.OEIS.«46969»
import Mathlib.NumberTheory.Bernoulli

/-! Denominators of the Stirling coefficients at primes p for which 2p−1 is prime. The von Staudt--Clausen correction has just the terms 1/2 and 1/3. Faulhaber and doubling the representatives modulo a prime square determine the other cancellations. -/

namespace OMA.Stirling
open Finset

/-- The rationals with a denominator coprime to p. -/
def localRing (p : ℕ) : Subring ℚ where
  carrier := {x | ∃ b : ℕ, p.Coprime b ∧ ∃ t : ℤ, (b:ℚ)*x=t}
  zero_mem' := ⟨1, by simp, 0, by simp⟩
  one_mem' := ⟨1, by simp, 1, by simp⟩
  neg_mem' := by
    rintro x ⟨b,hb,t,ht⟩
    exact ⟨b,hb,-t,by push_cast; rw [mul_neg,ht]⟩
  add_mem' := by
    rintro x y ⟨b,hb,t,ht⟩ ⟨d,hd,s,hs⟩
    refine ⟨b*d,hb.mul_right hd,(d:ℤ)*t+b*s,?_⟩
    push_cast
    linear_combination (d:ℚ)*ht + (b:ℚ)*hs
  mul_mem' := by
    rintro x y ⟨b,hb,t,ht⟩ ⟨d,hd,s,hs⟩
    refine ⟨b*d,hb.mul_right hd,t*s,?_⟩
    push_cast
    rw [← ht, ← hs]
    ring

lemma local_cancel {p : ℕ} (hp : p.Prime) (X : ℤ) (n : ℕ)
    (h : (X : ℚ)/(p:ℚ)^n ∈ localRing p) : (p:ℤ)^n ∣ X := by
  obtain ⟨b,hb,t,ht⟩ := h
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he : (b:ℚ) * (X:ℚ) = (p:ℚ)^n * (t:ℚ) := by
    field_simp [hp0] at ht
    linarith
  have hi : (b:ℤ)*X = (p:ℤ)^n*t := by exact_mod_cast he
  exact hb.isCoprime.pow_left.dvd_of_dvd_mul_left ⟨t,hi⟩

lemma prime_ratio {p l : ℕ} (hp : p.Prime) (hl : l.Prime) :
    (p:ℚ)/l ∈ localRing p := by
  by_cases h : p = l
  · subst l
    have h0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simpa [h0] using (localRing p).one_mem
  · refine ⟨l, (Nat.coprime_primes hp hl).mpr h, (p:ℤ), ?_⟩
    have h0 : (l:ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
    push_cast
    field_simp

/-- A prime appears at most once in a Bernoulli denominator. -/
lemma scaled_bernoulli {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (p:ℚ)*bernoulli i ∈ localRing p := by
  rcases Nat.even_or_odd i with ⟨m, he⟩ | ho
  · rw [show i = 2*m by omega]
    obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen m
    have hs := (localRing p).sum_mem (t := (range (2*m+2)).filter
      (fun l : ℕ => l.Prime ∧ (l-1) ∣ 2*m)) (f := fun l : ℕ => (p:ℚ)/l)
      (fun l hl => prime_ratio hp (mem_filter.mp hl).2.1)
    have heq : (p:ℚ)*bernoulli (2*m) = (p:ℚ)*(z:ℚ) -
        ∑ l ∈ range (2*m+2) with l.Prime ∧ (l-1) ∣ 2*m, (p:ℚ)/l := by
      rw [hz, mul_add, mul_sum]
      simp [div_eq_mul_inv]
    rw [heq]
    exact (localRing p).sub_mem ((localRing p).mul_mem (natCast_mem (localRing p) _) (intCast_mem (localRing p) _)) hs
  · by_cases hi : i = 1
    · subst i
      rw [bernoulli_one, show (p:ℚ)*(-1/2) = -((p:ℚ)/2) by ring]
      exact (localRing p).neg_mem (prime_ratio hp Nat.prime_two)
    · rw [bernoulli_eq_zero_of_odd ho (by obtain ⟨t,ht⟩ := ho; omega), mul_zero]
      exact (localRing p).zero_mem

def powerSum (p i : ℕ) : ℕ := ∑ k ∈ range p, k^i

/-- Faulhaber's formula after clearing the last denominator. -/
lemma power_sum_congruence {p i : ℕ} (hp : p.Prime) (hi : 4 ≤ i) (hev : Even i)
    (hc : p.Coprime (i+1)) (A : ℤ) (hA : 6*bernoulli i = A) :
    (p:ℤ)^2 ∣ 6*(powerSum p i : ℤ) - p*A := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsum := sum_range_pow p i
  rw [sum_range_succ] at hsum
  simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel_left, pow_one] at hsum
  have htrim : ((i:ℚ)+1)*(6*(powerSum p i:ℚ)-(p:ℚ)*A)/(p:ℚ)^2 =
      ∑ j ∈ range i, 6*(bernoulli j*((i+1).choose j:ℚ)*(p:ℚ)^(i+1-j))/(p:ℚ)^2 := by
    have hi0 : (i:ℚ)+1 ≠ 0 := by positivity
    unfold powerSum
    push_cast
    rw [hsum, ← hA]
    simp only [← Finset.sum_div, ← Finset.mul_sum]
    field_simp <;> ring
  have hrest : ((i:ℚ)+1)*(6*(powerSum p i:ℚ)-(p:ℚ)*A)/(p:ℚ)^2 ∈ localRing p := by
    rw [htrim]
    apply (localRing p).sum_mem
    intro j hj
    have hjlt := mem_range.mp hj
    by_cases hodd : j+1 = i
    · rw [bernoulli_eq_zero_of_odd (by obtain ⟨t, ht⟩ := hev; exact ⟨t-1,by omega⟩) (by omega)]
      simpa using (localRing p).zero_mem
    · rw [show i+1-j = (i-j-2)+3 by omega, pow_add]
      have he : 6*(bernoulli j*((i+1).choose j:ℚ)*((p:ℚ)^(i-j-2)*(p:ℚ)^3))/(p:ℚ)^2 =
          6*((p:ℚ)*bernoulli j)*((i+1).choose j:ℚ)*(p:ℚ)^(i-j-2) := by
        field_simp <;> ring
      rw [he]
      exact (localRing p).mul_mem ((localRing p).mul_mem ((localRing p).mul_mem
        (natCast_mem (localRing p) 6) (scaled_bernoulli hp j)) (natCast_mem (localRing p) _))
        ((localRing p).pow_mem (natCast_mem (localRing p) p) _)
  apply hc.isCoprime.pow_left.dvd_of_dvd_mul_left
  apply local_cancel hp _ 2
  push_cast
  exact hrest

end OMA.Stirling

namespace OMA.Stirling
open Finset

def residue (p k : ℕ) := if 2*k < p then 2*k else 2*k-p

lemma double_perm {M : Type*} [AddCommMonoid M] (p : ℕ) (ho : Odd p) (f : ℕ → M) :
    ∑ k ∈ range p, f (residue p k) = ∑ k ∈ range p, f k := by
  obtain ⟨m,hm⟩ := ho
  apply sum_nbij' (residue p) (fun k => if k%2=0 then k/2 else (k+p)/2)
  · intro k hk
    have := mem_range.mp hk
    apply mem_range.mpr
    unfold residue
    split <;> omega
  · intro k hk
    have := mem_range.mp hk
    apply mem_range.mpr
    split <;> omega
  · intro k hk
    have := mem_range.mp hk
    unfold residue
    split <;> split <;> omega
  · intro k hk
    have := mem_range.mp hk
    unfold residue
    split_ifs <;> omega
  · intros; rfl

lemma linear_pow {R : Type*} [CommRing R] (x y : R) (hy : y^2 = 0) (n : ℕ) :
    (x-y)^(n+1) = x^(n+1) - (n+1:R)*y*x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (x-y), ih, Nat.cast_succ, pow_succ x (n+1), pow_succ x n]
    linear_combination ((n:R)+1)*x^n*hy

def tailSum (p e : ℕ) : ℕ := ∑ k ∈ range p, if 2*k < p then 0 else (2*k)^e


/-- Double the representatives from zero through p-1 modulo p squared.
The correction is linear because the square of p vanishes in this ring. -/
lemma double_sum (p e : ℕ) (ho : Odd p) :
    (powerSum p (e+1) : ZMod (p^2)) =
    2^(e+1)*(powerSum p (e+1) : ZMod (p^2)) -
      (e+1:ZMod (p^2))*p*(tailSum p e : ZMod (p^2)) := by
  have hnil : (p:ZMod (p^2))^2 = 0 := by
    change (p:ZMod (p^2))^2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have ht (k : ℕ) (hk : k ∈ range p) :
      (residue p k:ZMod (p^2))^(e+1) =
       2^(e+1)*(k:ZMod (p^2))^(e+1) - (e+1:ZMod (p^2))*p*(if 2*k<p then 0 else (2*(k:ZMod (p^2)))^e) := by
    unfold residue
    split_ifs with h
    · simp [Nat.cast_mul, mul_pow]
    · rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, linear_pow _ _ hnil]
      push_cast
      ring
  unfold powerSum tailSum
  push_cast
  calc
    _ = ∑ k ∈ range p, (residue p k:ZMod (p^2))^(e+1) :=
      (double_perm p ho (fun k => (k:ZMod (p^2))^(e+1))).symm
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl ht

lemma first_sum (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    p^2 ∣ powerSum p (2*p) := by
  have ho := hp.odd_of_ne_two (by omega)
  have eq := double_sum p (2*p-1) ho
  rw [show 2*p-1+1 = 2*p by omega] at eq
  have hz : ((2*p-1:ℕ):ZMod (p^2)) + 1 = 2*p := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun x : ℕ => (x : ZMod (p^2))) (show 2*p-1+1=2*p by omega)
  rw [hz] at eq
  have hnil : (p:ZMod (p^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hzero : (2*(p:ZMod (p^2)))*p=0 := by linear_combination 2*hnil
  rw [hzero, zero_mul, sub_zero] at eq
  have hprod : ((2:ZMod (p^2))^(2*p)-1)*(powerSum p (2*p):ZMod (p^2))=0 := by
    linear_combination -eq
  have hcop : IsCoprime (p:ℤ) ((2:ℤ)^(2*p)-1) := by
    letI : Fact p.Prime := ⟨hp⟩
    have hne : ¬ (p:ℤ) ∣ (2:ℤ)^(2*p)-1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [mul_comm 2 p, pow_mul, ZMod.pow_card]
      have hn : (3:ZMod p) ≠ 0 := by
        change ((3:ℕ):ZMod p) ≠ 0
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by decide) hlarge
      convert hn using 1 <;> ring
    exact (show Prime (p:ℤ) from Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hne
  have hd : (p:ℤ)^2 ∣ ((2:ℤ)^(2*p)-1)*(powerSum p (2*p):ℤ) := by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hprod
  exact_mod_cast hcop.pow_left.dvd_of_dvd_mul_left hd

lemma twice_range (v : ℕ) : ∑ k ∈ range v, 2*k = v*(v-1) := by
  simp_rw [mul_comm 2]
  rw [← Finset.sum_mul, Finset.sum_range_id_mul_two]

lemma tail_nonzero (q : ℕ) (hq : q.Prime) (hlarge : 3 < q) :
    (tailSum q q : ZMod q) ≠ 0 := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨m,hm⟩ := hq.odd_of_ne_two (by omega)
  have hmq : m+1 ≤ q := by omega
  have hcut : (tailSum q q:ZMod q) = ∑ k ∈ Ico (m+1) q, 2*(k:ZMod q) := by
    unfold tailSum
    push_cast
    rw [← Finset.sum_range_add_sum_Ico (f := fun k : ℕ =>
       if 2*k<q then (0:ZMod q) else (2*(k:ZMod q))^q) hmq]
    have hz : (∑ k ∈ range (m+1), if 2*k<q then (0:ZMod q) else (2*(k:ZMod q))^q) = 0 := by
      apply sum_eq_zero
      intro k hk
      have := mem_range.mp hk
      rw [if_pos (by omega)]
    rw [hz, zero_add]
    apply sum_congr rfl
    intro k hk
    have := (mem_Ico.mp hk).1
    rw [if_neg (by omega), ZMod.pow_card]
  have htwice (v : ℕ) : ∑ k ∈ range v, 2*(k:ZMod q) = (v:ZMod q)*((v-1:ℕ):ZMod q) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n:ZMod q)) (twice_range v)
  intro h
  have hpartition := Finset.sum_range_add_sum_Ico (f := fun k : ℕ => 2*(k:ZMod q)) hmq
  rw [← hcut, h, add_zero, htwice, htwice, ZMod.natCast_self, zero_mul] at hpartition
  have nz (x : ℕ) (hx : 0 < x) (hx' : x < q) : (x:ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hx hx'
  exact (mul_ne_zero (nz (m+1) (by omega) (by omega)) (nz (m+1-1) (by omega) (by omega))) hpartition

lemma second_sum (q : ℕ) (hq : q.Prime) (hlarge : 3 < q) :
    ¬ q^2 ∣ powerSum q (q+1) := by
  intro hd
  have eq := double_sum q q (hq.odd_of_ne_two (by omega))
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero] at eq
  have hnil : (q:ZMod (q^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hone : ((q:ZMod (q^2))+1)*q = q := by linear_combination hnil
  rw [hone] at eq
  have hz : ((q*tailSum q q : ℕ):ZMod (q^2)) = 0 := by
    push_cast
    linear_combination eq
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  rw [pow_two] at hdvd
  exact tail_nonzero q hq hlarge ((ZMod.natCast_eq_zero_iff _ _).mpr
    ((Nat.dvd_of_mul_dvd_mul_left hq.pos) hdvd))
end OMA.Stirling

namespace OMA.Stirling
open Finset

/-- When p and 2p-1 are prime with p greater than three, the only
prime denominators in the von Staudt--Clausen correction are 2 and 3. -/
lemma correction_primes (p : ℕ) (hp : p.Prime) (hq : (2*p-1).Prime) (hp3 : 3 < p) :
    (range (2*p+2)).filter (fun l : ℕ => l.Prime ∧ (l-1) ∣ 2*p) = {2,3} := by
  have pmod : p%3=1 := by
    have h₁ : ¬ 3 ∣ p := fun h => by rcases (Nat.dvd_prime hp).mp h with h|h <;> omega
    have h₂ : ¬ 3 ∣ 2*p-1 := fun h => by rcases (Nat.dvd_prime hq).mp h with h|h <;> omega
    omega
  ext l
  simp only [mem_filter,mem_range,mem_insert,mem_singleton]
  constructor
  · rintro ⟨_,hl,t,ht⟩
    have hl2 := hl.two_le
    have hpd : p ∣ (l-1)*t := ht ▸ dvd_mul_left p 2
    rcases hp.dvd_mul.mp hpd with hlp | htp
    · obtain ⟨s,hs⟩ := hlp
      rw [hs] at ht
      have hx : p*(s*t) = p*2 := by nlinarith only [ht]
      have hs2 : s ∣ 2 := ⟨t,(Nat.eq_of_mul_eq_mul_left hp.pos hx).symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hs2 with h|h
      · rw [h,mul_one] at hs
        have hd : 2 ∣ l := by have := hp.odd_of_ne_two (by omega); obtain ⟨u,hu⟩ := this; omega
        rcases (Nat.dvd_prime hl).mp hd with hh|hh <;> omega
      · rw [h] at hs
        have hd : 3 ∣ l := by omega
        rcases (Nat.dvd_prime hl).mp hd with hh|hh <;> omega
    · obtain ⟨s,hs⟩ := htp
      rw [hs] at ht
      have hx : p*((l-1)*s) = p*2 := by nlinarith only [ht]
      have hd : l-1 ∣ 2 := ⟨s,(Nat.eq_of_mul_eq_mul_left hp.pos hx).symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h|h <;> omega
  · rintro (rfl|rfl)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨by omega, Nat.prime_three, dvd_mul_right 2 p⟩

lemma six_times (p : ℕ) (hp : p.Prime) (hq : (2*p-1).Prime) (hp3 : 3 < p) :
    ∃ z : ℤ, 6*bernoulli (2*p) = (6*z-5:ℤ) := by
  obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen p
  rw [correction_primes p hp hq hp3] at hz
  norm_num at hz
  refine ⟨z,?_⟩
  push_cast
  linarith

lemma cancel_six (q : ℕ) (hq : q.Prime) (h3 : 3 < q) : q.Coprime 6 := by
  rw [hq.coprime_iff_not_dvd]
  intro hd
  rw [show (6:ℕ)=2*3 by decide] at hd
  rcases hq.dvd_mul.mp hd with h|h
  · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < q)) h
  · exact (Nat.not_dvd_of_pos_of_lt (by decide) h3) h

end OMA.Stirling

theorem OMA.solution : type_of% @OeisA46969.conjecture1 := by
  intro p hp hq hp3
  let q := 2*p-1
  have hqp : q.Prime := hq
  have hq3 : 3 < q := by dsimp [q]; omega
  have he : q+1 = 2*p := by dsimp [q]; omega
  obtain ⟨z,hz⟩ := OMA.Stirling.six_times p hp hq hp3
  let A := 6*z-5
  have hA : 6*bernoulli (2*p) = A := hz
  have hcP : p.Coprime (2*p+1) := by
    rw [hp.coprime_iff_not_dvd]
    intro h
    have h1 := Nat.dvd_sub h (dvd_mul_left p 2)
    simp at h1
    omega
  have hcQ : q.Coprime (2*p+1) := by
    rw [hqp.coprime_iff_not_dvd, ← he]
    intro h
    have h2 := Nat.dvd_sub h (dvd_refl q)
    have : q ∣ 2 := by convert h2 using 1 <;> omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < q)) this
  let S := OMA.Stirling.powerSum
  have hP := OMA.Stirling.power_sum_congruence hp (by omega : 4 ≤ 2*p)
    (even_two_mul p) hcP A hA
  have hQ := OMA.Stirling.power_sum_congruence hqp (by omega : 4 ≤ 2*p)
    (even_two_mul p) hcQ A hA
  have hPS : (p:ℤ)^2 ∣ (S p (2*p):ℤ) := by exact_mod_cast OMA.Stirling.first_sum p hp hp3
  have hQS : ¬ (q:ℤ)^2 ∣ (S q (2*p):ℤ) := by
    rw [← he]
    exact_mod_cast OMA.Stirling.second_sum q hqp hq3
  have hpa : (p:ℤ) ∣ A := by
    have hh := dvd_sub (hPS.mul_left 6) hP
    change (p:ℤ)^2 ∣ 6*(S p (2*p):ℤ) - (6*(S p (2*p):ℤ) - p*A) at hh
    rw [sub_sub_cancel, pow_two] at hh
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero : (p:ℤ) ≠ 0)).mp hh
  have hqa : ¬ (q:ℤ) ∣ A := by
    intro hd
    have hh := dvd_add hQ (show (q:ℤ)^2 ∣ q*A by rw [pow_two]; exact mul_dvd_mul (dvd_refl _) hd)
    have h6 : (q:ℤ)^2 ∣ 6*(S q (2*p):ℤ) := by simpa [pow_two] using hh
    exact hQS ((OMA.Stirling.cancel_six q hqp hq3).isCoprime.pow_left.dvd_of_dvd_mul_left h6)
  obtain ⟨b,hb⟩ := hpa
  have hbp (l : ℕ) (hl : l.Prime) (h : ¬ (l:ℤ) ∣ A) : b.natAbs.Coprime l := by
    apply Nat.Coprime.symm
    apply hl.coprime_iff_not_dvd.mpr
    intro hd
    have hd' : (l:ℤ) ∣ b := Int.natAbs_dvd_natAbs.mp (by simpa using hd)
    exact h (hb ▸ hd'.mul_left p)
  have h2 : b.natAbs.Coprime 2 := hbp 2 Nat.prime_two (by dsimp [A]; omega)
  have h3 : b.natAbs.Coprime 3 := hbp 3 Nat.prime_three (by dsimp [A]; omega)
  have hden : b.natAbs.Coprime (12*q) := by
    simpa only [show (12:ℕ)=2*(2*3) by decide] using
      (h2.mul_right (h2.mul_right h3)).mul_right (hbp q hqp hqa)
  have eq : bernoulli (2*p) / ((2*p*(2*p-1):ℕ):ℚ) = (b:ℚ)/((12*q:ℕ):ℚ) := by
    change bernoulli (2*p) / ((2*p*q:ℕ):ℚ) = _
    have ha : 6*bernoulli (2*p) = (p:ℚ)*b := by rw [hA,hb]; push_cast; rfl
    have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
    push_cast
    field_simp
    linear_combination 2*ha
  have hd := Rat.den_div_eq_of_coprime (a := b) (b := ((12*q:ℕ):ℤ))
    (by positivity) (by exact hden)
  have hres : OeisA46969.a p = 12*q := by
    simp only [OeisA46969.a, if_neg hp.ne_zero]
    rw [eq]
    exact_mod_cast hd
  rw [hres, Nat.mul_div_right _ (by decide : 0 < 12)]
  exact hqp
