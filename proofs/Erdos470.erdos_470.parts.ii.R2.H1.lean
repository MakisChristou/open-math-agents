import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

/-! Divisor sums for a power of two times two distinct odd primes. Any
subset of divisors has sum of the form x + py + qz, with x smaller than
the next power of two. Applied to the complement of a proposed
pseudoperfect representation, this restricts the abundance. -/

namespace OMA.Weird470
open Finset

def sig (n : ℕ) := ∑ t ∈ n.divisors, t

lemma sig_two (k : ℕ) : sig (2^k)+1=2^(k+1) := by
  unfold sig
  rw [Nat.sum_divisors_prime_pow (f:=fun n => n) Nat.prime_two]
  induction k with
  | zero => decide
  | succ k ih => rw [sum_range_succ,pow_succ 2 (k+1)]; omega

lemma sig_prime {p : ℕ} (hp : p.Prime) : sig p=p+1 := by
  simp [sig,hp.divisors,hp.ne_one.symm,add_comm]

lemma sig_onePrime {k p : ℕ} (hp : p.Prime) (hodd : p≠2) :
    sig (2^k*p)=(2^(k+1)-1)*(p+1) := by
  have hc := ((Nat.coprime_primes Nat.prime_two hp).mpr hodd.symm).pow_left k
  change (∑ t ∈ (2^k*p).divisors,t)=_
  rw [hc.sum_divisors_mul]
  change sig (2^k)*sig p=_
  rw [sig_prime hp,show sig (2^k)=2^(k+1)-1 by have := sig_two k; omega]

lemma sig_twoPrimes {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p≠2) (hq2 : q≠2) (hpq : p≠q) :
    sig (2^k*p*q)=(2^(k+1)-1)*(p+1)*(q+1) := by
  have hc := (((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm).pow_left k).mul_left
    ((Nat.coprime_primes hp hq).mpr hpq)
  change (∑ t ∈ (2^k*p*q).divisors,t)=_
  rw [hc.sum_divisors_mul]
  change sig (2^k*p)*sig q=_
  rw [sig_onePrime hp hp2,sig_prime hq]

lemma divisorForm {d m p q : ℕ} (h : d∣m*p*q) (hp : p.Prime) (hq : q.Prime) :
    ∃ e, e∣m ∧ (d=e ∨ d=e*p ∨ d=e*q ∨ d=e*p*q) := by
  obtain ⟨f,c,hf,hc,rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨e,b,he,hb,rfl⟩ := Nat.dvd_mul.mp hf
  refine ⟨e,he,?_⟩
  rcases (Nat.dvd_prime hp).mp hb with rfl|rfl <;>
    rcases (Nat.dvd_prime hq).mp hc with rfl|rfl <;> simp

lemma subsetSum {m p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (S : Finset ℕ) (hS : ∀ d∈S, d∣m*p*q) :
    ∃ y z : ℕ, ∑ d∈S,d = (∑ d∈S.filter (·∣m),d)+p*y+q*z := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,0,by simp⟩
  | @insert v S hv ih =>
    obtain ⟨y,z,he⟩ := ih (fun d hd => hS d (mem_insert_of_mem hd))
    obtain ⟨e,hm,hform⟩ := divisorForm (hS v (mem_insert_self ..)) hp hq
    have hv' : v ∉ S.filter (·∣m) := fun h => hv (mem_filter.mp h).1
    rw [sum_insert hv,he,filter_insert]
    split
    · exact ⟨y,z,by rw [sum_insert hv']; omega⟩
    · rename_i hvm
      rcases hform with rfl|rfl|rfl|rfl
      · contradiction
      · exact ⟨y+e,z,by ring⟩
      · exact ⟨y,z+e,by ring⟩
      · exact ⟨y+e*q,z,by ring⟩

lemma noPseudo {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hgap : ∀ x y z : ℕ, x<2^(k+1) → x+p*y+q*z ≠ sig (2^k*p*q)-2*(2^k*p*q)) :
    ¬(2^k*p*q).Pseudoperfect := by
  rintro ⟨_,S,hS,he⟩
  let n := 2^k*p*q
  let T := n.properDivisors \ S
  have ht : ∀ d∈T, d∣n := fun _ hd => (Nat.mem_properDivisors.mp (mem_sdiff.mp hd).1).1
  obtain ⟨y,z,hyz⟩ := subsetSum hp hq T ht
  have hsub : T.filter (·∣2^k) ⊆ (2^k).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2,by positivity⟩
  have hx := Finset.sum_le_sum_of_subset (f := fun i : ℕ => i) hsub
  change _ ≤ sig (2^k) at hx
  have htotal : (∑ d∈T,d)+n+n=sig n := by
    have hh := Finset.sum_sdiff (f:=fun i : ℕ => i) hS
    change (∑ d∈T,d)+(∑ d∈S,d)=_ at hh
    rw [he] at hh
    exact congrArg (·+n) hh |>.trans Nat.sum_divisors_eq_sum_properDivisors_add_self.symm
  apply hgap (∑ d∈T.filter (·∣2^k),d) y z (by have := sig_two k; omega)
  rw [←hyz]
  change _=sig n-2*n
  omega

lemma oneDeficient {i p : ℕ} (hp : p.Prime) (h : 2^(i+1)<p) : ¬(2^i*p).Abundant := by
  intro ha
  have hs := Nat.abundant_iff_sum_divisors.mp ha
  change 2*(2^i*p)<sig (2^i*p) at hs
  have hpos : 0<2^i := by positivity
  have htwo : 1<2^(i+1) := by rw [pow_succ]; omega
  rw [sig_onePrime hp (by omega)] at hs
  have he : 2^(i+1)-1+1=2*2^i := by rw [pow_succ]; omega
  nlinarith [congrArg (fun a : ℕ => a*(p+1)) he,show 2^(i+1)=2*2^i by rw [pow_succ,Nat.mul_comm]]

lemma pairIneq {b p q : ℕ} (hp : 2*b+1≤p) (hq : 2*b+1≤q) :
    b*(p+1)*(q+1)≤(b+1)*p*q := by
  nlinarith only [Nat.mul_le_mul_right q hp,Nat.mul_le_mul_right p hq,hp,hq]

lemma divNotWeird {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hP : 2^(k+1)<p) (hQ : 2^(k+1)<q) (d : ℕ) (hd : d∈(2^k*p*q).properDivisors) : ¬d.Weird := by
  intro hw
  obtain ⟨hdvd,hlt⟩ := Nat.mem_properDivisors.mp hd
  obtain ⟨e,he,hform⟩ := divisorForm hdvd hp hq
  have hp0 := hp.pos
  have hq0 := hq.pos
  have notP := oneDeficient hp hP
  have notQ := oneDeficient hq hQ
  rcases hform with rfl|rfl|rfl|rfl
  · exact notP (hw.1.of_dvd (he.trans (dvd_mul_right ..)) (by positivity))
  · exact notP (hw.1.of_dvd (Nat.mul_dvd_mul_right he p) (by positivity))
  · exact notQ (hw.1.of_dvd (Nat.mul_dvd_mul_right he q) (by positivity))
  · obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp he
    have hik : i<k := lt_of_le_of_ne hi (by rintro rfl; omega)
    have hbase := Nat.pow_le_pow_right (by decide : 0<2) (Nat.succ_le_of_lt hik)
    have hpos : 0<2^i := by positivity
    have hN : 2^(i+1)=2*2^i := by rw [pow_succ,Nat.mul_comm]
    have hM : 2^(k+1)=2*2^k := by rw [pow_succ,Nat.mul_comm]
    have h := Nat.abundant_iff_sum_divisors.mp hw.1
    change 2*(2^i*p*q) < sig (2^i*p*q) at h
    rw [sig_twoPrimes hp hq (by omega) (by omega) hpq] at h
    let b := 2^(i+1)-1
    have hb : b+1=2*2^i := by dsimp [b]; omega
    have hp' : 2*b+1≤p := by omega
    have hq' : 2*b+1≤q := by omega
    change 2*(2^i*p*q)<b*(p+1)*(q+1) at h
    have hright := pairIneq hp' hq'
    rw [hb] at hright
    exact (not_lt_of_ge hright) (by simpa only [Nat.mul_assoc] using h)

lemma criterion {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hP : 2^(k+1)<p) (hQ : 2^(k+1)<q)
    (hA : 2^(k+1)*p*q < (2^(k+1)-1)*(p+1)*(q+1))
    (hgap : ∀ x y z : ℕ, x<2^(k+1) → x+p*y+q*z ≠
      (2^(k+1)-1)*(p+1)*(q+1)-2^(k+1)*p*q) : Erdos470.PrimitiveWeird (2^k*p*q) := by
  have ht : 1<2^(k+1) := one_lt_pow₀ (by decide) (by omega)
  have hs := sig_twoPrimes (k:=k) hp hq (by omega) (by omega) hpq
  have he : 2*(2^k*p*q)=2^(k+1)*p*q := by rw [pow_succ]; ring
  refine ⟨⟨Nat.abundant_iff_sum_divisors.mpr ?_,noPseudo hp hq ?_⟩,divNotWeird hp hq hpq hP hQ⟩
  · change 2*(2^k*p*q)<sig (2^k*p*q)
    rwa [he,hs]
  · simpa only [hs,he] using hgap

lemma residueGap {N p q D : ℕ} (hP : N<p) (hD : D<q) (hm : N≤D%p) :
    ∀ x y z : ℕ, x<N → x+p*y+q*z ≠ D := by
  intro x y z hx he
  have hz : z=0 := by
    by_contra! hz
    have := Nat.le_mul_of_pos_right q (by omega : 0<z)
    omega
  subst z
  simp only [mul_zero,add_zero] at he
  rw [←he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hx.trans hP)] at hm
  omega

end OMA.Weird470

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := by
  intro k p q hp hq hP hQ hpq hpos hlt hmod
  exact OMA.Weird470.criterion hp hq hpq hP hQ hpos (OMA.Weird470.residueGap hP (by omega) hmod)
