import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

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

lemma intervalGap {N p q D t : ℕ} (hpq : p≤q) (hlo : q*t+N≤D) (hhi : D<p*(t+1)) :
    ∀ x y z : ℕ, x<N → x+p*y+q*z ≠ D := by
  intro x y z hx he
  by_cases h : y+z≤t
  · nlinarith only [he,hx,hlo,Nat.mul_le_mul_right y hpq,Nat.mul_le_mul_left q h]
  · have h' : t+1≤y+z := by omega
    nlinarith only [he,hhi,Nat.mul_le_mul_right z hpq,Nat.mul_le_mul_left p h',Nat.zero_le x]

lemma nearPower {k a b : ℕ} (hab : b+3<a) (hsize : a*(a+b)<2^(k+2))
    (hp : (2^(k+2)-a).Prime) (hq : (2^(k+2)+b).Prime) :
    Erdos470.PrimitiveWeird (2^k*(2^(k+2)-a)*(2^(k+2)+b)) := by
  let N := 2^(k+1)
  have hX : 2^(k+2)=2*N := by dsimp [N]; rw [pow_succ 2 (k+1),Nat.mul_comm]
  rw [hX] at hp hq hsize ⊢
  have haN : a<N := by
    have := Nat.mul_le_mul_left a (show 2≤a+b by omega)
    omega
  have hlarge : 2<N := by omega
  have hevenp := hp.eq_two_or_odd
  have hevenq := hq.eq_two_or_odd
  let t := (a-b-4)/2
  have hat : a=b+4+2*t := by dsimp [t]; omega
  obtain ⟨v,hv⟩ : ∃ v, N=a+v+1 := ⟨N-a-1,by omega⟩
  let p := 2*N-a
  let q := 2*N+b
  have hP : N<p := by dsimp [p]; omega
  have hQ : N<q := by dsimp [q]; omega
  have hpq : p<q := by dsimp [p,q]; omega
  let R := (a-1)*(b+1)
  let D := N*(2*t+1)+R
  have hS : (N-1)*(p+1)*(q+1)=N*p*q+D := by
    dsimp [D,R,p,q]
    rw [hv,hat]
    simp only [show 2*(b+4+2*t+v+1)-(b+4+2*t)=b+4+2*t+2*v+2 by omega,
      show b+4+2*t+v+1-1=b+4+2*t+v by omega,show b+4+2*t-1=b+3+2*t by omega]
    ring
  have hD : 0<D := by dsimp [D]; positivity
  have hlo : q*t+N≤D := by
    dsimp [D,R,q]
    rw [hat,show b+4+2*t-1=b+3+2*t by omega]
    nlinarith
  have hhi : D<p*(t+1) := by
    dsimp [D,R,p]
    rw [hv,hat] at hsize ⊢
    simp only [show 2*(b+4+2*t+v+1)-(b+4+2*t)=b+4+2*t+2*v+2 by omega,
      show b+4+2*t-1=b+3+2*t by omega]
    nlinarith only [hsize,Nat.zero_le b]
  apply criterion hp hq hpq.ne hP hQ
  · change N*p*q < (N-1)*(p+1)*(q+1)
    omega
  · change ∀ x y z : ℕ, x<N → x+p*y+q*z ≠ (N-1)*(p+1)*(q+1)-N*p*q
    rw [hS,Nat.add_sub_cancel_left]
    exact intervalGap hpq.le hlo hhi

end OMA.Weird470

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := by
  intro k a b hab hsize hp hq
  exact OMA.Weird470.nearPower hab hsize hp hq
