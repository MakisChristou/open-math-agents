import FormalConjectures.OEIS.«60841»
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.BigOperators.Fin

/-! Smith's determinant calculation follows by factoring the gcd matrix
through the lower triangular incidence matrix of divisibility. Scaling its
rows and columns converts gcd entries to reciprocal lcm entries. -/

namespace OMA.LcmDet
open Finset Matrix

def index {n : ℕ} (i : Fin n) := i.val+1
def inc (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j => if index j ∣ index i then 1 else 0
def weights (n : ℕ) : Fin n → ℚ := fun i => (index i).totient
def scales (n : ℕ) : Fin n → ℚ := fun i => ((index i:ℕ):ℚ)⁻¹
def prodPhi (n : ℕ) := ∏ k∈range n,(k+1).totient

lemma gcd_sum {x y n : ℕ} (hx : 0<x) (hxn : x≤n) :
    (∑ k : Fin n, if k.val+1∣x ∧ k.val+1∣y then (k.val+1).totient else 0)=x.gcd y := by
  let g := x.gcd y
  have hg : 0<g := Nat.gcd_pos_of_pos_left y hx
  have hgn : g≤n := (Nat.le_of_dvd hx (Nat.gcd_dvd_left x y)).trans hxn
  have hset : ((range (n+1)).filter fun k => k∣g)=g.divisors := by
    ext k
    simp only [mem_filter,mem_range,Nat.mem_divisors,and_iff_left hg.ne']
    exact ⟨And.right,fun hk => ⟨by have := Nat.le_of_dvd hg hk; omega,hk⟩⟩
  have hsum : (∑ k∈range (n+1), if k∣g then k.totient else 0)=g := by
    rw [←sum_filter,hset,Nat.sum_totient]
  rw [sum_range_succ'] at hsum
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k+1∣x ∧ k+1∣y then (k+1).totient else 0) n]
  simpa [g,Nat.dvd_gcd_iff] using hsum

lemma gcdGram (n : ℕ) (i j : Fin n) :
    (inc n*diagonal (weights n)*(inc n).transpose) i j = ((index i).gcd (index j):ℚ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ k : Fin n, ((if index k∣index i ∧ index k∣index j then (index k).totient else 0 : ℕ):ℚ) := by
      apply sum_congr rfl
      intro k _
      by_cases hi : index k∣index i <;> by_cases hj : index k∣index j <;>
        simp [Matrix.mul_diagonal,Matrix.transpose_apply,inc,weights,hi,hj]
    _ = _ := by
      rw [←Nat.cast_sum]
      exact_mod_cast gcd_sum (x:=index i) (y:=index j) (n:=n) (by simp [index]) (by exact i.isLt)

lemma factor (n : ℕ) : OeisA60841.lcmMatrix n =
    diagonal (scales n)*(inc n*diagonal (weights n)*(inc n).transpose)*diagonal (scales n) := by
  ext i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul,gcdGram]
  change 1/(Nat.lcm (index i) (index j):ℚ)=((index i:ℕ):ℚ)⁻¹*((index i).gcd (index j):ℚ)*((index j:ℕ):ℚ)⁻¹
  have hi : index i ≠ 0 := Nat.succ_ne_zero _
  have hj : index j ≠ 0 := Nat.succ_ne_zero _
  have hl := Nat.lcm_ne_zero hi hj
  have hs : (((index i).gcd (index j):ℕ):ℚ)*((Nat.lcm (index i) (index j):ℕ):ℚ)
      = ((index i:ℕ):ℚ)*((index j:ℕ):ℚ) := by exact_mod_cast Nat.gcd_mul_lcm (index i) (index j)
  field_simp
  linear_combination -hs

lemma detInc (n : ℕ) : (inc n).det=1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [inc]
  · intro i j hij
    have hlt : index i < index j := by exact Nat.succ_lt_succ hij
    have hnd : ¬index j∣index i := fun hd => hlt.not_ge (Nat.le_of_dvd (Nat.succ_pos _) hd)
    simp [inc,hnd]

lemma prodScales (n : ℕ) : (∏ i, scales n i)=(n.factorial:ℚ)⁻¹ := by
  unfold scales index
  rw [Finset.prod_inv_distrib,←Nat.cast_prod,Fin.prod_univ_eq_prod_range (fun k : ℕ => k+1) n,Nat.factorial_eq_prod_range_add_one]

lemma inverseDet (n : ℕ) : (OeisA60841.lcmMatrix n).det⁻¹=(n.factorial:ℚ)^2/(prodPhi n : ℚ) := by
  have hw : (∏ i, weights n i)=(prodPhi n:ℚ) := by
    unfold weights prodPhi index
    rw [←Nat.cast_prod,Fin.prod_univ_eq_prod_range (fun k : ℕ => (k+1).totient) n]
  rw [factor]
  simp only [det_mul,det_diagonal,det_transpose,detInc,prodScales,hw,one_mul,mul_one]
  simp [div_eq_mul_inv,pow_two,mul_comm,mul_assoc]

/-- Each prime contributes at least its share from p − 1 to the
two-adic order of the totient of any multiple of p. -/
def weight (p : ℕ) := (p-1).factorization 2
def smallPrimes := Nat.primesBelow 194
def lower (n : ℕ) := ∑ p∈smallPrimes, (n/p)*weight p

lemma pointwise (m : ℕ) (hm : m≠0) :
    (∑ p∈smallPrimes, if p∣m then weight p else 0) ≤ m.totient.factorization 2 := by
  rw [←sum_filter]
  have sub : (smallPrimes.filter fun p => p∣m) ⊆ m.primeFactors := by
    intro p hp
    obtain ⟨h0,h1⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesBelow h0,h1,hm⟩
  have nz : ∀ p∈m.primeFactors, p-1≠0 := by
    intro p hp
    have hh := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  let u := ∏ p∈m.primeFactors, (p-1)
  have hu : 0<u := Finset.prod_pos (fun p hp => Nat.pos_of_ne_zero (nz _ hp))
  have hd : u∣m.totient := by
    rw [Nat.totient_eq_div_primeFactors_mul]
    exact dvd_mul_left _ _
  calc
    _ ≤ ∑ p∈m.primeFactors, weight p :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    _ = u.factorization 2 := (Nat.factorization_prod_apply nz).symm
    _ ≤ _ := (Nat.factorization_le_iff_dvd hu.ne' (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne').mpr hd 2

lemma prodPhi_pos (n : ℕ) : 0<prodPhi n := Finset.prod_pos (fun k _ => Nat.totient_pos.mpr (Nat.succ_pos k))

lemma lower_bound (n : ℕ) : lower n ≤ (prodPhi n).factorization 2 := by
  rw [prodPhi,Nat.factorization_prod_apply (fun k _ => (Nat.totient_pos.mpr (Nat.succ_pos k)).ne')]
  calc
    lower n = ∑ p∈smallPrimes, ∑ k∈range n, if p∣k+1 then weight p else 0 := by
      unfold lower
      apply sum_congr rfl
      intro p _
      rw [←Finset.sum_filter,Finset.sum_const,Nat.card_multiples,Nat.nsmul_eq_mul]
    _ = ∑ k∈range n, ∑ p∈smallPrimes, if p∣k+1 then weight p else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun k _ => pointwise (k+1) (Nat.succ_ne_zero _))

lemma lower_add (a b : ℕ) : lower a+lower b ≤ lower (a+b) := by
  unfold lower
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  rw [←Nat.add_mul]
  exact Nat.mul_le_mul_right (weight p) Nat.div_add_div_le_add_div

set_option maxRecDepth 100000 in
lemma startingBounds : ∀ i : Fin 192, 2*(192+i.val)<lower (192+i.val) := by decide +kernel

lemma lower_large (n : ℕ) (hn : 192≤n) : 2*n<lower n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n<384
    · have hx := startingBounds ⟨n-192,by omega⟩
      simpa only [show 192+(n-192)=n by omega] using hx
    · have hr := ih (n-192) (by omega) (by omega)
      have hb := startingBounds 0
      change 2*192<lower 192 at hb
      have hs := lower_add 192 (n-192)
      rw [show 192+(n-192)=n by omega] at hs
      omega

lemma no_dvd_large (n : ℕ) (hn : 192≤n) : ¬prodPhi n∣n.factorial^2 := by
  intro hd
  have h := (Nat.factorization_le_iff_dvd (prodPhi_pos n).ne'
    (pow_ne_zero 2 n.factorial_ne_zero)).mpr hd 2
  have hval := Nat.sub_one_mul_factorization_factorial (n:=n) Nat.prime_two
  have hn2 : n.factorial.factorization 2 ≤ n := by omega
  rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at h
  have hlow := lower_bound n
  have hbig := lower_large n hn
  omega

def fastPhi (n : ℕ) := (n / ∏ p∈n.primeFactors,p) * ∏ p∈n.primeFactors,(p-1)
def fastProd : ℕ→ℕ
  | 0 => 1
  | n+1 => fastProd n * fastPhi (n+1)

lemma fastProd_eq (n : ℕ) : fastProd n=prodPhi n := by
  induction n with
  | zero => simp [fastProd,prodPhi]
  | succ n ih =>
    simp only [fastProd,ih,prodPhi,prod_range_succ]
    rw [Nat.totient_eq_div_primeFactors_mul]
    rfl

set_option maxRecDepth 100000 in
lemma smallValues : ∀ j : Fin 191, let n := j.val+1
    (fastProd n ∣ n.factorial^2 ↔ n≤34 ∨ n=36 ∨ n=38) := by decide +kernel

lemma classification (n : ℕ) (hn : 1≤n) :
    (OeisA60841.lcmMatrix n).det⁻¹.den=1 ↔ n∈OeisA60841.integerDetN := by
  rw [inverseDet,←Nat.cast_pow,Rat.den_div_natCast_eq_one_iff _ _ (prodPhi_pos n).ne']
  have hm : n∈OeisA60841.integerDetN ↔ n≤34 ∨ n=36 ∨ n=38 := by
    simp [OeisA60841.integerDetN,hn]
    tauto
  rw [hm]
  by_cases h : n<192
  · have hs := smallValues ⟨n-1,by omega⟩
    dsimp only at hs
    rwa [show n-1+1=n by omega,fastProd_eq] at hs
  · exact iff_of_false (no_dvd_large n (by omega)) (by omega)
end OMA.LcmDet

theorem OMA.solution : type_of% @OeisA60841.conjecture1 := OMA.LcmDet.classification
