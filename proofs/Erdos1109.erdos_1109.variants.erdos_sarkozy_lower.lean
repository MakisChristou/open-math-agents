import FormalConjectures.ErdosProblems.«1109»
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Squarefree

/-! A progression of length k with squarefree sumset, giving the lower
bound of Erdős and Sárközy (1987). A primorial spacing rules out small
prime squares. Sieve the translates against the remaining prime squares. -/

namespace OMA.SquareSums
open Finset Filter
open scoped Pointwise BigOperators
noncomputable section

/-- In a linear progression with invertible slope mod m, at most one
argument in each block of length m gives a multiple of m. -/
lemma count_linear (T m a b : ℕ) (_hm : 0 < m) (ha : m.Coprime a) :
    ((range T).filter (fun t => m ∣ a*t+b)).card ≤ T/m+1 := by
  classical
  let S := (range T).filter (fun t => m ∣ a*t+b)
  have mem {t} (h : t ∈ S) : t < T ∧ m ∣ a*t+b := by simpa [S] using h
  change S.card ≤ _
  calc
    S.card ≤ (range (T/m+1)).card := by
      apply card_le_card_of_injOn (fun t => t/m)
      · intro t ht
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem ht).1.le))
      · intro s hs t ht eq
        have heq : a*s+b ≡ a*t+b [MOD m] :=
          (Nat.modEq_zero_iff_dvd.mpr (mem hs).2).trans
            (Nat.modEq_zero_iff_dvd.mpr (mem ht).2).symm
        have hres : s ≡ t [MOD m] :=
          Nat.ModEq.cancel_left_of_coprime ha (Nat.ModEq.add_right_cancel' b heq)
        have hs' := Nat.mod_add_div s m
        have ht' := Nat.mod_add_div t m
        change s % m = t % m at hres
        change s / m = t / m at eq
        rw [hres, eq] at hs'
        omega
    _ = _ := card_range _

/-- An elementary telescoping estimate for the tail of the inverse squares. -/
lemma tail (D P : ℕ) (hD : 0 < D) :
    (∑ i ∈ range P, (1:ℝ)/((D:ℝ)+i+1)^2) ≤ 1/(D:ℝ)-1/((D:ℝ)+P) := by
  induction P with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    have hx : (0:ℝ) < D+n := by positivity
    have hh : 1/((D:ℝ)+n+1)^2 ≤ 1/((D:ℝ)+n)-1/((D:ℝ)+n+1) := by
      generalize (D:ℝ)+(n:ℝ) = x at *
      field_simp
      nlinarith
    rw [← add_assoc]
    linarith

def q (k : ℕ) := 4 * primorial (8*k)
def value (k t j : ℕ) := 2+(2*t+j)*q k

lemma no_small {k t j p : ℕ} (hp : p.Prime) (hle : p ≤ 8*k) :
    ¬p*p ∣ value k t j := by
  intro h
  have hd : p ∣ q k := dvd_mul_of_dvd_right (hp.dvd_primorial_iff.mpr hle) _
  have hp2 : p ∣ 2 := (Nat.dvd_add_left (dvd_mul_of_dvd_right hd (2*t+j))).mp
    ((dvd_mul_right p p).trans h)
  have heq := (Nat.dvd_prime Nat.prime_two).mp hp2
  rcases heq with h1|rfl
  · exact hp.ne_one h1
  · have h4 : 4 ∣ (2*t+j)*q k := dvd_mul_of_dvd_right (dvd_mul_right 4 _) _
    have hb : 4 ∣ 2 := (Nat.dvd_add_left h4).mp h
    omega

def bad (k T j p : ℕ) : Finset ℕ :=
  if p.Prime then (range T).filter (fun t => p*p ∣ value k t j) else ∅

lemma nbad {k T j p : ℕ} (hk : 0 < k) (hp : 8*k < p) :
    ((bad k T j p).card:ℝ) ≤ (T:ℝ)/(p:ℝ)^2+1 := by
  classical
  by_cases hprime : p.Prime
  · have p2 : ¬p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
    have p4 : ¬p ∣ 4 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 4) h; omega
    have hq : ¬ p ∣ q k := by
      intro h
      rcases hprime.dvd_mul.mp h with h|h
      · exact p4 h
      · exact (not_le.mpr hp) (hprime.dvd_primorial_iff.mp h)
    have hc := (hprime.coprime_iff_not_dvd.mpr p2).mul_right
      (hprime.coprime_iff_not_dvd.mpr hq)
    have hm : (p*p).Coprime (2*q k) := hc.mul_left hc
    have he (t : ℕ) : value k t j = (2*q k)*t + (2+j*q k) := by unfold value; ring
    have cnt := count_linear T (p*p) (2*q k) (2+j*q k) (Nat.mul_pos hprime.pos hprime.pos) hm
    simp only [bad, if_pos hprime, he]
    calc
      _ ≤ ((T/(p*p)+1 : ℕ):ℝ) := by exact_mod_cast cnt
      _ ≤ _ := by
        push_cast
        rw [sq]
        gcongr
        simpa [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := T) (n := p*p))
  · simp [bad,hprime]
    positivity

/-- Sieve all translates of a fixed sumset index. -/
def excluded (k T P j : ℕ) :=
  (range P).biUnion (fun i => bad k T j (8*k+i+1))

lemma nexcluded {k T P j : ℕ} (hk : 0 < k) :
    ((excluded k T P j).card : ℝ) ≤ (T:ℝ)/(8*k)+P := by
  classical
  let D := 8*k
  have hD : 0 < D := by dsimp [D]; omega
  calc
    _ ≤ ∑ i ∈ range P, ((bad k T j (D+i+1)).card:ℝ) := by
      exact_mod_cast card_biUnion_le (s := range P) (t := fun i => bad k T j (D+i+1))
    _ ≤ ∑ i ∈ range P, ((T:ℝ)*(1/((D:ℝ)+i+1)^2)+1) := by
      apply sum_le_sum
      intro i hi
      simpa [D, div_eq_mul_inv, Nat.cast_add] using
        (nbad (T := T) (j := j) hk (p := D+i+1) (by dsimp [D]; omega))
    _ = (T:ℝ)*(∑ i ∈ range P, (1:ℝ)/((D:ℝ)+i+1)^2)+P := by
      rw [sum_add_distrib, mul_sum]; simp
    _ ≤ _ := by
      have hh := tail D P hD
      have hinv : 0 ≤ 1/((D:ℝ)+P) := by positivity
      have hm := mul_le_mul_of_nonneg_left (show (∑ i ∈ range P, (1:ℝ)/((D:ℝ)+i+1)^2) ≤ 1/(D:ℝ) by linarith) (Nat.cast_nonneg T (α := ℝ))
      simpa [D,div_eq_mul_inv] using add_le_add_right hm (P:ℝ)

lemma exists_translate {k T P : ℕ} (hk : 0 < k)
    (hcount : (2*k:ℝ)*((T:ℝ)/(8*k)+P) < T)
    (hlarge : ∀ t < T, ∀ j < 2*k, value k t j < P*P) :
    ∃ t < T, ∀ j < 2*k, Squarefree (value k t j) := by
  classical
  let S := (range (2*k)).biUnion (excluded k T P)
  have hs : (S.card:ℝ) ≤ (2*k:ℝ)*((T:ℝ)/(8*k)+P) := calc
    _ ≤ ∑ j ∈ range (2*k), ((excluded k T P j).card:ℝ) := by
      exact_mod_cast card_biUnion_le (s := range (2*k)) (t := excluded k T P)
    _ ≤ ∑ _j ∈ range (2*k), ((T:ℝ)/(8*k)+P) := sum_le_sum fun _ _ => nexcluded hk
    _ = _ := by simp [mul_add]
  have hc : S.card < (range T).card := by rw [card_range]; exact_mod_cast hs.trans_lt hcount
  obtain ⟨t,ht,hout⟩ := exists_mem_notMem_of_card_lt_card hc
  refine ⟨t,mem_range.mp ht,fun j hj => Nat.squarefree_iff_prime_squarefree.mpr fun p hp hd => ?_⟩
  by_cases hsmall : p ≤ 8*k
  · exact no_small hp hsmall hd
  have hval : 0 < value k t j := by unfold value; omega
  have hpp := (Nat.le_of_dvd hval hd).trans_lt (hlarge t (mem_range.mp ht) j hj)
  have hpless : p < P := by_contra fun h => (not_le.mpr hpp) (Nat.mul_self_le_mul_self (by omega))
  let i := p - (8*k+1)
  have ie : 8*k+i+1 = p := by dsimp [i]; omega
  have il : i < P := by dsimp [i]; omega
  apply hout
  apply mem_biUnion.mpr ⟨j,mem_range.mpr hj,?_⟩
  apply mem_biUnion.mpr ⟨i,mem_range.mpr il,?_⟩
  simpa [ie,bad,hp] using And.intro (mem_range.mp ht) hd

def base : ℕ := 2^160
def scale (k : ℕ) : ℕ := 2^(16*(k+1))

lemma scale_bounds (k : ℕ) : 16 ≤ scale k ∧ k ≤ scale k ∧ q k ≤ scale k := by
  have hx : 2^4 ≤ scale k := Nat.pow_le_pow_right (by decide) (by omega)
  have hk : 2^k ≤ scale k := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨hx,k.lt_two_pow_self.le.trans hk,?_⟩
  calc
    q k ≤ 4*4^(8*k) := Nat.mul_le_mul_left _ (primorial_le_four_pow _)
    _ = 2^(2+2*(8*k)) := by rw [pow_add, pow_mul (2:ℕ) 2 (8*k)]; rfl
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

lemma power_bound (k : ℕ) : (scale k)^10 = base^(k+1) := by
  unfold scale base
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

lemma size_estimate {k X t j : ℕ} (h16 : 16 ≤ X) (hkX : k ≤ X) (hqX : q k ≤ X)
    (ht : t < X^8) (hj : j < 2*k) : value k t j < X^10 := by
  have hX : 1 ≤ X := by omega
  have hX8 : X ≤ X^8 := by simpa using (Nat.pow_le_pow_right hX (show 1 ≤ 8 by decide))
  have hX9 : X ≤ X^9 := by simpa using (Nat.pow_le_pow_right hX (show 1 ≤ 9 by decide))
  have hjX : j ≤ 2*X^8 := by omega
  calc
    _ ≤ 2+(2*X^8+2*X^8)*X := by unfold value; gcongr
    _ = 2+4*X^9 := by ring
    _ ≤ 5*X^9 := by omega
    _ < X*X^9 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega : 0 < X) _)
    _ = X^10 := by ring

lemma count_estimate {X k : ℕ} (hk : 0 < k) (h16 : 16 ≤ X) (hkX : k ≤ X) :
    (2*k:ℝ)*(((X^8:ℕ):ℝ)/(8*k)+(X^5:ℕ)) < (X^8:ℕ) := by
  push_cast
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hr : (16:ℝ) ≤ X := by exact_mod_cast h16
  have hx : (0:ℝ) < X := by linarith
  have hx2 : (4:ℝ) ≤ (X:ℝ)^2 := by nlinarith [sq_nonneg ((X:ℝ)-2)]
  have h6 : (4:ℝ)*X^6 ≤ (X:ℝ)^8 := calc
    _ ≤ (X:ℝ)^2*X^6 := by exact mul_le_mul_of_nonneg_right hx2 (by positivity)
    _ = _ := by ring
  have h5 : (2*k:ℝ)*X^5 ≤ 2*(X:ℝ)^6 := calc
    _ ≤ (2*X:ℝ)*X^5 := by gcongr
    _ = _ := by ring
  have he : (2*k:ℝ)*((X:ℝ)^8/(8*k)) = (X:ℝ)^8/4 := by field_simp; ring
  rw [mul_add,he]
  nlinarith only [h5,h6,show (0:ℝ) < (X:ℝ)^8 by positivity]

lemma progression {k N : ℕ} (hk : 0 < k) (hN : base^(k+1) ≤ N) :
    k ≤ Erdos1109.f N := by
  classical
  let X := scale k
  obtain ⟨h16,hkX,hqX⟩ := scale_bounds k
  change 16 ≤ X at h16
  change k ≤ X at hkX
  change q k ≤ X at hqX
  have hsize (t : ℕ) (ht : t < X^8) (j : ℕ) (hj : j < 2*k) :
      value k t j < X^10 := by
    exact size_estimate h16 hkX hqX ht hj
  have hcount := count_estimate hk h16 hkX
  obtain ⟨t,ht,hgood⟩ := exists_translate (T := X^8) (P := X^5) hk hcount (fun t ht j hj => by
    convert hsize t ht j hj using 1; ring)
  let term := fun i : ℕ => 1+(t+i)*q k
  let A := (range k).image term
  have htj (i j : ℕ) : term i + term j = value k t (i+j) := by unfold term value; ring
  have hin {i : ℕ} (hi : i < k) : term i ∈ Icc 1 N := by
    apply mem_Icc.mpr
    refine ⟨by dsimp [term]; omega,?_⟩
    have hv := hsize t ht (i+i) (by omega)
    rw [← htj] at hv
    have hl : X^10 ≤ N := (power_bound k).le.trans hN
    omega
  have hq : 0 < q k := Nat.mul_pos (by decide) (primorial_pos _)
  have hinj : Function.Injective term := by
    intro i j e
    exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel e))
  have hcard : A.card = k := by simp [A,card_image_of_injective _ hinj]
  apply le_csSup
  · use N
    rintro n ⟨B,hB,_,rfl⟩
    simpa using card_le_card hB
  · refine ⟨A,?_,?_,hcard⟩
    · intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      exact hin (mem_range.mp hi)
    · intro n hn
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hn
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
      rw [htj]
      exact hgood (i+j) (by have := mem_range.mp hi; have := mem_range.mp hj; omega)


end
end OMA.SquareSums
open OMA.SquareSums in
theorem OMA.solution : type_of% @Erdos1109.erdos_1109.variants.erdos_sarkozy_lower := by
  apply Asymptotics.IsBigO.of_bound (3 * Real.log (base : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (base^2)] with N hN
  have hb : 1 < base := by decide
  have hn : N ≠ 0 := by have : 0 < base^2 := Nat.pow_pos (by omega); omega
  let m := Nat.log base N
  have hm : 2 ≤ m := (Nat.le_log_iff_pow_le hb hn).mpr hN
  have hpow := Nat.pow_log_le_self base hn
  have hk := progression (k := m-1) (N := N) (by omega) (by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)])
  have hlog : Real.log (N:ℝ) ≤ ((m:ℝ)+1)*Real.log (base:ℝ) := by
    have e := Nat.lt_pow_succ_log_self hb N
    have e' : (N:ℝ) ≤ (base:ℝ)^(m+1) := by exact_mod_cast e.le
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) e'
    simpa [Real.log_pow] using hh
  have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hb' : 0 ≤ Real.log (base:ℝ) := Real.log_nonneg (by exact_mod_cast hb.le)
  change ‖Real.log (N:ℝ)‖ ≤ _ * ‖(Erdos1109.f N : ℝ)‖
  rw [Real.norm_eq_abs,abs_of_nonneg hln,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  have h3 : (m:ℝ)+1 ≤ 3*(Erdos1109.f N : ℝ) := by
    exact_mod_cast (show m+1 ≤ 3*Erdos1109.f N by omega)
  linarith only [hlog,mul_le_mul_of_nonneg_right h3 hb']
