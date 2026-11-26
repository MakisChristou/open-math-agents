import FormalConjectures.ErdosProblems.«1100»

/-! In the Erdős–Hall construction each new prime exceeds the entire
preceding product. The new divisors therefore form a second block, all
divisible by the new prime. The only new coprime adjacency ends at that prime. -/

namespace OMA.DivisorBlocks

open Erdos1100
open scoped ArithmeticFunction.omega

def PrimeUpper (n : ℕ) : Prop :=
  ∀ x y : ℕ, x ∣ n → y ∣ n → x < y → x.Coprime y →
    (∀ z, x < z → z < y → ¬ z ∣ n) → y.Prime

lemma extend {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hlt : n < p) (h : PrimeUpper n) :
    PrimeUpper (n * p) := by
  intro x y hx hy hxy hco hgap
  have old (v : ℕ) (hv : v ∣ n * p) (hnot : ¬ p ∣ v) : v ∣ n :=
    (hp.coprime_iff_not_dvd.mpr hnot).symm.dvd_of_dvd_mul_right hv
  have small (v : ℕ) (hv : v ∣ n * p) (hvp : v < p) : v ∣ n :=
    old v hv (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_dvd_of_pos hv (Nat.mul_pos hn hp.pos)) hvp)
  rcases lt_trichotomy y p with hlt' | rfl | hgt
  · apply h x y (small x hx (hxy.trans hlt')) (small y hy hlt') hxy hco
    intro z hzx hzy hz
    exact hgap z hzx hzy (dvd_mul_of_dvd_left hz p)
  · exact hp
  · have hpx : p ≤ x := by
      by_contra! hxp
      exact hgap p hxp hgt (dvd_mul_left p n)
    have large (v : ℕ) (hv : v ∣ n * p) (hl : p ≤ v) : p ∣ v := by
      by_contra hz
      have := Nat.le_of_dvd hn (old v hv hz)
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (large x hx hpx) (large y hy hgt.le) hco).elim

lemma count_upper {n : ℕ} (hn : 0 < n) (upper : PrimeUpper n) : tauPerp n ≤ ω n := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  have homega : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
    rfl
  rw [homega, tauPerp]
  let upperIndex (i : Fin (n.divisors.card - 1)) := Nat.nth (· ∣ n) (i.val+1)
  have hlast (i : Fin (n.divisors.card - 1)) : i.val+1 < hf.toFinset.card := by
    have := i.isLt
    omega
  apply Finset.card_le_card_of_injOn upperIndex
  · intro i hmem
    let x := Nat.nth (· ∣ n) i
    have hidx : i.val < hf.toFinset.card := by have := hlast i; omega
    have hx : x ∣ n := Nat.nth_mem_of_lt_card hf hidx
    have hy : upperIndex i ∣ n := Nat.nth_mem_of_lt_card hf (hlast i)
    have hxy : x < upperIndex i := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) (hlast i)
    have hcop := (Finset.mem_filter.mp hmem).2
    apply Nat.mem_primeFactors.mpr
    refine ⟨upper x _ hx hy hxy hcop ?_, hy, hn.ne'⟩
    intro z hxz hzy hz
    exact (not_lt_of_ge (Nat.le_nth_of_lt_nth_succ hzy hz)) hxz
  · intro i _ j _ heq
    change Nat.nth (· ∣ n) (i.val+1) = Nat.nth (· ∣ n) (j.val+1) at heq
    have := Nat.nth_strictMonoOn hf |>.injOn (show i.val+1 ∈ Set.Iio _ from hlast i)
      (show j.val+1 ∈ Set.Iio _ from hlast j) heq
    exact Fin.ext (by omega)

lemma construct (k : ℕ) : ∃ n : ℕ, 0 < n ∧ Squarefree n ∧ ω n = k ∧ PrimeUpper n := by
  induction k with
  | zero =>
    refine ⟨1, by decide, squarefree_one, by simp, ?_⟩
    intro x y hx hy hxy
    have := Nat.eq_one_of_dvd_one hx
    have := Nat.eq_one_of_dvd_one hy
    omega
  | succ k ih =>
    obtain ⟨n, hn, hsf, hw, hupper⟩ := ih
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n+1)
    have hlt : n < p := hnp
    have hco := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn hlt)).symm
    refine ⟨n*p, Nat.mul_pos hn hp.pos, (Nat.squarefree_mul hco).mpr ⟨hsf,hp.squarefree⟩,
      ?_, extend hn hp hlt hupper⟩
    rw [ArithmeticFunction.cardDistinctFactors_mul hco, hw, ArithmeticFunction.cardDistinctFactors_apply_prime hp]

end OMA.DivisorBlocks

open OMA.DivisorBlocks Erdos1100 in
theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.eq_omega := by
  intro k
  obtain ⟨n, hn, hsf, hw, h⟩ := construct k
  exact ⟨n, hsf, hw, ((count_upper hn h).antisymm (erdos_1100.variants.omega_le n hn)).trans hw⟩
