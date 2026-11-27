import OMAReductions.R_Erdos830_erdos_830_variants_erdos_R1

/-! Erdős's truncation estimate for the abundancy function. A divisor d occurs
at most N/d times up to N. Its contribution to the mean is therefore at most
1/d², whose tail tends to zero. -/
namespace OMA.DivisorTail
open Finset
open scoped ArithmeticFunction.sigma

noncomputable def tail (B N n : ℕ) : ℝ := ∑ d ∈ Ioc B N, if d ∣ n then (1:ℝ)/d else 0

lemma ratio_tail {B N n : ℕ} (hn : n ∈ Icc 1 N) :
    (σ 1 n : ℝ)/n - ∑ d ∈ n.divisors.filter (·≤B), (1:ℝ)/d = tail B N n := by
  classical
  obtain ⟨hp,hN⟩ := mem_Icc.mp hn
  rw [OMA.R_Erdos830_erdos_830_variants_erdos_R1.ratio_eq hp]
  have hpart := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d≤B) (fun d => (1:ℝ)/d)
  have hs : n.divisors.filter (fun d => ¬d≤B) = (Ioc B N).filter (· ∣ n) := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,mem_Ioc]
    constructor
    · rintro ⟨⟨hd,_⟩,hb⟩
      exact ⟨⟨by omega,(Nat.le_of_dvd hp hd).trans hN⟩,hd⟩
    · rintro ⟨⟨hb,_⟩,hd⟩
      exact ⟨⟨hd,by omega⟩,by omega⟩
  rw [hs] at hpart
  unfold tail
  rw [← Finset.sum_filter]
  linarith

lemma count_dvd (N d : ℕ) : ((Icc 1 N).filter (d ∣ ·)).card = N/d := by
  have eq : (Icc 1 N).filter (d ∣ ·) = (range (N+1)).filter (fun k => k≠0 ∧ d ∣ k) := by
    ext k
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [eq,Nat.card_multiples']

lemma total_bound (B N : ℕ) :
    ∑ n ∈ Icc 1 N, tail B N n ≤ (N:ℝ)*∑ d ∈ Ioc B N, 1/(d:ℝ)^2 := by
  classical
  unfold tail
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [←Finset.sum_filter,Finset.sum_const,count_dvd,nsmul_eq_mul]
  have hp : (0:ℝ)<d := by exact_mod_cast (Nat.zero_le B).trans_lt (mem_Ioc.mp hd).1
  have hle : ((N/d:ℕ):ℝ)*(d:ℝ)≤N := by exact_mod_cast Nat.div_mul_le_self N d
  calc
    ((N/d:ℕ):ℝ)*(1/(d:ℝ)) = ((N/d:ℕ):ℝ)*(d:ℝ) / (d:ℝ)^2 := by field_simp
    _ ≤ (N:ℝ)/(d:ℝ)^2 := by gcongr
    _ = _ := by ring

end OMA.DivisorTail

open Finset Filter OMA.DivisorTail in
theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_erdos_R1.H2 := by
  classical
  intro η ε hη hε
  have summ : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by decide)
  obtain ⟨U,hU⟩ := summable_iff_vanishing_norm.mp summ (η*ε) (mul_pos hη hε)
  let B := U.sup id
  refine ⟨B,Eventually.of_forall fun N => ?_⟩
  let S := (Icc 1 N).filter (fun n => η ≤ tail B N n)
  have same : ((Icc 1 N).filter (fun n => η ≤ (ArithmeticFunction.sigma 1 n : ℝ)/n -
      ∑ d ∈ n.divisors.filter (·≤B), (1:ℝ)/d)) = S := by
    ext n
    simp only [S,mem_filter]
    exact and_congr_right fun hn => by rw [ratio_tail hn]
  rw [same]
  have ds : Disjoint (Ioc B N) U := by
    apply Finset.disjoint_left.mpr
    intro x hx hux
    exact (not_lt_of_ge (show x≤B from Finset.le_sup (f:=id) hux)) (mem_Ioc.mp hx).1
  have htail := hU (Ioc B N) ds
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at htail
  have mark : (S.card:ℝ)*η ≤ ∑ n ∈ Icc 1 N, tail B N n := calc
    (S.card:ℝ)*η = ∑ _n ∈ S, η := by simp
    _ ≤ ∑ n ∈ S, tail B N n := Finset.sum_le_sum fun n hn => (mem_filter.mp hn).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => by
      unfold tail
      exact sum_nonneg fun d _ => by split <;> positivity)
  have h := mark.trans (total_bound B N)
  have h' := mul_le_mul_of_nonneg_left htail.le (show 0≤(N:ℝ) by positivity)
  nlinarith
