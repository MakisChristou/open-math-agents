import OMAReductions.R_Erdos295_erdos_295_variants_erdos_straus_R1

/-! Distinct denominators increase by at least one. Bound their reciprocal
sum by telescoping logarithms, starting at N−1. -/

open Filter Finset Real

theorem OMA.solution : OMA.R_Erdos295_erdos_295_variants_erdos_straus_R1.H1 := by
  refine ⟨exp 1, exp_pos _, ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  intro m n hn hs hsum
  have rank (j : ℕ) (hj : j < m) : N+j ≤ n ⟨j,hj⟩ := by
    induction j with
    | zero => simpa using hn ⟨0,hj⟩
    | succ j ih =>
      have hprev := ih (by omega)
      have hstep := hs (show (⟨j,by omega⟩ : Fin m) < ⟨j+1,hj⟩ from Nat.lt_succ_self _)
      omega
  let a : ℝ := N-1
  have ha : 0<a := by
    have h : (2:ℝ) ≤ N := by exact_mod_cast hN
    dsimp [a]
    linarith
  let f (j : ℕ) := log (a+j)
  have term (i : Fin m) : (1/(n i):ℝ) ≤ f (i.val+1)-f i.val := by
    let t : ℝ := a+i.val
    have ht : 0<t := by dsimp [t]; positivity
    have hle : t+1 ≤ n i := by
      have h : (N:ℝ)+i.val ≤ n i := by exact_mod_cast rank i.val i.isLt
      dsimp [t,a]
      linarith
    calc
      _ ≤ 1/(t+1) := one_div_le_one_div_of_le (by positivity) hle
      _ = 1-((t+1)/t)⁻¹ := by field_simp; ring
      _ ≤ log ((t+1)/t) := Real.one_sub_inv_le_log_of_pos (by positivity)
      _ = _ := by
        rw [Real.log_div (by positivity : t+1≠0) ht.ne']
        simp [f,t,add_assoc]
  have upper : 1 ≤ log ((a+m)/a) := calc
    _ = ∑ i, (1/(n i):ℝ) := hsum.symm
    _ ≤ ∑ i : Fin m, (f (i.val+1)-f i.val) := sum_le_sum (fun i _ => term i)
    _ = f m-f 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => f (j+1)-f j)]
      exact sum_range_sub _ _
    _ = _ := by simp [f,Real.log_div,ha.ne',show a+(m:ℝ)≠0 by positivity]
  have he : exp 1 ≤ (a+m)/a := by
    simpa [Real.exp_log (by positivity : 0<(a+m)/a)] using Real.exp_le_exp.mpr upper
  have hf := (le_div_iff₀ ha).mp he
  dsimp [a] at hf
  linarith
