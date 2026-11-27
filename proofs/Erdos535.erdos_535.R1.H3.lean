import OMAReductions.R_Erdos535_erdos_535_R1

/-! Choose the small-prime cutoff at the square root of log N. Taking logarithms
of the extraction cost leaves a quadratic logarithm, bounded by the second
term of the exponential series. -/

open Filter Real

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H3 := by
  intro C hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlogC := Real.log_nonneg hC
  refine ⟨72 + 3 * log C, by positivity, ?_⟩
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htt : Tendsto (fun N : ℕ => log (log (N : ℝ))) atTop atTop := tendsto_log_atTop.comp ht
  filter_upwards [ht.eventually_ge_atTop 4, htt.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with N hx4 hu1 hN
  let x := log (N : ℝ)
  let u := log x
  let z := exp (u / 2)
  change 4 ≤ x at hx4
  change 1 ≤ u at hu1
  have hx : 0 < x := by linarith
  have hu : 0 < u := by linarith
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (by positivity)
  have hzz : z * z = x := by
    rw [show z*z = exp (u/2+u/2) from (Real.exp_add ..).symm]
    simpa [u, add_halves] using (Real.exp_log hx)
  have husq : u^2 ≤ 8*z := by
    have h := Real.pow_div_factorial_le_exp (u/2) (by positivity : 0 ≤ u/2) 2
    norm_num [Nat.factorial] at h
    dsimp [z]
    nlinarith
  have huit : u ≤ x := Real.log_le_self hx.le
  let y := ⌈z⌉₊
  let L := ⌈2*x⌉₊+1
  let K := ⌈2*x/u⌉₊
  have hylo : z ≤ (y : ℝ) := Nat.le_ceil _
  have hyhi : (y : ℝ) ≤ 2*z := by have h := Nat.ceil_lt_add_one (le_trans zero_le_one hz.le); dsimp [y]; linarith
  have hy : 2 ≤ y := by exact_mod_cast (lt_of_lt_of_le hz hylo : (1 : ℝ) < y)
  have hLlo : 2*x < (L : ℝ) := by
    dsimp [L]
    push_cast
    linarith [Nat.le_ceil (2*x)]
  have hLhi : (L : ℝ)+1 ≤ 2*x+3 := by
    dsimp [L]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*x)]
  have hKlo : 2*x ≤ (K : ℝ)*u := (div_le_iff₀ hu).mp (Nat.le_ceil _)
  have hKhi : (K : ℝ)*u ≤ 3*x := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*x/u)
    change (K : ℝ) < 2*x/u+1 at h
    have he : 2*x/u*u = 2*x := div_mul_cancel₀ _ hu.ne'
    nlinarith [mul_lt_mul_of_pos_right h hu]
  have hKbase : (K : ℝ)+1 ≤ 2*x+3 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*x/u)
    change (K : ℝ) < 2*x/u+1 at h
    have hd : 2*x/u ≤ 2*x := (div_le_iff₀ hu).mpr (by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hu1)])
    linarith
  have hNy : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hY : 0 < (y : ℝ) := by linarith
  have hlogy : u/2 ≤ log y := by
    simpa [z] using Real.log_le_log (Real.exp_pos _) hylo
  refine ⟨y, L, K, hy, ?_, ?_, ?_⟩
  · have hlog2 : (1:ℝ)/2 < log 2 := by linarith [log_two_gt_d9]
    have hbase : 0 < (2 : ℝ)^L := by positivity
    have hm : x < (L : ℝ) * log 2 := by
      nlinarith [mul_lt_mul_of_pos_left hlog2 (by positivity : 0 < (L:ℝ))]
    have h : (N : ℝ) < (2 : ℝ)^L := (Real.log_lt_log_iff hNy hbase).mp (by rwa [Real.log_pow])
    exact_mod_cast h
  · have hbase : 0 < (y:ℝ)^(K+1) := by positivity
    have hm : x < ((K:ℝ)+1) * log y := by
      nlinarith [mul_le_mul_of_nonneg_left hlogy (by positivity : 0 ≤ (K:ℝ)+1)]
    have h : (N : ℝ) < (y : ℝ)^(K+1) := (Real.log_lt_log_iff hNy hbase).mp (by
      rw [Real.log_pow]
      push_cast
      exact hm)
    exact_mod_cast h
  · have hcub : 2*x+3 ≤ x^3 := by
      nlinarith [sq_nonneg (x-2), mul_nonneg (sq_nonneg x) (show 0 ≤ x-4 by linarith)]
    have log_bound (t : ℝ) (ht : 0 < t) (hb : t ≤ 2*x+3) : log t ≤ 3*u := by
      simpa [Real.log_pow, u] using Real.log_le_log ht (hb.trans hcub)
    have hll := log_bound ((L:ℝ)+1) (by positivity) hLhi
    have hkl := log_bound ((K:ℝ)+1) (by positivity) hKbase
    have hweight : z * u^2 ≤ 8*x := by nlinarith [mul_le_mul_of_nonneg_left husq (le_trans zero_le_one hz.le)]
    have hlog : (y:ℝ)*log ((L:ℝ)+1) + log ((K:ℝ)+1) + (K:ℝ)*log C ≤ x*((72+3*log C)/u) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hu).mpr
      have hyterm : (y:ℝ)*log ((L:ℝ)+1) ≤ 6*z*u := calc
        _ ≤ (2*z)*(3*u) := mul_le_mul hyhi hll (Real.log_nonneg (by simp)) (by linarith)
        _ = _ := by ring
      have hcost : (y:ℝ)*log ((L:ℝ)+1) + log ((K:ℝ)+1) ≤ 9*z*u := by
        nlinarith [mul_nonneg (show 0 ≤ z-1 by linarith) hu.le]
      have htotal := mul_le_mul_of_nonneg_right hcost hu.le
      have hCterm := mul_le_mul_of_nonneg_right hKhi hlogC
      nlinarith
    push_cast
    apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hNy _)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_rpow hNy]
    simpa [x, u, mul_comm] using hlog
