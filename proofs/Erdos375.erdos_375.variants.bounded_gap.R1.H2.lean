import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1
import Mathlib.NumberTheory.Chebyshev

/-! Chebyshev's upper bound is a constant times k/log k. The denominator
eventually exceeds any fixed positive reciprocal-density threshold. -/

open Filter Real

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H2 := by
  intro c hc
  have hcount := tendsto_natCast_atTop_atTop.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  have hlog : Tendsto (fun k : ℕ => log (k:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hcount, hlog.eventually_gt_atTop ((log 4+1)/c), eventually_ge_atTop (2:ℕ)]
    with k hk hl hk2
  have hk' : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  have hp := Real.log_pos hk'
  change ((k.primesLE.card : ℕ):ℝ) < c*k
  rw [Nat.primesLE_card_eq_primeCounting]
  rw [Nat.floor_natCast] at hk
  apply lt_of_le_of_lt hk
  apply (div_lt_iff₀ hp).mpr
  have h := (div_lt_iff₀ hc).mp hl
  nlinarith [mul_lt_mul_of_pos_right h (zero_lt_one.trans hk')]
