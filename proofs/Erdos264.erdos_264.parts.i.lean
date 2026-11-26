import FormalConjectures.ErdosProblems.«264»

/-! A bounded integer perturbation of the powers of two gives a reciprocal sum of 1/8.
Starting at 64, round a scaled remainder to one of six nonzero odd digits.
The rounding error stays bounded, so the unscaled remainder tends to zero. -/

namespace OMA.Ahmes

open Filter Topology Finset

noncomputable def digit (x : ℝ) : ℤ :=
  if x < -4 then -5 else if x < -2 then -3 else if x < 0 then -1 else
  if x < 2 then 1 else if x < 4 then 3 else 5

lemma digit_bounds (x : ℝ) : -5 ≤ digit x ∧ digit x ≤ 5 ∧ digit x ≠ 0 := by
  unfold digit
  split_ifs <;> decide

lemma close_digit (x : ℝ) (hlo : -6 ≤ x) (hhi : x ≤ 6) :
    x - 1 ≤ (digit x : ℝ) ∧ (digit x : ℝ) ≤ x + 1 := by
  unfold digit
  split_ifs <;> norm_num <;> constructor <;> linarith

def scale (n : ℕ) : ℝ := 2 ^ (n + 6)

lemma scale_bound (n : ℕ) : 64 ≤ scale n := by
  calc (64 : ℝ) = 2 ^ 6 := by norm_num
       _ ≤ 2 ^ (n + 6) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma scale_succ (n : ℕ) : scale (n+1) = 2 * scale n := by
  unfold scale
  rw [show n + 1 + 6 = (n + 6) + 1 by omega, pow_succ, mul_comm]

noncomputable def state : ℕ → ℝ
  | 0 => 0
  | n+1 =>
    let x := state n
    let d : ℝ := digit x
    4 * (x - scale n * d / (scale n + d))

lemma state_bounds (n : ℕ) : -6 ≤ state n ∧ state n ≤ 6 := by
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    let x := state n
    let d : ℝ := digit x
    let T := scale n
    have ht : 64 ≤ T := scale_bound n
    have hd₁ : -5 ≤ d := by dsimp only [d]; exact_mod_cast (digit_bounds x).1
    have hd₂ : d ≤ 5 := by dsimp only [d]; exact_mod_cast (digit_bounds x).2.1
    have hclose := close_digit x ih.1 ih.2
    change x - 1 ≤ d ∧ d ≤ x + 1 at hclose
    have hpos : 0 < T + d := by linarith
    have hlo : d - 1/2 ≤ T*d/(T+d) := by
      apply (le_div_iff₀ hpos).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 5-d) (by linarith : 0 ≤ 5+d)]
    have hhi : T*d/(T+d) ≤ d := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith [sq_nonneg d]
    change -6 ≤ 4*(x - T*d/(T+d)) ∧ 4*(x - T*d/(T+d)) ≤ 6
    constructor <;> linarith

noncomputable def remainder (n : ℕ) : ℝ := 2 / scale n - state n / (scale n)^2

lemma remainder_step (n : ℕ) :
    1 / (scale n + (digit (state n) : ℝ)) = remainder n - remainder (n+1) := by
  have ht := scale_bound n
  have hd : (-5:ℝ) ≤ digit (state n) := by exact_mod_cast (digit_bounds _).1
  have hn : scale n ≠ 0 := by linarith
  have hp : scale n + (digit (state n) : ℝ) ≠ 0 := by linarith
  simp only [remainder, state, scale_succ]
  field_simp
  ring

lemma remainder_zero : Tendsto remainder atTop (𝓝 0) := by
  have ht : Tendsto scale atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).comp (tendsto_add_atTop_nat 6)
  apply squeeze_zero (g := fun n => 3 / scale n)
  · intro n
    have h := scale_bound n
    have hs := (state_bounds n).2
    have hpos : 0 < scale n := by linarith
    dsimp [remainder]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hpos.le]
  · intro n
    have h := scale_bound n
    have hs := (state_bounds n).1
    have hpos : 0 < scale n := by linarith
    dsimp [remainder]
    rw [sub_le_iff_le_add]
    field_simp
    nlinarith
  · exact ht.const_div_atTop 3

noncomputable def shift (n : ℕ) : ℤ :=
  if n < 6 then 64 - 2 ^ n else digit (state (n-6))

lemma tail_shift (n : ℕ) : shift (n+6) = digit (state n) := by simp [shift]

noncomputable def term (n : ℕ) : ℝ := 1 / ((2:ℝ)^n + (shift n : ℝ))

lemma tail_sum : HasSum (fun n => term (n+6)) (1/32) := by
  have heq (n : ℕ) : term (n+6) = remainder n - remainder (n+1) := by
    simpa only [term, tail_shift, scale] using remainder_step n
  apply (hasSum_iff_tendsto_nat_of_nonneg ?_ _).mpr
  · simp_rw [heq, sum_range_sub']
    have hzero : remainder 0 = 1/32 := by norm_num [remainder, state, scale]
    simpa [hzero] using (tendsto_const_nhds (x := remainder 0)).sub remainder_zero
  · intro n
    rw [term, tail_shift]
    have h := scale_bound n
    have hd : (-5 : ℝ) ≤ digit (state n) := by exact_mod_cast (digit_bounds _).1
    change 0 ≤ 1 / (scale n + _)
    apply one_div_nonneg.mpr
    linarith

lemma full_sum : HasSum term (1/8) := by
  have hhead : ∑ n ∈ range 6, term n = 6/64 := by
    norm_num [sum_range_succ, term, shift]
  apply (hasSum_nat_add_iff' 6).mp
  rw [hhead, show (1/8:ℝ) - 6/64 = 1/32 by norm_num]
  exact tail_sum

end OMA.Ahmes

open OMA.Ahmes in
theorem OMA.solution : type_of% @Erdos264.erdos_264.parts.i := by
  intro h
  have hrange (n : ℕ) : -5 ≤ shift n ∧ shift n ≤ 64 ∧ shift n ≠ 0 := by
    unfold shift
    split_ifs with hn
    · interval_cases n <;> decide
    · have hd := digit_bounds (state (n-6))
      omega
  have hpos (n : ℕ) : (0:ℤ) < (2:ℤ)^n + shift n := by
    by_cases hn : n < 6
    · simp [shift, hn]
    · have hpow : (64:ℤ) ≤ 2^n := by
        calc (64:ℤ) = 2^6 := by norm_num
             _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) (by omega)
      have hlow := (hrange n).1
      omega
  have hi := h shift ⟨64, by rintro _ ⟨n,rfl⟩; exact (hrange n).2.1⟩
    ⟨-5, by rintro _ ⟨n,rfl⟩; exact (hrange n).1⟩
    (by rintro ⟨n,hn⟩; push_cast at hn; exact (hpos n).ne' hn)
    (by rintro ⟨n,hn⟩; exact (hrange n).2.2 hn)
  have hx : Irrational (∑' n, term n) := by simpa [term] using hi
  rw [full_sum.tsum_eq] at hx
  exact hx ⟨(1/8 : ℚ), by norm_num⟩
