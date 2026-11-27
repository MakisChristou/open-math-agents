import OMAReductions.R_OeisA215926_conjecture_2_R1

/-! Summing the divisors of 2ʲq when q is an odd prime. -/

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hgt hlt
  have hc : (2^j).Coprime q := ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left _
  have hs (i : ℕ) : (∑ t ∈ Finset.range (i+1), 2^t) + 1 = 2*2^i := by
    induction i with
    | zero => decide
    | succ i ih => rw [Finset.sum_range_succ,pow_succ]; omega
  have hdiv := Nat.sum_divisors_prime_pow (k := j) (f := fun a => a) Nat.prime_two
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.mul_pos (by positivity) hq.pos),
    Nat.abundant_iff_sum_divisors,hc.sum_divisors_mul,hdiv,hq.divisors]
  simp only [Finset.sum_insert (show 1 ∉ ({q} : Finset ℕ) by simpa using hq.ne_one.symm),
    Finset.sum_singleton]
  have h := hs j
  rcases le_total (2*(2^j*q)) ((∑ t ∈ Finset.range (j+1), 2^t)*(1+q)) with hle|hle
  · omega
  · left
    nlinarith [congrArg (fun a : ℕ => a*q) h]
