import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R1

/-! Fermat's little theorem gives the pseudoprime congruence modulo each
prime divisor; squarefreeness then gives divisibility by the whole modulus. -/

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3 := by
  intro n hn hcom hsf hex b hb hc
  refine ⟨?_,hcom,hn⟩
  let t := b^(n-1)-1
  change n ∣ t
  by_cases ht : t=0
  · simp [ht]
  apply (Nat.factorization_le_iff_dvd hsf.ne_zero ht).mp
  intro p
  by_cases hpn : p.Prime ∧ p∣n
  · obtain ⟨hp,hd⟩ := hpn
    have hcop := (hc.of_dvd_left hd).symm
    obtain ⟨j,hj⟩ := hex p hp hd
    have e := (Nat.ModEq.pow_totient hcop).pow j
    rw [Nat.totient_prime hp, ← pow_mul, ← hj, one_pow] at e
    have hpd : p ∣ t := (Nat.modEq_iff_dvd' (one_le_pow₀ hb)).mp e.symm
    exact (hsf.natFactorization_le_one p).trans ((hp.dvd_iff_one_le_factorization ht).mp hpd)
  · by_cases hp : p.Prime
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun hd => hpn ⟨hp,hd⟩)]
      exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
