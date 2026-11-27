import OMAReductions.R_Erdos694_erdos_694_variants_inf_unique_R1

/-! A prime large enough cannot divide a preimage of n, since p−1 would divide
n. If a scaled preimage contained p twice, its totient would be divisible by p. -/

theorem OMA.solution : OMA.R_Erdos694_erdos_694_variants_inf_unique_R1.H2 := by
  intro n p hn hp hpn
  constructor
  · intro m hm
    have hnd : ¬ p ∣ m := by
      intro hd
      have h := Nat.totient_dvd_of_dvd hd
      rw [Nat.totient_prime hp, hm] at h
      have := Nat.le_of_dvd hn h
      omega
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hnd,hm,Nat.mul_comm]
  · rintro x hx ⟨m,rfl⟩
    have hnd : ¬ p ∣ m := by
      intro hd
      rw [Nat.totient_mul_of_prime_of_dvd hp hd] at hx
      have h : p ∣ n*(p-1) := ⟨m.totient,hx.symm⟩
      rcases (hp.dvd_mul.mp h) with h | h
      · have := Nat.le_of_dvd hn h
        omega
      · have := Nat.le_of_dvd (by have := hp.one_lt; omega : 0<p-1) h
        omega
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hnd,Nat.mul_comm n] at hx
    exact ⟨m,Nat.eq_of_mul_eq_mul_left (by have := hp.one_lt; omega) hx,rfl⟩
