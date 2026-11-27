import OMAReductions.R_Erdos384_erdos_384_R1

/-! The cases k = 2 and k = 3 of Ecklund's theorem on binomial coefficients. -/
namespace OMA.EcklundSmall

lemma half_dvd (n : ℕ) : n/2 ∣ n.choose 2 := by
  have h := Nat.choose_succ_right_eq n 1
  simp only [Nat.choose_one_right] at h
  by_cases he : n%2=0
  · refine ⟨n-1,?_⟩
    have hn : n=2*(n/2) := by omega
    nlinarith [congrArg (· * (n-1)) hn]
  · refine ⟨n,?_⟩
    have hn : n-1=2*(n/2) := by omega
    nlinarith [congrArg (n * ·) hn]

lemma small_factor {u v n : ℕ} (hu : 1<u) (hd : u ∣ v) (hsize : 2*u≤n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ 2*p≤n := by
  exact ⟨u.minFac,Nat.minFac_prime (by omega),(Nat.minFac_dvd u).trans hd,
    by have := Nat.minFac_le (by omega : 0<u); omega⟩

end OMA.EcklundSmall

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := by
  intro n k hl hu hnk he
  rcases (show k=2 ∨ k=3 by omega) with rfl|rfl
  · exact OMA.EcklundSmall.small_factor (u:=n/2) (by omega) (OMA.EcklundSmall.half_dvd n) (by omega)
  · by_cases hn : n≤7
    · have hn6 : n=6 := by
        have hn7 : n≠7 := fun eq => he (by simp [eq])
        omega
      subst n
      exact ⟨2,by decide,by decide,by decide⟩
    have hh : n/2 ∣ n.choose 3 * 3 := by
      rw [Nat.choose_succ_right_eq n 2]
      exact dvd_mul_of_dvd_left (OMA.EcklundSmall.half_dvd n) _
    by_cases h3 : 3 ∣ n/2
    · obtain ⟨t,ht⟩ := h3
      rw [ht,mul_comm (n.choose 3)] at hh
      exact OMA.EcklundSmall.small_factor (u:=t) (by omega) (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<3) hh) (by omega)
    · have hc : (n/2).Coprime 3 := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 h3 |>.symm
      exact OMA.EcklundSmall.small_factor (u:=n/2) (by omega) (hc.dvd_of_dvd_mul_right hh) (by omega)
