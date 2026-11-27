import OMAReductions.R_Erdos813_erdos_813_variants_bucic_sudakov_R1

/-! At least seven vertices force a triangle, and a nonpositive power of n is at most one. -/
open Filter Erdos813

theorem OMA.solution : OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H1 := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with n hn
  have hclique : 3 ≤ h n := by
    apply le_csInf
    · exact ⟨_, ⊤,everySevenHasTriangle_top n,rfl⟩
    · rintro k ⟨G,hG,rfl⟩
      obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := 7) (by simpa)
      obtain ⟨t,_,htc⟩ := hG T ht
      exact htc.card_eq ▸ htc.isClique.card_le_cliqueNum
  exact (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n))
    (by linarith)).trans (by exact_mod_cast (by omega : 1 ≤ h n))
