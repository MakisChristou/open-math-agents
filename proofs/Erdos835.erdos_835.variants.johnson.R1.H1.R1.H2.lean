import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

/-! In a proper edge coloring of an odd complete graph with as many colors as
vertices, every vertex misses exactly one color. Each color must be missing
somewhere by the degree sum formula. The missing colors therefore give a bijection. -/

open Finset SimpleGraph

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H2 := by
  classical
  intro k hk Q hQ e symm proper
  let U (a : Q) := (Q.erase a.val).image (e a.val)
  have ucard (a : Q) : (U a).card = k := by
    have inj : Set.InjOn (e a.val) (↑(Q.erase a.val) : Set _) := by
      intro x hx y hy he
      obtain ⟨hxa,hxQ⟩ := Finset.mem_erase.mp hx
      obtain ⟨hya,hyQ⟩ := Finset.mem_erase.mp hy
      by_contra hn
      exact proper a.val a.2 x hxQ y hyQ hxa hya hn he
    change ((Q.erase a.val).image (e a.val)).card = k
    rw [Finset.card_image_of_injOn inj,Finset.card_erase_of_mem a.2,hQ]
    omega
  have single (a : Q) : ∃ i, (U a)ᶜ={i} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_compl,Fintype.card_fin,ucard]
    omega
  choose miss hm using single
  have miss_iff (a : Q) (i : Fin (k+1)) :
      i=miss a ↔ ∀ t ∈ Q, t≠a.val → i≠e a.val t := by
    have eq : i ∈ (U a)ᶜ ↔ i=miss a := by rw [hm,Finset.mem_singleton]
    rw [← eq,Finset.mem_compl]
    constructor
    · intro hn t ht hta he
      exact hn (Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr ⟨hta,ht⟩,he.symm⟩)
    · intro hf hi
      obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hi
      obtain ⟨hta,ht⟩ := Finset.mem_erase.mp ht
      exact hf t ht hta he.symm
  have onto : Function.Surjective miss := by
    intro i
    by_contra! hn
    let H : SimpleGraph Q :=
      { Adj := fun a b => a≠b ∧ e a.val b.val=i
        symm := by
          constructor
          intro a b h
          exact ⟨h.1.symm,(symm b.val b.2 a.val a.2).trans h.2⟩
        loopless := ⟨fun a h => h.1 rfl⟩ }
    have deg (a : Q) : H.degree a=1 := by
      apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      have hsome := mt (miss_iff a i).2 (Ne.symm (hn a))
      push Not at hsome
      obtain ⟨b,hb,hba,he⟩ := hsome
      let v : Q := ⟨b,hb⟩
      refine ⟨v,⟨fun h => hba (congrArg Subtype.val h.symm),he.symm⟩,?_⟩
      intro c hc
      apply Subtype.ext
      by_contra hne
      have hca : c.val≠a.val := fun eq => hc.1 (Subtype.ext eq.symm)
      exact proper a.val a.2 c.val c.2 b hb hca hba hne (hc.2.trans he)
    have h := H.sum_degrees_eq_twice_card_edges
    simp only [deg,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_coe,hQ] at h
    obtain ⟨m,hm⟩ := hk
    omega
  let E : Fin (k+1) ≃ Q := Fintype.equivOfCardEq (by simp [hQ])
  have hi : Function.Injective (E ∘ miss) := Finite.injective_iff_surjective.mpr (E.surjective.comp onto)
  intro a ha b hb hne i j hia hjb heq
  have ha' := (miss_iff ⟨a,ha⟩ i).2 hia
  have hb' := (miss_iff ⟨b,hb⟩ j).2 hjb
  exact hne (congrArg Subtype.val (hi (congrArg E (ha'.symm.trans (heq.trans hb')))))
