import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2

/-! An optimal coloring is balanced on the blocks containing any proper face.
Inclusion-exclusion at an odd block shows that its disjoint blocks exhaust the
other colors. This is the intersecting-block argument of Mendelsohn. -/

open Finset

namespace OMA.BlockBalance

private theorem weighted_disjoint {α : Type} [Fintype α] [DecidableEq α]
    (k : ℕ) (w : Finset α → ℤ)
    (D : Finset (Finset α)) (hD : ∀ B ∈ D, B.card=k)
    (F : Finset α → ℤ) (df : ∀ T, F T = ∑ B ∈ D, if T ⊆ B then w B else 0)
    (top : ∀ T : Finset α, T.card+1=k → F T=0)
    (A : Finset α) (hA : A∈D) :
    (∑ B ∈ D, if Disjoint A B then w B else 0) = (-1:ℤ)^k*w A := by
  classical
  let rec low (T : Finset α) (ht : T.card < k) : F T=0 := by
    by_cases he : T.card+1=k
    · exact top T he
    have step : ∑ x ∈ Tᶜ, F (insert x T) = ((k-T.card : ℕ):ℤ) * F T := by
      simp_rw [df]
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro B hB
      by_cases h : T⊆B
      · simp only [insert_subset_iff, h, and_true, if_true, ← sum_filter, sum_const, nsmul_eq_mul]
        congr 2
        have seteq : (Tᶜ.filter (fun x => x∈B)) = B \ T := by ext; simp [and_comm]
        rw [seteq,card_sdiff_of_subset h,hD B hB]
      · simp [insert_subset_iff,h]
    have hzero : ∑ x ∈ Tᶜ, F (insert x T) = 0 := by
      apply sum_eq_zero
      intro x hx
      apply low (insert x T)
      rw [card_insert_of_notMem (mem_compl.mp hx)]
      omega
    rw [hzero] at step
    exact (mul_eq_zero.mp step.symm).resolve_left (by exact_mod_cast Nat.sub_ne_zero_of_lt ht)
  termination_by k-T.card
  decreasing_by rw [card_insert_of_notMem (mem_compl.mp hx)]; omega
  have fa : F A = w A := by
    rw [df]
    rw [← (if_pos (Subset.rfl : A ⊆ A) : (if A ⊆ A then w A else 0) = w A)]
    apply sum_eq_single_of_mem A hA
    · intro b hb hba
      exact if_neg (fun hs => hba (eq_of_subset_of_card_le hs (by rw [hD A hA,hD b hb])).symm)
  have sgn : (∑ T ∈ A.powerset, (-1:ℤ)^T.card * F T) = (-1:ℤ)^k*w A := by
    rw [← hD A hA, ← fa]
    apply sum_eq_single_of_mem A (mem_powerset.mpr (Subset.rfl))
    intro T hT hne
    rw [low T (by rw [← hD A hA]; exact card_lt_card ⟨mem_powerset.mp hT, fun hs => hne (Subset.antisymm (mem_powerset.mp hT) hs)⟩), mul_zero]
  rw [← sgn]
  simp_rw [df, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  have parts : (A.powerset.filter (· ⊆ B)) = (A∩B).powerset := by
    ext T
    simp only [mem_filter,mem_powerset,Finset.subset_inter_iff]
  calc
    _ = (if A∩B=∅ then 1 else 0 : ℤ)*w B := by
      by_cases hd : Disjoint A B
      · simp [hd,Finset.disjoint_iff_inter_eq_empty.mp hd]
      · have hne : A∩B ≠ ∅ := fun he => hd (Finset.disjoint_iff_inter_eq_empty.mpr he)
        simp [hd,hne]
    _ = _ := by
      rw [← Finset.sum_powerset_neg_one_pow_card, ← parts, Finset.sum_filter, Finset.sum_mul]
      apply sum_congr rfl
      intro T _
      split_ifs <;> simp

theorem result : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H3 := by
  classical
  intro p hp hp5 c proper A B hA hB hdis heq
  let k := p-2
  let D := (univ : Finset (Fin (2*p-3))).powersetCard k
  let w (S : Finset (Fin (2*p-3))) : ℤ := (if c S=c A then (p:ℤ) else 0)-1
  let F (T : Finset (Fin (2*p-3))) := ∑ S ∈ D, if T⊆S then w S else 0
  have memD (S : Finset (Fin (2*p-3))) : S ∈ D ↔ S.card=k := by simp [D]
  have face (T : Finset (Fin (2*p-3))) (ht : T.card+1=k) : F T=0 := by
    let E := D.filter (T⊆·)
    have repr : E=Tᶜ.image (fun x => insert x T) := by
      ext S
      simp only [E,mem_filter,memD,mem_image,mem_compl]
      rw [exists_eq_insert_iff, ht]
      exact ⟨fun h => ⟨h.2,h.1.symm⟩,fun h => ⟨h.2.symm,h.1⟩⟩
    have ic : Set.InjOn (fun x => insert x T) (↑(Tᶜ) : Set _) := by
      intro x hx y _ h
      change insert x T = insert y T at h
      have hm := mem_insert_self x T
      rw [h] at hm
      exact (mem_insert.mp hm).resolve_right (mem_compl.mp hx)
    have ec : E.card=p := by
      rw [repr,card_image_of_injOn ic,card_compl,Fintype.card_fin]
      dsimp [k] at ht
      omega
    have ci : Set.InjOn c (↑E : Set _) := by
      intro U hU V hV eq
      obtain ⟨cu,tu⟩ := mem_filter.mp hU
      obtain ⟨cv,tv⟩ := mem_filter.mp hV
      have hu := (memD U).mp cu
      have hv := (memD V).mp cv
      by_contra ne
      apply proper U V hu hv _ eq
      have lo := card_le_card (subset_inter tu tv)
      have hi := card_le_card (inter_subset_left (s₁:=U) (s₂:=V))
      have hne : (U∩V).card ≠ k := by
        intro he
        exact ne ((eq_of_subset_of_card_le inter_subset_left (by omega)).symm.trans
          (eq_of_subset_of_card_le inter_subset_right (by omega)))
      dsimp [k] at *
      omega
    have allc : E.image c = univ := eq_univ_of_card _ (by rw [card_image_of_injOn ci,ec,Fintype.card_fin])
    change (∑ S ∈ D, if T⊆S then w S else 0)=0
    rw [← sum_filter]
    change (∑ S ∈ E, w S)=0
    calc
      _ = ∑ i ∈ E.image c, ((if i=c A then (p:ℤ) else 0)-1) := by rw [sum_image ci]
      _ = 0 := by rw [allc,sum_sub_distrib]; simp
  have d := weighted_disjoint k w D (fun S h => (memD S).mp h) F (fun _ => rfl) face A ((memD A).mpr hA)
  have odd : Odd k := by
    obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨m-1, by dsimp [k]; omega⟩
  rw [odd.neg_one_pow] at d
  let E := D.filter (Disjoint A)
  have sets : E=(Aᶜ).powersetCard k := by
    ext S
    simp only [E,mem_filter,memD,mem_powersetCard,subset_compl_iff_disjoint_left,and_comm]
  have ec : E.card=p-1 := by
    rw [sets,card_powersetCard,card_compl,Fintype.card_fin,hA]
    change (2*p-3-(p-2)).choose (p-2)=p-1
    rw [show 2*p-3-(p-2)=(p-2)+1 by omega,Nat.choose_succ_self_right]
    omega
  rw [← sum_filter] at d
  change (∑ S ∈ E,w S)=(-1)*w A at d
  simp only [w, if_true, sum_sub_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_one] at d
  rw [ec] at d
  have hb : B ∈ E.filter (fun S => c S=c A) := mem_filter.mpr ⟨mem_filter.mpr ⟨(memD B).mpr hB,hdis⟩,heq.symm⟩
  have hpos : 0 < (E.filter (fun S => c S=c A)).card := card_pos.mpr ⟨B,hb⟩
  have hf : ((E.filter (fun S => c S=c A)).card : ℤ)*p > 0 := by positivity
  omega

end OMA.BlockBalance

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H3 := OMA.BlockBalance.result
