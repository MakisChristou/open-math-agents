import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1

/-! Existence of a stable marriage for complete strict preferences (Gale and Shapley).
We construct mutually consistent offers and acceptances by a monotone fixed point.
A man offers through the first woman willing to accept him, and a woman accepts
through the first man offering to her, in their respective preference orders. -/

namespace OMA.StableOffers
open StableMarriage

abbrev Rel (n : ℕ) := Fin n → Fin n → Prop

def offers {n : ℕ} (p : Profile n) (accepted : Rel n) : Rel n :=
  fun m w => ∀ v, p.manRank m v < p.manRank m w → ¬ accepted m v

def accepts {n : ℕ} (p : Profile n) (offered : Rel n) : Rel n :=
  fun m w => ∀ k, p.womanRank w k < p.womanRank w m → ¬ offered k w

def round {n : ℕ} (p : Profile n) : Rel n →o Rel n where
  toFun s := accepts p (offers p s)
  monotone' := by
    intro s t h m w hm k hk hkt
    exact hm k hk (fun v hv hsv => hkt v hv (h k v hsv))

lemma best {n : ℕ} (rank : Equiv.Perm (Fin n)) (S : Fin n → Prop)
    (h : ∃ i, S i) : ∃ i, S i ∧ ∀ j, rank j < rank i → ¬ S j := by
  classical
  let s := Finset.univ.filter S
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := s.exists_min_image rank hs
  refine ⟨i, (Finset.mem_filter.mp hi).2, fun j hj hsj => ?_⟩
  exact hj.not_ge (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsj⟩))

lemma stable_exists {n : ℕ} (p : Profile n) : ∃ μ : Matching n, IsStable p μ := by
  classical
  let A := (round p).lfp
  let O := offers p A
  have accept_iff (m w) : A m w ↔ accepts p O m w := by
    change (round p).lfp m w ↔ (round p) (round p).lfp m w
    rw [(round p).map_lfp]
  let M : Rel n := fun m w => O m w ∧ A m w
  have one_w {m w v} (h : M m w) (h' : M m v) : w = v := by
    apply (p.manRank m).injective
    rcases lt_trichotomy (p.manRank m w) (p.manRank m v) with lt|eq|gt
    · exact (h'.1 w lt h.2).elim
    · exact eq
    · exact (h.1 v gt h'.2).elim
  have one_m {m k w} (h : M m w) (h' : M k w) : m = k := by
    apply (p.womanRank w).injective
    rcases lt_trichotomy (p.womanRank w m) (p.womanRank w k) with lt|eq|gt
    · exact ((accept_iff k w).1 h'.2 m lt h.1).elim
    · exact eq
    · exact ((accept_iff m w).1 h.2 k gt h'.1).elim
  have total (m) : ∃ w, M m w := by
    by_contra missing
    have none (w) : ¬ A m w := by
      intro hw
      obtain ⟨v,hv,hbest⟩ := best (p.manRank m) (A m) ⟨w,hw⟩
      exact missing ⟨v,hbest,hv⟩
    have all_w (w) : ∃ k, M k w := by
      have hm : O m w := fun v _ => none v
      obtain ⟨k,hk,hbest⟩ := best (p.womanRank w) (fun j => O j w) ⟨m,hm⟩
      exact ⟨k,hk,(accept_iff k w).2 hbest⟩
    choose f hf using all_w
    have fi : Function.Injective f := by
      intro w v eq
      exact one_w (hf w) (eq.symm ▸ hf v)
    obtain ⟨w,hw⟩ := Finite.surjective_of_injective fi m
    exact missing ⟨w,hw ▸ hf w⟩
  choose g hg using total
  have gi : Function.Injective g := by
    intro m k eq
    exact one_m (hg m) (eq.symm ▸ hg k)
  let μ : Matching n := Equiv.ofBijective g ⟨gi,Finite.surjective_of_injective gi⟩
  refine ⟨μ, fun m w hblock => ?_⟩
  obtain ⟨_,hm,hw⟩ := hblock
  have offered : O m w := fun v hv => (hg m).1 v (hv.trans hm)
  have paired : M (μ.symm w) w := by
    have hp : M (μ.symm w) (μ (μ.symm w)) := hg _
    simpa only [Equiv.apply_symm_apply] using hp
  exact (accept_iff _ _).1 paired.2 m hw offered

end OMA.StableOffers

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  classical
  intro n p
  obtain ⟨μ,hμ⟩ := OMA.StableOffers.stable_exists p
  exact Fintype.card_pos_iff.mpr ⟨⟨μ,hμ⟩⟩
