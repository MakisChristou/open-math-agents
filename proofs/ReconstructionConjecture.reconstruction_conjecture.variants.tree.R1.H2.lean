import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

/-! Count pairs consisting of an induced copy and a vertex outside the copy.
The deleted-vertex deck determines this count, and each copy contributes the
same positive number of pairs. This is Kelly's counting lemma. -/

open scoped Classical
open Finset SimpleGraph ReconstructionConjecture

namespace OMA.KellyDeck

private noncomputable def copies {V U : Type} [Fintype V] (G : SimpleGraph V) (Q : SimpleGraph U) :
    Finset (Finset V) := by
  classical
  exact univ.filter (fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g Q))

private theorem count {V U : Type} [Fintype V] [Fintype U] (G : SimpleGraph V) (Q : SimpleGraph U) :
    (∑ v : V, ((copies G Q).filter (fun S => v∉S)).card) =
    (copies G Q).card*(Fintype.card V - Fintype.card U) := by
  classical
  simp only [Finset.card_filter]
  rw [sum_comm]
  calc
    _ = ∑ _S ∈ copies G Q, (Fintype.card V-Fintype.card U) := by
      apply sum_congr rfl
      intro S hS
      obtain ⟨f⟩ := (mem_filter.mp hS).2
      have hcard : S.card=Fintype.card U := by simpa using Fintype.card_congr f.toEquiv
      have hcompl : (univ.filter (fun v : V => v∉S)) = Sᶜ := by ext; simp
      rw [← card_filter,hcompl,card_compl,hcard]
    _ = _ := by simp

private theorem matching_deletions {V W U : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (Q : SimpleGraph U) (v : V) (w : W)
    (f : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ((copies G Q).filter (fun S => v∉S)).card = ((copies H Q).filter (fun S => w∉S)).card := by
  classical
  let f' : {x : V // x≠v} ≃ {y : W // y≠w} := f.toEquiv
  let e := (Equiv.optionSubtypeNe v).symm.trans (f'.optionCongr.trans (Equiv.optionSubtypeNe w))
  have ev : e v=w := by simp [e]
  have agree (x : V) (hx : x≠v) : e x=(f ⟨x,hx⟩).val := by
    simp only [e,Equiv.trans_apply,Equiv.optionSubtypeNe_symm_of_ne hx]
    rfl
  apply card_equiv e.finsetCongr
  intro S
  let T := S.map e.toEmbedding
  have em (x : V) : e x ∈ T ↔ x ∈ S := mem_map' e.toEmbedding
  have ew : w∈T ↔ v∈S := ev ▸ em v
  change (S ∈ (copies G Q).filter _) ↔ (T ∈ (copies H Q).filter _)
  simp only [mem_filter,copies,mem_univ,true_and,ew]
  by_cases hv : v∈S
  · simp [hv]
  simp only [hv, not_false_eq_true, and_true]
  let r : G.induce (S : Set V) ≃g H.induce (T : Set W) :=
    { toEquiv := e.subtypeEquiv (fun x => (em x).symm)
      map_rel_iff' := by
        intro x y
        have hx : x.val≠v := fun h => hv (h ▸ x.2)
        have hy : y.val≠v := fun h => hv (h ▸ y.2)
        change H.Adj (e x.val) (e y.val) ↔ G.Adj x.val y.val
        rw [agree _ hx,agree _ hy]
        exact f.map_rel_iff }
  exact ⟨fun ⟨s⟩ => ⟨s.comp r.symm⟩,fun ⟨s⟩ => ⟨s.comp r⟩⟩

theorem result : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H2 := by
  classical
  rintro V W _ _ _ G H _ _ ⟨σ,deck⟩ U _ Q hlt
  have hcounts : (copies G Q).card*(Fintype.card V-Fintype.card U) =
      (copies H Q).card*(Fintype.card W-Fintype.card U) := by
    rw [← count,← count]
    apply Fintype.sum_equiv σ
    intro v
    exact matching_deletions G H Q v (σ v) (deck v).some
  rw [← Fintype.card_congr σ] at hcounts
  have hh := Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hlt) hcounts
  have card {X : Type} [Fintype X] (F : SimpleGraph X) :
      {S : Finset X | Nonempty (F.induce (S : Set X) ≃g Q)}.ncard = (copies F Q).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext S
    simp [copies]
  rwa [card,card]

end OMA.KellyDeck

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H2 :=
  OMA.KellyDeck.result
