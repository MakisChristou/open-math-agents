import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1

/-! Extremal numbers for a graph split into two parts with no edges between them.
Delete the edges incident to a copy of the first part, then find the second part
in the remaining graph. Positive degree keeps its vertices outside the first copy. -/
namespace OMA.ComponentExtremal
open SimpleGraph Finset
open scoped Classical

lemma cut_bound {q : ℕ} (G : SimpleGraph (Fin q)) (s : Set (Fin q))
    (cut : ∀ ⦃x y⦄, G.Adj x y → (x ∈ s ↔ y ∈ s))
    (nonisolated : ∀ x, ∃ y, G.Adj x y) (n : ℕ) :
    extremalNumber n G ≤ extremalNumber n (G.induce s) +
      extremalNumber n (G.induce sᶜ) + q*n := by
  classical
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro H _ hfree
  simp only [Fintype.card_fin] at *
  by_contra! hcount
  have big₁ : extremalNumber (Fintype.card (Fin n)) (G.induce s) < H.edgeFinset.card := by
    simpa only [Fintype.card_fin] using (show extremalNumber n (G.induce s) < H.edgeFinset.card by omega)
  obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset big₁
  let U := Finset.univ.image (fun x : s => f x)
  let E := U.biUnion (fun v => H.incidenceFinset v)
  let K := H.deleteEdges (E : Set (Sym2 (Fin n)))
  have hu : U.card ≤ q := calc
    U.card ≤ Fintype.card s := by simpa [U] using (Finset.card_image_le (s:=Finset.univ) (f:=fun x : s => f x))
    _ ≤ q := by simpa using Fintype.card_le_of_injective (fun x : s => x.val) Subtype.val_injective
  have he : E.card ≤ q*n := calc
    E.card ≤ ∑ x ∈ U, (H.incidenceFinset x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ U, n := Finset.sum_le_sum fun x _ => by
      simpa only [card_incidenceFinset_eq_degree,Fintype.card_fin] using (H.degree_lt_card_verts x).le
    _ ≤ q*n := by simpa using Nat.mul_le_mul_right n hu
  have hd : H.edgeFinset.card ≤ K.edgeFinset.card + E.card := by
    change H.edgeFinset.card ≤ (H.deleteEdges (E : Set _)).edgeFinset.card + E.card
    rw [edgeFinset_deleteEdges]
    exact Finset.card_le_card_sdiff_add_card
  have big₂ : extremalNumber (Fintype.card (Fin n)) (G.induce sᶜ) < K.edgeFinset.card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset big₂
  have outside (y : ↥sᶜ) : g y ∉ U := by
    intro hy
    obtain ⟨z,hz⟩ := nonisolated y
    have hzc : z ∈ sᶜ := fun hzs => y.2 ((cut hz).2 hzs)
    let z' : ↥sᶜ := ⟨z,hzc⟩
    have h := g.toHom.map_adj (show (G.induce sᶜ).Adj y z' from hz)
    obtain ⟨hH,hn⟩ := SimpleGraph.deleteEdges_adj.mp h
    exact hn (Finset.mem_biUnion.mpr ⟨g y, hy, (H.mem_incidenceFinset _ _).mpr
      (H.mk'_mem_incidenceSet_left_iff.mpr hH)⟩)
  let j (v : Fin q) : Fin n := if hv : v ∈ s then f ⟨v,hv⟩ else g ⟨v,hv⟩
  have inside (v : s) : f v ∈ U := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  apply hfree
  refine ⟨⟨⟨j,?_⟩,?_⟩⟩
  · intro x y hxy
    by_cases hx : x ∈ s
    · have hy := (cut hxy).1 hx
      simpa only [j,dif_pos hx,dif_pos hy,Copy.toHom_apply] using
        f.toHom.map_adj (show (G.induce s).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy)
    · have hy := mt (cut hxy).2 hx
      simpa only [j,dif_neg hx,dif_neg hy,Copy.toHom_apply] using SimpleGraph.deleteEdges_adj.mp
        (g.toHom.map_adj (show (G.induce sᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy)) |>.1
  · intro x y eq
    change j x = j y at eq
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · simp only [j,dif_pos hx,dif_pos hy] at eq
      exact congrArg Subtype.val (f.injective eq)
    · simp only [j,dif_pos hx,dif_neg hy] at eq
      exact (outside ⟨y,hy⟩ (eq ▸ inside ⟨x,hx⟩)).elim
    · simp only [j,dif_neg hx,dif_pos hy] at eq
      exact (outside ⟨x,hx⟩ (eq.symm ▸ inside ⟨y,hy⟩)).elim
    · simp only [j,dif_neg hx,dif_neg hy] at eq
      exact congrArg Subtype.val (g.injective eq)

lemma degree_cut {q : ℕ} (G : SimpleGraph (Fin q)) (s : Set (Fin q))
    (closed : ∀ ⦃x y⦄, x ∈ s → G.Adj x y → y ∈ s) (x : s) :
    Nat.card ((G.induce s).neighborSet x) = Nat.card (G.neighborSet x.val) := by
  classical
  apply Nat.card_congr
  exact { toFun := fun y => ⟨y.val.val,y.2⟩
          invFun := fun y => ⟨⟨y.val,closed x.2 y.2⟩,y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

end OMA.ComponentExtremal
open SimpleGraph
open scoped Classical

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H1 := by
  classical
  intro q G hq degree disc
  let a : Fin q := ⟨0,hq⟩
  have hb : ∃ b, ¬ G.Reachable a b := by
    by_contra! h
    exact disc (G.connected_iff_exists_forall_reachable.mpr ⟨a,h⟩)
  obtain ⟨b,hb⟩ := hb
  let s : Set (Fin q) := {x | G.Reachable a x}
  have ha : a ∈ s := SimpleGraph.Reachable.rfl
  have cut {x y} (hxy : G.Adj x y) : x ∈ s ↔ y ∈ s :=
    ⟨fun hx => hx.trans hxy.reachable,fun hy => hy.trans hxy.symm.reachable⟩
  let e := (Fintype.equivFin s).symm
  let d := (Fintype.equivFin ↥sᶜ).symm
  let F := (G.induce s).comap e
  let J := (G.induce sᶜ).comap d
  let ei : F ≃g G.induce s := SimpleGraph.Iso.comap e (G.induce s)
  let di : J ≃g G.induce sᶜ := SimpleGraph.Iso.comap d (G.induce sᶜ)
  refine ⟨_,_,F,J,Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩,?_,
    Fintype.card_pos_iff.mpr ⟨⟨b,hb⟩⟩,?_,
    ⟨(SimpleGraph.Copy.induce G s).comp ei.toCopy⟩,
    ⟨(SimpleGraph.Copy.induce G sᶜ).comp di.toCopy⟩,?_,?_,?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_lt (p:=fun x => x ∈ s) hb
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_lt (p:=fun x => x ∈ sᶜ) (x:=a) (fun h => h ha)
  · intro x
    have hd := degree (ei x).val
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ⊢
    rw [Nat.card_congr (ei.mapNeighborSet x), OMA.ComponentExtremal.degree_cut G s (fun {_ _} h hxy => (cut hxy).1 h)]
    exact hd
  · intro x
    have hd := degree (di x).val
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ⊢
    rw [Nat.card_congr (di.mapNeighborSet x), OMA.ComponentExtremal.degree_cut G sᶜ (fun {_ _} h hxy => mt (cut hxy).2 h)]
    exact hd
  · intro n
    rw [extremalNumber_congr_right ei,extremalNumber_congr_right di]
    apply OMA.ComponentExtremal.cut_bound G s (fun {_ _} h => cut h)
    intro x
    exact (G.degree_pos_iff_exists_adj x).mp (lt_of_lt_of_le (by decide : 0<2) (degree x))
