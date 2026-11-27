import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-! Enumerate each support in increasing order and transport its real sum back to the rationals. -/

open scoped Cardinal
open Cardinal

set_option maxHeartbeats 1200000 in
/-- Increasing enumeration identifies each binary-indexed support uniquely.
The rational sum follows from the embedding into the reals. -/
theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H3 := by
  classical
  rintro ⟨A, hinj, hA⟩
  let e (b : ℕ → Bool) := @Nat.Subtype.orderIsoOfNat (A b) (hA b).1.to_subtype
  let a (b : ℕ → Bool) (k : ℕ) : ℕ := (e b k).val
  have hrange (b) : Set.range (a b) = A b := by
    ext n
    constructor
    · rintro ⟨k, rfl⟩
      exact (e b k).property
    · intro hn
      obtain ⟨k, hk⟩ := (e b).surjective ⟨n, hn⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hrep (b) : Erdos261.Erdos261InfiniteRepresentation 1 (a b) := by
    let term (n : ℕ) : ℝ := n / 2 ^ n
    have hsub : HasSum (fun z : A b => term z.val) 1 := hasSum_subtype_iff_indicator.mpr (hA b).2.2
    have hreal : HasSum (fun k => (a b k : ℝ) / 2 ^ a b k) 1 := ((e b).toEquiv.hasSum_iff (f := fun z : A b => term z.val) (a := (1 : ℝ))).mpr hsub
    let g : ℚ →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom
    have hg : Topology.IsInducing g := Rat.isEmbedding_coe_real.isInducing
    have hrat : HasSum (fun k => (a b k : ℚ) / 2 ^ a b k) 1 := by
      apply (hg.hasSum_iff _ _).mp
      simpa [g, Function.comp_def] using hreal
    exact ⟨fun _ _ h => (e b).strictMono h, fun k => (hA b).2.1 _ (e b k).property,
      hrat.summable, hrat.tsum_eq.symm⟩
  let F (b : ℕ → Bool) : {s : ℕ → ℕ | Erdos261.Erdos261InfiniteRepresentation 1 s} := ⟨a b, hrep b⟩
  have hf : Function.Injective F := by
    intro b c h
    apply hinj
    rw [← hrange b, ← hrange c]
    exact congrArg Set.range (congrArg Subtype.val h)
  have size : #(ℕ → Bool) = 𝔠 := by
    rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
    simp only [Cardinal.lift_id, Cardinal.continuum]
  rw [← size]
  exact Cardinal.mk_le_of_injective hf
