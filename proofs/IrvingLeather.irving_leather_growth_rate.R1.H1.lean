import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1

/-! A block sum of preference profiles carries every pair of stable matchings
to a distinct stable matching. Everyone ranks the left block first, so any
cross-block pair has a member who prefers their assigned partner. -/

open StableMarriage IrvingLeather Finset

namespace OMA.MarriageProduct

private def block {m n : ℕ} (l : Matching m) (r : Matching n) : Matching (m+n) :=
  finSumFinEquiv.permCongr (l.sumCongr r)

@[simp] private lemma blockL {m n : ℕ} (l : Matching m) (r : Matching n) (x : Fin m) :
    block l r (Fin.castAdd n x) = Fin.castAdd n (l x) := by simp [block]
@[simp] private lemma blockR {m n : ℕ} (l : Matching m) (r : Matching n) (x : Fin n) :
    block l r (Fin.natAdd m x) = Fin.natAdd m (r x) := by simp [block]
@[simp] private lemma invL {m n : ℕ} (l : Matching m) (r : Matching n) (x : Fin m) :
    (block l r).symm (Fin.castAdd n x) = Fin.castAdd n (l.symm x) := by
  apply (block l r).injective
  simp
@[simp] private lemma invR {m n : ℕ} (l : Matching m) (r : Matching n) (x : Fin n) :
    (block l r).symm (Fin.natAdd m x) = Fin.natAdd m (r.symm x) := by
  apply (block l r).injective
  simp

private def ranks {m n : ℕ} (l : Fin m → Matching m) (r : Fin n → Matching n)
    (i : Fin (m+n)) : Matching (m+n) :=
  (finSumFinEquiv.symm i).elim (fun j => block (l j) (Equiv.refl _)) (fun j => block (Equiv.refl _) (r j))

private def combined {m n : ℕ} (p : Profile m) (q : Profile n) : Profile (m+n) :=
  ⟨ranks p.manRank q.manRank, ranks p.womanRank q.womanRank⟩

private lemma left_lt {m n : ℕ} (i j : Fin m) : Fin.castAdd n i < Fin.castAdd n j ↔ i < j := Iff.rfl

private lemma stable {m n : ℕ} {p : Profile m} {q : Profile n} {l : Matching m} {r : Matching n}
    (hl : IsStable p l) (hr : IsStable q r) : IsStable (combined p q) (block l r) := by
  intro a b
  induction a using Fin.addCases with
  | left a =>
    induction b using Fin.addCases with
    | left b =>
      rintro ⟨hne,hm,hw⟩
      apply hl a b
      refine ⟨fun eq => hne (by simp [eq]), ?_, ?_⟩
      · simpa only [combined,ranks,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inl,Sum.elim_inr,blockL,blockR,left_lt,Fin.natAdd_lt_natAdd_iff] using hm
      · simpa only [combined,ranks,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inl,Sum.elim_inr,invL,invR,blockL,blockR,left_lt,Fin.natAdd_lt_natAdd_iff] using hw
    | right b =>
      intro h
      have hm := h.2.1
      simp [combined,ranks,Fin.lt_def] at hm
      omega
  | right a =>
    induction b using Fin.addCases with
    | left b =>
      intro h
      have hw := h.2.2
      simp [combined,ranks,Fin.lt_def] at hw
      omega
    | right b =>
      rintro ⟨hne,hm,hw⟩
      apply hr a b
      refine ⟨fun eq => hne (by simp [eq]), ?_, ?_⟩
      · simpa only [combined,ranks,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inl,Sum.elim_inr,blockL,blockR,left_lt,Fin.natAdd_lt_natAdd_iff] using hm
      · simpa only [combined,ranks,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inl,Sum.elim_inr,invL,invR,blockL,blockR,left_lt,Fin.natAdd_lt_natAdd_iff] using hw

private lemma product_le {m n : ℕ} (p : Profile m) (q : Profile n) :
    numStableMatchings p * numStableMatchings q ≤ numStableMatchings (combined p q) := by
  classical
  let F (v : {l : Matching m // IsStable p l} × {r : Matching n // IsStable q r}) :
      {s : Matching (m+n) // IsStable (combined p q) s} :=
    ⟨block v.1.val v.2.val, stable v.1.property v.2.property⟩
  have inj : Function.Injective F := by
    intro a b h
    have e := congrArg Subtype.val h
    change block a.1.val a.2.val = block b.1.val b.2.val at e
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      have := congrArg (fun t : Matching (m+n) => t (Fin.castAdd n x)) e
      simpa using this
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      have := congrArg (fun t : Matching (m+n) => t (Fin.natAdd m x)) e
      simpa using this
  simpa [numStableMatchings,Fintype.card_prod] using Fintype.card_le_of_injective F inj

theorem result : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 := by
  classical
  intro m n
  obtain ⟨p,_,hp⟩ := exists_mem_eq_sup (univ : Finset (Profile m)) univ_nonempty numStableMatchings
  obtain ⟨q,_,hq⟩ := exists_mem_eq_sup (univ : Finset (Profile n)) univ_nonempty numStableMatchings
  unfold maxStableMatchings
  rw [hp,hq]
  exact (product_le p q).trans (Finset.le_sup (f:=numStableMatchings) (mem_univ (combined p q)))

end OMA.MarriageProduct

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 := OMA.MarriageProduct.result
