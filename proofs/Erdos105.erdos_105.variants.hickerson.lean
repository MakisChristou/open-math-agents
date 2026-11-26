import FormalConjectures.ErdosProblems.«105»

/-! We use eleven of Xichuan's twelve points from the Erdős 105 configuration
(https://www.erdosproblems.com/forum/thread/105). The nine blocking points
still meet every joining line after one point is deleted. The incidences
below are checked by integer determinants. -/

namespace OMA.BlockingPoints

open EuclideanGeometry

abbrev Grid := ℤ × ℤ

def red : Finset Grid :=
  {(0,6930), (0,7920), (13860,0), (5544,5544), (3465,6930), (2520,7560),
   (18480,0), (9240,4620), (6160,6160), (4620,6930), (11880,3960)}

def blue : Finset Grid :=
  {(0,9240), (-13860,13860), (27720,0), (6930,6930), (3960,7920),
   (-55440,27720), (11088,5544), (5940,5940), (-5544,11088)}

def point (p : Grid) : ℝ² := WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

lemma faithful : Function.Injective point := by
  intro p q h
  apply Prod.ext
  · have hx : (p.1 : ℝ) = q.1 := congrArg (fun v : ℝ² => v 0) h
    exact_mod_cast hx
  · have hy : (p.2 : ℝ) = q.2 := congrArg (fun v : ℝ² => v 1) h
    exact_mod_cast hy

def area (p q b : Grid) : ℤ :=
  (q.1 - p.1) * (b.2 - p.2) - (q.2 - p.2) * (b.1 - p.1)

lemma on_line {p q b : Grid} (hne : p ≠ q) (h : area p q b = 0) :
    point b ∈ line[ℝ, point p, point q] := by
  have cross : ((q.1 : ℝ) - p.1) * (b.2 - p.2) =
      ((q.2 : ℝ) - p.2) * (b.1 - p.1) := by
    exact_mod_cast (sub_eq_zero.mp h)
  have param (t : ℝ) (hx : t * (q.1 - p.1) = b.1 - p.1)
      (hy : t * (q.2 - p.2) = b.2 - p.2) : point b ∈ line[ℝ, point p, point q] := by
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    · change t * ((q.1 : ℝ) - p.1) + p.1 = b.1
      linarith
    · change t * ((q.2 : ℝ) - p.2) + p.2 = b.2
      linarith
  by_cases hx : (q.1 : ℝ) - p.1 = 0
  · have hy : (q.2 : ℝ) - p.2 ≠ 0 := by
      intro hy
      apply hne
      apply Prod.ext
      · exact_mod_cast (sub_eq_zero.mp hx).symm
      · exact_mod_cast (sub_eq_zero.mp hy).symm
    apply param ((b.2 - p.2) / (q.2 - p.2))
    · rw [hx, zero_mul] at cross
      have := (mul_eq_zero.mp cross.symm).resolve_left hy
      simp [hx, this]
    · exact div_mul_cancel₀ _ hy
  · apply param ((b.1 - p.1) / (q.1 - p.1))
    · exact div_mul_cancel₀ _ hx
    · field_simp
      linear_combination -cross

lemma incidences : ∀ p ∈ red, ∀ q ∈ red, p ≠ q → ∃ b ∈ blue, area p q b = 0 := by
  decide +kernel

end OMA.BlockingPoints

open OMA.BlockingPoints EuclideanGeometry in
theorem OMA.solution : type_of% @Erdos105.erdos_105.variants.hickerson := by
  classical
  intro hall
  have dis : Disjoint (red.image point) (blue.image point) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨p, hred, hp⟩ := Finset.mem_image.mp hv
    obtain ⟨q, hblue, hq⟩ := Finset.mem_image.mp hw
    have he := faithful (hq.trans hp.symm)
    exact Finset.disjoint_left.mp (show Disjoint red blue by decide +kernel) hred (he ▸ hblue)
  have card : (red.image point).card = (blue.image point).card + 2 := by
    rw [Finset.card_image_of_injective _ faithful, Finset.card_image_of_injective _ faithful]
    decide +kernel
  have nc : ¬ Collinear ℝ (red.image point : Set ℝ²) := by
    intro hc
    have mem (p : Grid) (hp : p ∈ red) : point p ∈ (red.image point : Set ℝ²) :=
      Finset.mem_image_of_mem _ hp
    have he := hc.mem_affineSpan_of_mem_of_ne (mem (0,6930) (by decide))
      (mem (0,7920) (by decide)) (mem (13860,0) (by decide))
      (fun h => (by decide : ((0,6930) : Grid) ≠ (0,7920)) (faithful h))
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp he
    have hx := congrArg (fun v : ℝ² => v 0) ht
    change t * (((0 : ℤ) : ℝ) - ((0 : ℤ) : ℝ)) + ((0 : ℤ) : ℝ) = ((13860 : ℤ) : ℝ) at hx
    norm_num at hx
  obtain ⟨x, hxr, y, hyr, hne, miss⟩ := hall _ _ dis card nc
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hyr
  have hne' : p ≠ q := fun h => hne (congrArg point h)
  obtain ⟨b, hb, hit⟩ := incidences p hp q hq hne'
  exact miss (point b) (Finset.mem_image_of_mem _ hb) (on_line hne' hit)
