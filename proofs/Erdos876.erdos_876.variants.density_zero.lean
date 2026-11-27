import FormalConjectures.ErdosProblems.«876»

/-! Erdős's density-zero theorem (1962). Translate the tail of the set by
successive partial sums of its first k elements. If two translates meet,
one element of the tail is the sum of a smaller tail element and a nonempty
block of distinct earlier elements. Thus all k translates are disjoint. -/

namespace OMA.SubsetSumDensity
open Finset Filter Erdos876
open scoped Topology
noncomputable section

open scoped Classical in
def part (A : Set ℕ) (N : ℕ) : Finset ℕ := (range N).filter (· ∈ A)

lemma mem_part {A : Set ℕ} {N n : ℕ} : n ∈ part A N ↔ n < N ∧ n ∈ A := by
  classical
  simp [part]

def count (A : Set ℕ) (N : ℕ) : ℕ := (part A N).card

def Bound (A : Set ℕ) (d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, (count A N : ℝ) ≤ d*N + C


lemma separated {A : Set ℕ} (hs : IsSubsetSumFree A)
    (f : ℕ → ℕ) (hf : StrictMono f) (hmem : ∀ i, f i ∈ A)
    {i j x y k : ℕ} (hi : i < j) (hj : j ≤ k) (hx : x ∈ A) (hy : y ∈ A)
    (hy' : f k < y)
    (eq : (∑ t ∈ range i, f t) + x = (∑ t ∈ range j, f t) + y) : False := by
  classical
  let U := (Ico i j).image f
  have sp : ∑ v ∈ U, v = ∑ t ∈ Ico i j, f t := by
    unfold U
    rw [sum_image (fun a _ b _ e => hf.injective e)]
  have seg := sum_range_add_sum_Ico f hi.le
  have eq' : x = y + ∑ v ∈ U, v := by omega
  have low {v : ℕ} (hv : v ∈ U) : v ∈ A ∧ v < y := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hv
    exact ⟨hmem t,(hf.monotone ((mem_Ico.mp ht).2.le.trans hj)).trans_lt hy'⟩
  have yn : y ∉ U := fun H => (low H).2.false
  have pos : 0 < ∑ v ∈ U, v := by
    apply Finset.sum_pos'
    · intro v _; omega
    · exact ⟨f i, mem_image.mpr ⟨i,mem_Ico.mpr ⟨le_rfl,hi⟩,rfl⟩, (hs _ (hmem i)).1⟩
  have yx : y < x := by omega
  apply (hs x hx).2
  refine ⟨insert y U, ?_, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨hy,yx⟩
    · exact ⟨(low hz).1,(low hz).2.trans yx⟩
  · simpa [sum_insert yn] using eq'

lemma sparse {A : Set ℕ} (hA : A.Infinite) (hs : IsSubsetSumFree A)
    {e : ℝ} (he : 0 < e) : Bound A e := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (1/e)
  have hk' : 0 < (k:ℝ) := (by positivity : 0 < 1/e).trans hk
  let f := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  have hmem : ∀ i, f i ∈ A := Nat.nth_mem_of_infinite hA
  let B := f k + 1
  let s (i : ℕ) := ∑ t ∈ range i, f t
  have hsm : Monotone s := monotone_nat_of_le_succ fun i => by simp [s,sum_range_succ]
  refine ⟨(B:ℝ) + (s k : ℝ)/k,fun N => ?_⟩
  let V := (part A N).filter (fun x => B ≤ x)
  have hV {x : ℕ} (hx : x ∈ V) : x < N ∧ x ∈ A ∧ f k < x := by
    obtain ⟨hp,hb⟩ := mem_filter.mp hx
    exact ⟨(mem_part.mp hp).1,(mem_part.mp hp).2,hb⟩
  have card : k*V.card ≤ N+s k := by
    have m : ((range k) ×ˢ V).card ≤ (range (N+s k)).card := by
      apply card_le_card_of_injOn (fun w : ℕ × ℕ => s w.1+w.2)
      · rintro ⟨i,x⟩ hw
        obtain ⟨hi,hx⟩ := mem_product.mp hw
        have h₁ : s i ≤ s k := hsm (mem_range.mp hi).le
        have h₂ := (hV hx).1
        exact mem_range.mpr (by dsimp; omega)
      · rintro ⟨i,x⟩ hw ⟨j,y⟩ hz eq
        obtain ⟨hi,hx⟩ := mem_product.mp hw
        obtain ⟨hj,hy⟩ := mem_product.mp hz
        change s i + x = s j + y at eq
        rcases lt_trichotomy i j with lt | rfl | gt
        · exact False.elim (separated hs f hf hmem lt (mem_range.mp hj).le (hV hx).2.1 (hV hy).2.1 (hV hy).2.2 eq)
        · exact Prod.ext rfl (by dsimp; omega)
        · exact False.elim (separated hs f hf hmem gt (mem_range.mp hi).le (hV hy).2.1 (hV hx).2.1 (hV hx).2.2 eq.symm)
    simpa using m
  have cover : part A N ⊆ range B ∪ V := by
    intro x hx
    by_cases h : x < B
    · exact mem_union_left _ (mem_range.mpr h)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,le_of_not_gt h⟩)
  have tot : count A N ≤ B + V.card := by simpa [count] using (card_le_card cover).trans (card_union_le _ _)
  have tot' : (count A N : ℝ) ≤ B + (V.card : ℝ) := by exact_mod_cast tot
  have card' : (k:ℝ)*V.card ≤ N+(s k:ℝ) := by exact_mod_cast card
  have bound := (le_div_iff₀ hk').mpr (by simpa [mul_comm] using card' : (V.card : ℝ)*k ≤ N+s k)
  have ratio : 1/(k:ℝ) ≤ e := (div_le_iff₀ hk').mpr (by linarith [(div_lt_iff₀ he).mp hk])
  have slope := mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg N)
  linarith only [tot',bound,slope, show ((N:ℝ)+(s k:ℝ))/k = (1/(k:ℝ))*N + (s k:ℝ)/k by ring]

lemma density (A : Set ℕ) (h : ∀ e > (0:ℝ), Bound A e) : A.HasDensity 0 := by
  classical
  have pd (n : ℕ) : A.partialDensity Set.univ n = (count A n : ℝ)/n := by
    have eq : A ∩ Set.Iio n = (part A n : Set ℕ) := by
      ext k
      simp [mem_part, and_comm]
    simp [Set.partialDensity,eq,count]
  rw [Set.HasDensity,Metric.tendsto_nhds]
  intro e he
  obtain ⟨C,hC⟩ := h (e/2) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (max 0 (2*C/e))
  filter_upwards [eventually_ge_atTop K] with n hn
  have hN : (K:ℝ) ≤ n := by exact_mod_cast hn
  have pn : 0 < (n:ℝ) := lt_of_lt_of_le ((le_max_left _ _).trans_lt hK) hN
  have cut := (div_lt_iff₀ he).mp (lt_of_lt_of_le ((le_max_right _ _).trans_lt hK) hN)
  rw [pd,Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ pn]
  linarith [hC n]

end
end OMA.SubsetSumDensity

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.density_zero :=
  fun A hA hs => OMA.SubsetSumDensity.density A (fun _ he => OMA.SubsetSumDensity.sparse hA hs he)
