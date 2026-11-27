import FormalConjectures.ErdosProblems.«876»
import Mathlib.Analysis.PSeries

/-! Erdős's reciprocal-sum bound. Compare disjoint partial-sum translates
of the tail to bound the number of dyadic blocks of each given density.
Summing the resulting geometric series gives a uniform bound. -/

namespace OMA.Recip
open Finset Filter Erdos876
noncomputable section

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


lemma packing {A : Set ℕ} (hs : IsSubsetSumFree A) (f : ℕ → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, f i ∈ A) {k m : ℕ} (hk : 4*k ≤ m) (hb : 4*f k ≤ m) :
    k*m ≤ 2*(f m + 1) := by
  classical
  let s (i : ℕ) := ∑ t ∈ range i, f t
  have bound {i : ℕ} (hi : i < k) : s i ≤ k*f k := by
    calc
      s i ≤ ∑ _t ∈ range i, f k := sum_le_sum fun j hj => hf.monotone ((mem_range.mp hj).trans hi).le
      _ = i*f k := by simp
      _ ≤ k*f k := Nat.mul_le_mul_right _ hi.le
  have hc : ((range k) ×ˢ (Ioc k m)).card ≤ (range (f m+k*f k+1)).card := by
    apply card_le_card_of_injOn (fun w : ℕ × ℕ => s w.1 + f w.2)
    · rintro ⟨i,u⟩ hw
      obtain ⟨hi,hu⟩ := mem_product.mp hw
      have h1 : s i ≤ k*f k := bound (mem_range.mp hi)
      have h2 : f u ≤ f m := hf.monotone (mem_Ioc.mp hu).2
      exact mem_range.mpr (by dsimp; omega)
    · rintro ⟨i,u⟩ hw ⟨j,v⟩ hz eq
      obtain ⟨hi,hu⟩ := mem_product.mp hw
      obtain ⟨hj,hv⟩ := mem_product.mp hz
      change s i + f u = s j + f v at eq
      rcases lt_trichotomy i j with h | rfl | h
      · exact False.elim (separated hs f hf hmem h (mem_range.mp hj).le (hmem u) (hmem v) (hf (mem_Ioc.mp hv).1) eq)
      · exact Prod.ext rfl (hf.injective (show f u = f v by omega))
      · exact False.elim (separated hs f hf hmem h (mem_range.mp hi).le (hmem v) (hmem u) (hf (mem_Ioc.mp hu).1) eq.symm)
  simp only [card_product,card_range,Nat.card_Ioc] at hc
  have diff : m-k+k=m := Nat.sub_add_cancel (by omega)
  nlinarith [congrArg (k*·) diff, Nat.mul_le_mul_left k hk, Nat.mul_le_mul_left k hb]

def small (f : ℕ → ℕ) (h j : ℕ) : Prop := f (2^j) < 2^j*2^(h+1)

lemma near {A : Set ℕ} (hs : IsSubsetSumFree A) (f : ℕ → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, f i ∈ A) {h a b : ℕ} (ha : h+4 ≤ a)
    (sa : small f h a) (sb : small f h b) : b < a+h+4 := by
  by_contra! big
  let k := 2^(h+4)
  let m := 2^b
  have ka : k ≤ 2^a := Nat.pow_le_pow_right (by decide) ha
  have low : 2^a*2^h*16 ≤ m := by
    calc
      _ = 2^(a+h+4) := by rw [pow_add,pow_add]; norm_num
      _ ≤ m := Nat.pow_le_pow_right (by decide) big
  change f (2^a) < 2^a*2^(h+1) at sa
  change f m < m*2^(h+1) at sb
  have pt : 0 < 2^h := Nat.two_pow_pos h
  have pa : 0 < 2^a := Nat.two_pow_pos a
  have K : k = 16*2^h := by dsimp [k]; rw [pow_add]; ring
  have pk : 4*k ≤ m := by nlinarith [Nat.mul_le_mul_left (2^a*16) (show 1 ≤ 2^h from pt)]
  have pf : 4*f k ≤ m := by
    have lf := (hf.monotone ka).trans_lt sa
    rw [pow_succ] at lf
    nlinarith
  have pack := packing hs f hf hmem pk pf
  rw [K] at pack
  rw [pow_succ] at sb
  have pm : 0 < m := Nat.two_pow_pos b
  nlinarith [Nat.mul_pos pm pt]

lemma count_small {A : Set ℕ} (hs : IsSubsetSumFree A) (f : ℕ → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, f i ∈ A) (h : ℕ) (J : Finset ℕ) (hj : ∀ j ∈ J, small f h j) :
    J.card ≤ 2*h+8 := by
  classical
  let U := J.filter (fun j => h+4 ≤ j)
  by_cases ne : U.Nonempty
  · let a := U.min' ne
    have mem : a ∈ U := min'_mem _ _
    have ha := mem_filter.mp mem
    have cover : J ⊆ range (h+4) ∪ Ico a (a+h+4) := by
      intro b hb
      by_cases e : b < h+4
      · exact mem_union_left _ (mem_range.mpr e)
      · have bu : b ∈ U := mem_filter.mpr ⟨hb,by omega⟩
        exact mem_union_right _ (mem_Ico.mpr ⟨min'_le _ _ bu,near hs f hf hmem ha.2 (hj a ha.1) (hj b hb)⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    simp only [card_range,Nat.card_Ico] at c
    omega
  · have cover : J ⊆ range (h+4) := by
      intro b hb
      apply mem_range.mpr
      by_contra! h'
      exact ne ⟨b,mem_filter.mpr ⟨hb,h'⟩⟩
    have c := card_le_card cover
    simp at c
    omega


def level (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  open scoped Classical in Nat.find (show ∃ h, small f h j from by
    refine ⟨f (2^j),?_⟩
    dsimp [small]
    have h : f (2^j) < 2^(f (2^j)+1) := by
      have := (Nat.lt_two_pow_self : f (2^j) < 2^(f (2^j)))
      rw [pow_succ]; omega
    exact h.trans_le (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))

lemma at_level (f : ℕ → ℕ) (j : ℕ) : small f (level f j) j := by
  classical
  unfold level
  exact Nat.find_spec (p:=fun h => small f h j) _

lemma level_lower (f : ℕ → ℕ) (hf : StrictMono f) (j : ℕ) :
    2^j*2^(level f j) ≤ f (2^j) := by
  classical
  cases h : level f j with
  | zero => simpa using hf.id_le (2^j)
  | succ i =>
    have no : ¬ small f i j := by
      have hw : i < level f j := by omega
      unfold level at hw
      exact Nat.find_min (p:=fun h => small f h j) _ hw
    exact Nat.le_of_not_gt no

lemma geometric (n : ℕ) :
    ∑ h ∈ range n, ((2*(h:ℝ)+8)/(2:ℝ)^h) + (4*(n:ℝ)+20)/2^n = 20 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ,pow_succ]
    push_cast
    calc
      _ = ∑ h ∈ range n, ((2*(h:ℝ)+8)/2^h) + (4*(n:ℝ)+20)/2^n := by ring
      _ = _ := ih

lemma condensed {A : Set ℕ} (hs : IsSubsetSumFree A) (f : ℕ → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, f i ∈ A) (J : Finset ℕ) :
    ∑ j ∈ J, ((2:ℝ)^j/(f (2^j):ℝ)) ≤ 20 := by
  classical
  let l := level f
  let M := J.sup l + 1
  have lands (i) (hi : i ∈ J) : l i ∈ range M := mem_range.mpr (Nat.lt_succ_of_le (le_sup hi))
  rw [← sum_fiberwise_of_maps_to lands]
  calc
    _ ≤ ∑ h ∈ range M, ((2*(h:ℝ)+8)/2^h) := by
      apply sum_le_sum
      intro h hh
      let U := J.filter (fun i => l i = h)
      have bound (i) (hi : i ∈ U) : (2:ℝ)^i/(f (2^i):ℝ) ≤ 1/2^h := by
        have eq : level f i = h := (mem_filter.mp hi).2
        have pos : (0:ℝ) < f (2^i) := by exact_mod_cast (hs _ (hmem _)).1
        apply (div_le_div_iff₀ pos (by positivity : (0:ℝ) < 2^h)).mpr
        simpa only [one_mul] using (show (2:ℝ)^i*2^h ≤ f (2^i) by exact_mod_cast eq ▸ level_lower f hf i)
      have card := count_small hs f hf hmem h U (fun i hi => (show level f i = h from (mem_filter.mp hi).2) ▸ at_level f i)
      calc
        _ ≤ ∑ _i ∈ U, (1:ℝ)/2^h := sum_le_sum bound
        _ = (U.card:ℝ)/2^h := by simp [nsmul_eq_mul,div_eq_mul_inv]
        _ ≤ _ := by gcongr; exact_mod_cast card
    _ ≤ 20 := by linarith [geometric M,show (0:ℝ) ≤ (4*(M:ℝ)+20)/2^M by positivity]

lemma reciprocals {A : Set ℕ} (hA : A.Infinite) (hs : IsSubsetSumFree A) :
    ∃ s : ℝ, s < 103 ∧ HasSum (fun a : A => (1:ℝ)/(a:ℕ)) s := by
  classical
  let : Infinite A := hA.to_subtype
  let e := Nat.Subtype.orderIsoOfNat A
  let f (i : ℕ) : ℕ := e i
  have hf : StrictMono f := fun _ _ hi => e.strictMono hi
  have hmem (i : ℕ) : f i ∈ A := (e i).property
  let g (n : ℕ) := 1/(f n:ℝ)
  have non (n) : 0 ≤ g n := by dsimp [g]; positivity
  have anti : Antitone g := by
    intro i j hij
    exact one_div_le_one_div_of_le (by exact_mod_cast (hs _ (hmem i)).1) (by exact_mod_cast hf.monotone hij)
  have ub (n : ℕ) : ∑ i ∈ range n, g i ≤ 21 := by
    have h₀ : g 0 ≤ 1 := by
      apply div_le_one_of_le₀ _ (by positivity); exact_mod_cast (hs _ (hmem 0)).1
    have h₁ := Finset.le_sum_condensed (f:=g) (fun _ _ _ hij => anti hij) n
    have h₂ := condensed hs f hf hmem (range n)
    have eq : ∑ k ∈ range n, 2^k • g (2^k) = ∑ k ∈ range n, (2:ℝ)^k/(f (2^k):ℝ) := by
      simp [g,nsmul_eq_mul,div_eq_mul_inv]
    rw [eq] at h₁
    have sub : range n ⊆ range (2^n) := range_mono (Nat.lt_two_pow_self.le)
    linarith [sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => non i)]
  have hsum := (summable_of_sum_range_le non ub).hasSum
  refine ⟨∑' n, g n, (Real.tsum_le_of_sum_range_le non ub).trans_lt (by norm_num),?_⟩
  exact (e.toEquiv.hasSum_iff).mp hsum

end
end OMA.Recip

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.recip_sum_lt :=
  fun _ hA hs => OMA.Recip.reciprocals hA hs
