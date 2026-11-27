import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1

/-! Choose a single permitted positive exponent at each prime. A dyadic
averaging argument preserves total weight and costs at most 2^k elements
per survivor. Numbers in the surviving family are encoded by prime copies. -/
namespace OMA.SunflowerFactors
open Finset
open scoped ArithmeticFunction.Omega

lemma total_exp (n : ℕ) : ∑ p ∈ n.primeFactors, n.factorization p = Ω n := by
  simp [ArithmeticFunction.cardFactors_eq_sum_factorization,Finsupp.sum]

lemma exp_bound {k n : ℕ} (h : Ω n=k) (p : ℕ) : n.factorization p ≤ k := by
  by_cases hp : p∈n.primeFactors
  · rw [← h,← total_exp]
    exact single_le_sum (fun _ _ => Nat.zero_le _) hp
  · have hz : n.factorization p = 0 := by
      simpa only [← Nat.support_factorization,Finsupp.mem_support_iff,not_ne_iff] using hp
    omega

/-- At least one positive-exponent class compensates for discarding the others. -/
lemma dyadic (n : ℕ) (f : ℕ → ℕ) :
    ∃ i, (∑ j ∈ range n, f j) ≤ 2^(i+1)*f i := by
  induction n generalizing f with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    rw [sum_range_succ']
    by_cases h : (∑ j ∈ range n, f (j+1)) ≤ f 0
    · exact ⟨0,by simpa using (show (∑ j ∈ range n, f (j+1))+f 0 ≤ 2*f 0 by omega)⟩
    · obtain ⟨i,hi⟩ := ih (fun j => f (j+1))
      refine ⟨i+1,?_⟩
      rw [pow_succ 2 (i+1)]
      nlinarith [hi]

def weight (D : Finset ℕ) (n : ℕ) := 2^(∑ q ∈ D, n.factorization q)

lemma weight_insert {D : Finset ℕ} {p : ℕ} (hp : p∉D) (n : ℕ) :
    weight (insert p D) n = 2^(n.factorization p)*weight D n := by
  rw [weight,sum_insert hp,pow_add,weight]

def consistent (D B : Finset ℕ) := ∀ p ∈ D, ∀ a ∈ B, ∀ b ∈ B,
  0 < a.factorization p → 0 < b.factorization p → a.factorization p = b.factorization p

lemma prune (A D : Finset ℕ) (k : ℕ) (hk : ∀ n ∈ A, Ω n=k) :
    ∃ B ⊆ A, A.card ≤ ∑ n ∈ B, weight D n ∧ consistent D B := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨A,Subset.rfl,by simp [weight],by simp [consistent]⟩
  | @insert p D hp ih =>
    obtain ⟨B,hBA,hW,hC⟩ := ih
    let F := fun e => B.filter (fun n => n.factorization p=e)
    let mass := fun e => ∑ n ∈ F e, weight D n
    obtain ⟨i,hHeavy⟩ := dyadic k (fun j => mass (j+1))
    let B' := F 0 ∪ F (i+1)
    have hf (e : ℕ) : F e ⊆ B := filter_subset _ _
    have hsub : B' ⊆ B := union_subset (hf 0) (hf (i+1))
    have hdis : Disjoint (F 0) (F (i+1)) := by
      rw [disjoint_left]; intro n h0 h1
      have := (mem_filter.mp h0).2; have := (mem_filter.mp h1).2; omega
    have hpart : ∑ e ∈ range (k+1), mass e = ∑ n ∈ B, weight D n := by
      apply sum_fiberwise_of_maps_to
      intro n h
      exact mem_range.mpr (by have := exp_bound (hk n (hBA h)) p; omega)
    have hfib (e : ℕ) : ∑ n ∈ F e, weight (insert p D) n = 2^e * mass e := by
      unfold mass; rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [weight_insert hp, (mem_filter.mp hn).2]
    refine ⟨B',hsub.trans hBA,?_,?_⟩
    · rw [show B'=F 0 ∪ F (i+1) by rfl,sum_union hdis,hfib,hfib,pow_zero,one_mul]
      rw [← hpart,sum_range_succ'] at hW
      omega
    · intro q hq a ha b hb ha' hb'
      rcases mem_insert.mp hq with hqp|hd
      · subst q
        have hint {x : ℕ} (hx : x ∈ B') (hpos : 0 < x.factorization p) : x.factorization p=i+1 := by
          rcases mem_union.mp hx with hz|hi
          · have := (mem_filter.mp hz).2; omega
          · exact (mem_filter.mp hi).2
        exact (hint ha ha').trans (hint hb hb').symm
      · exact hC q hd a (hsub ha) b (hsub hb) ha' hb'


def codePoint (z : (p : ℕ) × ℕ) := Nat.pair z.1 z.2
lemma point_inj : Function.Injective codePoint := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨rfl,rfl⟩ := Nat.pair_eq_pair.mp h
  rfl

def code (n : ℕ) : Finset ℕ :=
  (n.primeFactors.sigma (fun p => range (n.factorization p))).image codePoint

lemma code_card (n : ℕ) : (code n).card = Ω n := by
  rw [code,card_image_of_injective _ point_inj,card_sigma]
  simpa using total_exp n

lemma point_mem (n p j : ℕ) :
    Nat.pair p j ∈ code n ↔ j < n.factorization p := by
  rw [code,mem_image]
  constructor
  · rintro ⟨⟨q,i⟩,hx,he⟩
    obtain ⟨rfl,rfl⟩ := Nat.pair_eq_pair.mp he
    exact mem_range.mp (mem_sigma.mp hx).2
  · intro h
    have hm : p∈n.primeFactors := by
      rw [← Nat.support_factorization,Finsupp.mem_support_iff]; omega
    exact ⟨⟨p,j⟩,mem_sigma.mpr ⟨hm,mem_range.mpr h⟩,rfl⟩

lemma code_inj {a b : ℕ} (ha : a≠0) (hb : b≠0) (h : code a=code b) : a=b := by
  apply Nat.factorization_inj ha hb
  ext p
  have hh (i : ℕ) : i<a.factorization p ↔ i<b.factorization p := by
    rw [← point_mem,← point_mem,h]
  exact le_antisymm (le_of_not_gt (by simpa using (hh (b.factorization p)).not.mpr (lt_irrefl _)))
    (le_of_not_gt (by simpa using (hh (a.factorization p)).not.mp (lt_irrefl _)))

lemma code_gcd {a b : ℕ} (ha : a≠0) (hb : b≠0) : code (a.gcd b) = code a ∩ code b := by
  ext z
  obtain ⟨⟨p,i⟩,rfl⟩ := Nat.pairEquiv.surjective z
  change Nat.pair p i ∈ _ ↔ Nat.pair p i ∈ _
  rw [mem_inter,point_mem,point_mem,point_mem,Nat.factorization_gcd ha hb]
  simp

lemma positive_exp {n p : ℕ} (hp : p.Prime) (hn : n≠0) (hd : p∣n) :
    0<n.factorization p := by
  have hs : p∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩
  rw [← Nat.support_factorization,Finsupp.mem_support_iff] at hs
  omega

lemma coprime_quot {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : ∀ p, 0<a.factorization p → 0<b.factorization p → a.factorization p=b.factorization p) :
    Nat.Coprime (a/a.gcd b) (a.gcd b) := by
  let d := a.gcd b
  have hd : 0<d := Nat.gcd_pos_of_pos_left b ha
  have hdvd : d∣a := Nat.gcd_dvd_left a b
  have he : 0<a/d := Nat.div_pos (Nat.le_of_dvd ha hdvd) hd
  by_contra hn
  obtain ⟨p,hp,hq,hdp⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have h₁ := positive_exp hp he.ne' hq
  have h₂ := positive_exp hp hd.ne' hdp
  rw [Nat.factorization_div hdvd,Finsupp.tsub_apply] at h₁
  have heq : d.factorization p = min (a.factorization p) (b.factorization p) := by
    dsimp only [d]; rw [Nat.factorization_gcd ha.ne' hb.ne']; rfl
  rw [heq] at h₁ h₂
  have := hc p (by omega) (by omega)
  omega

lemma common_gcd {D B S : Finset ℕ} (hw : consistent D B) (hS : S⊆B)
    (hpos : ∀ a ∈ B, 0<a) (hpr : ∀ a ∈ B, a.primeFactors⊆D)
    (h : ∃ K : Finset ℕ, (S : Set ℕ).Pairwise (fun a b => code a ∩ code b = K)) :
    ∃ d, 0<d ∧ (S : Set ℕ).Pairwise (fun a b => a.gcd b=d) ∧
      ∀ a∈S, ∃ b, a=d*b ∧ b.gcd d=1 := by
  by_cases hn : S.Nontrivial
  · have other := hn.exists_ne
    obtain ⟨a,ha,b,hb,hab⟩ := hn
    obtain ⟨K,hK⟩ := h
    let d := a.gcd b
    have hD : 0<d := Nat.gcd_pos_of_pos_left b (hpos a (hS ha))
    have hdCode : code d=K := (code_gcd (hpos a (hS ha)).ne' (hpos b (hS hb)).ne').trans (hK ha hb hab)
    have hsame : (S : Set ℕ).Pairwise (fun x y : ℕ => x.gcd y=d) := by
      intro x hx y hy hxy
      exact code_inj (Nat.gcd_pos_of_pos_left y (hpos x (hS hx))).ne' hD.ne'
        ((code_gcd (hpos x (hS hx)).ne' (hpos y (hS hy)).ne').trans ((hK hx hy hxy).trans hdCode.symm))
    refine ⟨d,hD,hsame,?_⟩
    intro x hx
    obtain ⟨y,hy,hyx⟩ := other x
    have hd := hsame hx hy hyx.symm
    refine ⟨x/d,?_,?_⟩
    · rw [← hd,Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)]
    · rw [← hd]
      apply coprime_quot (hpos x (hS hx)) (hpos y (hS hy))
      intro p p₁ p₂
      have hx' : p∈x.primeFactors := by
        rw [← Nat.support_factorization,Finsupp.mem_support_iff]; omega
      exact hw p (hpr x (hS hx) hx') x (hS hx) y (hS hy) p₁ p₂
  · refine ⟨1,by decide,?_,fun x _ => ⟨x,by simp,by simp⟩⟩
    intro a ha b hb hab
    exact (hn ⟨a,ha,b,hb,hab⟩).elim

end OMA.SunflowerFactors

open Finset OMA.SunflowerFactors

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.H2 := by
  classical
  intro r k A hA
  let D := A.biUnion Nat.primeFactors
  have hsub {n : ℕ} (hn : n∈A) : n.primeFactors⊆D := by
    intro p hp; exact mem_biUnion.mpr ⟨n,hn,hp⟩
  obtain ⟨B,hBA,hW,hC⟩ := prune A D k (fun n hn => (hA n hn).2)
  have same {n : ℕ} (hn : n∈A) : weight D n = 2^k := by
    unfold weight
    have h := sum_subset (hsub hn) (f:=fun q => n.factorization q) (by
      intro q _ hq
      simpa only [← Nat.support_factorization,Finsupp.mem_support_iff,not_ne_iff] using hq)
    rw [← h,total_exp,(hA n hn).2]
  refine ⟨B,hBA,?_,code,?_,fun n hn => (code_card n).trans (hA n (hBA hn)).2,?_⟩
  · calc
      A.card ≤ ∑ n ∈ B, weight D n := hW
      _ = ∑ _n ∈ B, 2^k := sum_congr rfl (fun n hn => same (hBA hn))
      _ = _ := by simp [mul_comm]
  · intro a ha b hb
    exact code_inj (by have := (hA a (hBA ha)).1; omega) (by have := (hA b (hBA hb)).1; omega)
  · intro S hS _ hg
    exact common_gcd hC hS (fun a ha => (hA a (hBA ha)).1) (fun _ ha => hsub (hBA ha)) hg
