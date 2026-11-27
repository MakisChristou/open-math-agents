import FormalConjectures.OEIS.«251758»
import Mathlib.Data.List.Sort
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic

/-! The least index with consecutive-divisor quotient eight (Robert G. Wilson v).
Replacing the distinct prime factors by the smallest admissible primes, while
preserving exponents, can only decrease the sorted divisors at each rank.
Divisor reflection therefore bounds the normalized sum of adjacent products
by the corresponding sum for the smaller prime factors. Divisor reflection
also appears for the value 14 in T. Adamczewski, arXiv:2608.11941, Appendix A. -/

namespace OMA.DivisorMinimum
open List
noncomputable section

def divisors (n : ℕ) := (List.range (n+1)).filter (fun d => d ∣ n)

lemma mem_divs {n d : ℕ} (hn : 0 < n) : d ∈ divisors n ↔ d ∣ n := by
  simp only [divisors,List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨by have := Nat.le_of_dvd hn h; omega,h⟩⟩

lemma divs_sorted (n : ℕ) : (divisors n).Pairwise (· < ·) :=
  (List.pairwise_lt_range.filter _)

lemma positive_divs {n d : ℕ} (hn : 0 < n) (hd : d ∈ divisors n) : 0 < d :=
  Nat.pos_of_dvd_of_pos ((mem_divs hn).mp hd) hn

def total : List ℕ → ℕ
  | a::b::tl => a*b + total (b::tl)
  | _ => 0

lemma total_eq (xs : List ℕ) :
    total xs = ((xs.zip xs.tail).map (fun p => p.1*p.2)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b tl => simpa [total] using congrArg (a*b + ·) ih

lemma a_eq (n : ℕ) : OeisA251758.a n = n^2 / total (divisors n) := by
  unfold OeisA251758.a
  simp only
  rw [total_eq]
  split <;> simp_all [divisors]

def weight (x : ℕ) : ℚ := (x:ℚ)⁻¹

def chain (w : ℚ) : List ℕ → ℚ
  | [] => 0
  | x::xs => w*weight x + chain (weight x) xs

lemma chain_last (w : ℚ) (xs : List ℕ) (x : ℕ) :
    chain w (xs ++ [x]) = chain w xs + (xs.getLast?.map weight).getD w * weight x := by
  induction xs generalizing w with
  | nil => simp [chain]
  | cons y ys ih =>
    cases ys with
    | nil => simp [chain]
    | cons z zs =>
      change w*weight y + chain (weight y) ((z::zs) ++ [x]) = _
      rw [ih]
      simp only [chain,List.getLast?_cons_cons,add_assoc]
      have he := List.getLast?_eq_some_getLast (l := z::zs) (by simp)
      simp [he]

lemma chain_reverse (xs : List ℕ) : chain 0 xs.reverse = chain 0 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,chain_last,ih]
    cases xs with
    | nil => simp [chain]
    | cons y ys => simp [chain, List.getLast?_reverse, mul_comm, add_comm]

lemma reflect {n : ℕ} (hn : 0 < n) :
    ((divisors n).map (n / ·)).reverse = divisors n := by
  let l := divisors n
  have pos (d) (hd : d ∈ l) := positive_divs hn hd
  have revmono : (l.map (n / ·)).reverse.Pairwise (· < ·) := by
    rw [List.pairwise_reverse,List.pairwise_map]
    apply (divs_sorted n).imp_of_mem
    intro x y hx hy hxy
    have hdx := (mem_divs hn).mp hx
    have hdy := (mem_divs hn).mp hy
    have h1 := Nat.div_mul_cancel hdx
    have h2 := Nat.div_mul_cancel hdy
    have h3 : 0 < n/y := Nat.div_pos (Nat.le_of_dvd hn hdy) (pos y hy)
    change n/y < n/x
    by_contra! h
    have hh := Nat.mul_lt_mul_of_pos_left hxy h3
    nlinarith [Nat.mul_le_mul_right x h]
  apply List.Perm.eq_of_pairwise' (revmono.imp Nat.le_of_lt) ((divs_sorted n).imp Nat.le_of_lt)
  · apply List.perm_ext_iff_of_nodup (revmono.imp Nat.ne_of_lt) ((divs_sorted n).imp Nat.ne_of_lt) |>.mpr
    intro d
    simp only [List.mem_reverse,List.mem_map]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (mem_divs hn).mpr (Nat.div_dvd_of_dvd ((mem_divs hn).mp ha))
    · intro hd
      have h := (mem_divs hn).mp hd
      exact ⟨n/d,(mem_divs hn).mpr (Nat.div_dvd_of_dvd h),Nat.div_div_self h hn.ne'⟩


lemma scale_chain {n : ℕ} (hn : 0 < n) (xs : List ℕ) (hxs : ∀ x ∈ xs, x ∣ n) :
    (total xs : ℚ) = (n:ℚ)^2 * chain 0 (xs.map (n/·)) := by
  have hw (a : ℕ) (ha : a ∣ n) : weight (n/a) = (a:ℚ)/n := by
    have ha' := Nat.pos_of_dvd_of_pos ha hn
    unfold weight
    rw [Nat.cast_div ha (by exact_mod_cast ha'.ne')]
    simp [inv_div]
  induction xs with
  | nil => simp [total,chain]
  | cons a xs ih =>
    cases xs with
    | nil => simp [total,chain]
    | cons b tl =>
      have ha := hw a (hxs a (by simp))
      have hb := hw b (hxs b (by simp))
      specialize ih (fun x hx => hxs x (by simp [hx]))
      simp only [total,Nat.cast_add,Nat.cast_mul,List.map_cons,chain,zero_mul,zero_add] at *
      rw [ih,ha,hb]
      field_simp

lemma normalized {n : ℕ} (hn : 0 < n) :
    (total (divisors n):ℚ) = (n:ℚ)^2 * chain 0 (divisors n) := by
  rw [scale_chain hn _ (fun _ h => (mem_divs hn).mp h),← chain_reverse,reflect hn]

/-- Every initial segment cut out by a value is at least as large in l. -/
def Covers (l u : List ℕ) : Prop :=
  ∀ k : ℕ, (u.filter (· ≤ k)).length ≤ (l.filter (· ≤ k)).length

lemma cover_perm {l u l' u' : List ℕ} (hl : l ~ l') (hu : u ~ u') (h : Covers l u) :
    Covers l' u' := by
  intro k
  simpa only [(hu.filter (· ≤ k)).length_eq, (hl.filter (· ≤ k)).length_eq] using h k

lemma separate {x : ℕ} {xs : List ℕ} (hs : (x::xs).Pairwise (· ≤ ·)) {k : ℕ} (hk : k < x) :
    xs.filter (· ≤ k) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have := (List.pairwise_cons.mp hs).1 a ha
  simp [show ¬a ≤ k by omega]

lemma weight_le {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) : weight y ≤ weight x := by
  exact inv_anti₀ (by exact_mod_cast hx : (0:ℚ) < x) (by exact_mod_cast hxy)

lemma chain_nonneg {a : ℚ} (ha : 0 ≤ a) (l : List ℕ) : 0 ≤ chain a l := by
  induction l generalizing a with
  | nil => simp [chain]
  | cons x xs ih =>
    have hx : 0 ≤ weight x := by unfold weight; positivity
    exact add_nonneg (mul_nonneg ha hx) (ih hx)

lemma chain_le {l u : List ℕ} (hl : l.Pairwise (· ≤ ·)) (hu : u.Pairwise (· ≤ ·))
    (hpos : ∀ x ∈ l, 0 < x) (h : Covers l u) {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) :
    chain a u ≤ chain b l := by
  induction u generalizing l a b with
  | nil => exact chain_nonneg (ha.trans hab) _
  | cons y ys ih =>
    cases l with
    | nil =>
      have hh := h y
      simp at hh
    | cons x xs =>
      have hxy : x ≤ y := by
        by_contra! hg
        have hh := h y
        simp [Nat.not_le_of_gt hg,separate hl hg] at hh
      have hcov : Covers xs ys := by
        intro k
        by_cases hy : y ≤ k
        · simpa [hy,hxy.trans hy] using h k
        · simp [separate hu (by omega : k < y)]
      have hw := weight_le (hpos x (by simp)) hxy
      have hw0 : 0 ≤ weight y := by unfold weight; positivity
      exact add_le_add (mul_le_mul hab hw hw0 (ha.trans hab))
        (ih (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp hu).2
          (fun z hz => hpos z (by simp [hz])) hcov hw0 hw)



abbrev Factor := ℕ × ℕ

def expand (p e : ℕ) (l : List ℕ) : List ℕ :=
  (List.range (e+1)).flatMap fun i => l.map (p^i * ·)

def enumerate : List Factor → List ℕ → List ℕ
  | [], l => l
  | (p,e)::ps, l => enumerate ps (expand p e l)

def size (ps : List Factor) := (ps.map (fun f => f.1 ^ f.2)).prod

def ordered (l : List ℕ) := l.insertionSort (· ≤ ·)

lemma expand_rel {p q e : ℕ} (hpq : p ≤ q) {l u : List ℕ} (hu : List.Forall₂ (· ≤ ·) l u) :
    List.Forall₂ (· ≤ ·) (expand p e l) (expand q e u) := by
  unfold expand
  generalize List.range (e+1) = is
  induction is with
  | nil => exact .nil
  | cons i is ih =>
    apply List.rel_append _ ih
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    exact hu.imp (fun x y hy => Nat.mul_le_mul (Nat.pow_le_pow_left hpq _) hy)

lemma rel_covers {l u : List ℕ} (h : List.Forall₂ (· ≤ ·) l u) : Covers l u := by
  intro k
  induction h with
  | nil => rfl
  | @cons x y l u hxy h ih =>
    by_cases hy : y ≤ k
    · simpa [hy,hxy.trans hy] using ih
    · by_cases hx : x ≤ k <;> simp [hx,hy] <;> omega

lemma mem_expand {x p e : ℕ} {l : List ℕ} : x ∈ expand p e l ↔
    ∃ i ≤ e, ∃ d ∈ l, p^i*d = x := by
  simp [expand]

lemma enumerate_spec {ps : List Factor} (hp : ∀ f ∈ ps, f.1.Prime)
    (l : List ℕ) (x : ℕ) :
    x ∈ enumerate ps l ↔ ∃ d ∈ l, ∃ v, v ∣ size ps ∧ v*d = x := by
  induction ps generalizing l x with
  | nil => simp [enumerate,size]
  | cons f fs ih =>
    obtain ⟨p,e⟩ := f
    have hp0 := hp (p,e) (by simp)
    have hps (f) (hf : f ∈ fs) := hp f (by simp [hf])
    rw [enumerate,ih hps]
    simp only [size,List.map_cons,List.prod_cons]
    constructor
    · rintro ⟨d,hd,v,hv,rfl⟩
      obtain ⟨i,hi,a,ha,rfl⟩ := mem_expand.mp hd
      exact ⟨a,ha,p^i*v,Nat.mul_dvd_mul (pow_dvd_pow p hi) hv,by ring⟩
    · rintro ⟨a,ha,v,hv,rfl⟩
      obtain ⟨b,c,hb,hc,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hv
      obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow hp0).mp hb
      exact ⟨p^i*a,mem_expand.mpr ⟨i,hi,a,ha,rfl⟩,c,hc,by ring⟩

lemma expand_pos {p e : ℕ} (hp : 0 < p) {l : List ℕ} (h : ∀ x ∈ l, 0 < x) :
    ∀ x ∈ expand p e l, 0 < x := by
  intro x hx
  obtain ⟨i,_,d,hd,rfl⟩ := mem_expand.mp hx
  exact Nat.mul_pos (pow_pos hp _) (h d hd)

def grid : ℕ := 100000000

/-- Round each scaled reciprocal product upward before adding. -/
def coarse (prev : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => grid/(prev*x)+1+coarse x xs

lemma coarse_bound (prev : ℕ) (l : List ℕ) :
    (grid:ℚ) * chain (weight prev) l ≤ (coarse prev l:ℚ) := by
  induction l generalizing prev with
  | nil => simp [chain,coarse]
  | cons x xs ih =>
    have h : (grid:ℚ)*weight prev*weight x ≤ ((grid/(prev*x)+1 : ℕ):ℚ) := by
      by_cases h0 : prev*x = 0
      · rcases Nat.mul_eq_zero.mp h0 with rfl|rfl <;> simp [weight]
      · have hp : (0:ℚ) < (prev:ℚ)*x := by exact_mod_cast Nat.pos_of_ne_zero h0
        have hc : (grid:ℚ) ≤ ((prev*x:ℕ):ℚ)*((grid/(prev*x)+1:ℕ):ℚ) := by
          exact_mod_cast (Nat.lt_mul_div_succ grid (Nat.pos_of_ne_zero h0)).le
        rw [Nat.cast_mul] at hc
        unfold weight
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_div, div_le_iff₀ hp]
        simpa [mul_comm] using hc
    simp only [chain,coarse,Nat.cast_add,mul_add,← mul_assoc] at *
    linarith [ih x]

def bound : ℕ := 35336848261
def primes : List ℕ := [11,13,17,19,23,29,31,37]

/-- Only descend while the compressed product could occur below the bound. -/
def verify : List ℕ → ℕ → List ℕ → Bool
  | [], _, _ => false
  | b::bs, c, l =>
    decide (9*coarse 0 (ordered l) < grid) &&
      (List.range 10).all (fun i =>
        let e := i+1
        if c*b^e < bound then verify bs (c*b^e) (expand b e l) else true)



def gaps : ℕ → List ℕ → Bool
  | _, [] => true
  | lo, b::bs => (decide (lo < b) && (List.range b).all (fun x => decide (x ≤ lo ∨ ¬x.Prime))) && gaps b bs

lemma gap_lower {lo b p : ℕ} {bs : List ℕ} (hg : gaps lo (b::bs) = true)
    (hp : p.Prime) (hlo : lo < p) : b ≤ p := by
  by_contra! h
  have h0 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).2
  have h1 := List.all_eq_true.mp h0 p (List.mem_range.mpr h)
  simp [Nat.not_le_of_gt hlo,hp] at h1

lemma size_pos {fs : List Factor} (hp : ∀ f ∈ fs, f.1.Prime) : 0 < size fs := by
  induction fs with
  | nil => decide
  | cons f fs ih =>
    change 0 < f.1^f.2 * size fs
    exact Nat.mul_pos (pow_pos (hp f (by simp)).pos _) (ih (fun x hx => hp x (by simp [hx])))

lemma walk {bs : List ℕ} {lo c : ℕ} {l u : List ℕ}
    (hg : gaps lo bs = true) (hv : verify bs c l = true) (hc : 0 < c)
    (hb : 7 ≤ lo) (hpL : ∀ x ∈ l, 0 < x) (hr : List.Forall₂ (· ≤ ·) l u)
    (fs : List Factor) (hs : fs.Pairwise (fun a b => a.1 < b.1))
    (hp : ∀ f ∈ fs, lo < f.1 ∧ f.1.Prime ∧ 1 ≤ f.2 ∧ f.2 ≤ 10)
    (hsize : c*size fs < bound) :
    ∃ l' : List ℕ, (∀ x ∈ l', 0 < x) ∧ List.Forall₂ (· ≤ ·) l' (enumerate fs u) ∧
      9*coarse 0 (ordered l') < grid := by
  induction bs generalizing fs lo c l u with
  | nil => simp [verify] at hv
  | cons b bs ih =>
    obtain ⟨here,branches⟩ := Bool.and_eq_true_iff.mp hv
    cases fs with
    | nil => exact ⟨l,hpL,hr,of_decide_eq_true here⟩
    | cons f fs =>
      obtain ⟨p,e⟩ := f
      obtain ⟨hl,hpr,he,he'⟩ := hp (p,e) (by simp)
      have hbp := gap_lower hg hpr hl
      have hstep : c*b^e * size fs < bound := by
        change c*(p^e * size fs) < bound at hsize
        calc
          _ ≤ c*p^e * size fs := by gcongr
          _ = _ := Nat.mul_assoc _ _ _
          _ < bound := hsize
      have hrest : 0 < size fs := size_pos (fun f hf => (hp f (by simp [hf])).2.1)
      have hcb : c*b^e < bound := (Nat.le_mul_of_pos_right _ hrest).trans_lt hstep
      have heq : e-1+1=e := by omega
      have hv' := List.all_eq_true.mp branches (e-1) (List.mem_range.mpr (by omega))
      simp only [heq,if_pos hcb] at hv'
      have hlb : lo < b := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
      have hb0 : 0 < b := by omega
      apply ih (lo := b) (c := c*b^e) (l := expand b e l)
        (u := expand p e u) (Bool.and_eq_true_iff.mp hg).2 hv' (Nat.mul_pos hc (pow_pos hb0 _))
        (by omega) (expand_pos hb0 hpL) (expand_rel hbp hr) fs (List.pairwise_cons.mp hs).2
      · intro z hz
        have hprime := hp z (by simp [hz])
        exact ⟨hbp.trans_lt ((List.pairwise_cons.mp hs).1 _ hz),hprime.2⟩
      · exact hstep



lemma factors_exist {n : ℕ} (hn : 0 < n) (hB : n < bound)
    (hsmall : ∀ p, p.Prime → p ∣ n → 7 < p) :
    ∃ fs : List Factor, size fs = n ∧ fs.Pairwise (fun a b => a.1 < b.1) ∧
      ∀ f ∈ fs, 7 < f.1 ∧ f.1.Prime ∧ 1 ≤ f.2 ∧ f.2 ≤ 10 := by
  let ps := n.primeFactors.sort (· ≤ ·)
  let fs := ps.map (fun p => (p,n.factorization p))
  refine ⟨fs,?_,?_,?_⟩
  · unfold size fs
    simp only [List.map_map]
    calc
      _ = (n.primeFactors.toList.map fun p => p^n.factorization p).prod :=
        ((n.primeFactors.sort_perm_toList (· ≤ ·)).map _).prod_eq
      _ = n := (Finset.prod_map_toList _ _).trans (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  · simpa only [fs,List.pairwise_map] using n.primeFactors.sortedLT_sort.pairwise
  · intro f hf
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
    have hpf : p ∈ n.primeFactors := by simpa [ps] using hp
    obtain ⟨hpr,hd,_⟩ := Nat.mem_primeFactors.mp hpf
    have h7 := hsmall p hpr hd
    have h11 : 11 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at hpr
    refine ⟨h7,hpr,hpr.factorization_pos_of_dvd hn.ne' hd,?_⟩
    change n.factorization p ≤ 10
    by_contra! h
    have h11p : 11^11 ≤ p^(n.factorization p) :=
      (Nat.pow_le_pow_left h11 _).trans (Nat.pow_le_pow_right hpr.pos (by omega))
    have hd' : p^(n.factorization p) ≤ n := Nat.ordProj_le p hn.ne'
    have : bound < 11^11 := by decide
    omega

lemma divs_covered {n : ℕ} (hn : 0 < n) (fs : List Factor) (he : size fs = n)
    (hp : ∀ f ∈ fs, f.1.Prime) : Covers (enumerate fs [1]) (divisors n) := by
  have sub : divisors n ⊆ enumerate fs [1] := by
    intro d hd
    apply (enumerate_spec hp [1] d).mpr
    exact ⟨1,by simp,d,he.symm ▸ (mem_divs hn).mp hd,by simp⟩
  intro k
  exact ((List.subperm_of_subset ((divs_sorted n).imp Nat.ne_of_lt) sub).filter (· ≤ k)).length_le

lemma rough_bound {n : ℕ} (hn : 0 < n) (hB : n < bound)
    (hsmall : ∀ p, p.Prime → p ∣ n → 7 < p) (hv : verify primes 1 [1] = true) :
    9 * total (divisors n) < n^2 := by
  obtain ⟨fs,he,hs,hp⟩ := factors_exist hn hB hsmall
  have hpr (f) (hf : f ∈ fs) := (hp f hf).2.1
  obtain ⟨l,hpos,hr,hcheck⟩ := walk (lo := 7) (bs := primes) (c := 1) (l := [1]) (u := [1])
    (by decide) hv (by decide) (by decide) (by simp) (by repeat constructor) fs hs hp (by simpa [he] using hB)
  have hcov : Covers (ordered l) (divisors n) := by
    intro k
    have h1 := divs_covered hn fs he hpr k
    have h2 := rel_covers hr k
    have h3 := ((List.perm_insertionSort (· ≤ ·) l).filter (· ≤ k)).length_eq
    exact h1.trans (h2.trans h3.ge)
  have hchain := chain_le (List.pairwise_insertionSort (· ≤ ·) l) ((divs_sorted n).imp Nat.le_of_lt)
    (fun x hx => hpos x ((List.perm_insertionSort (· ≤ ·) _).mem_iff.mp hx)) hcov (a := 0) (by rfl) (by rfl)
  change chain 0 (divisors n) ≤ chain 0 (ordered l) at hchain
  have hround := coarse_bound 0 (ordered l)
  have hG : (0:ℚ) < grid := by decide
  have hrat : (9:ℚ)*coarse 0 (ordered l) < grid := by exact_mod_cast hcheck
  have hw : weight 0 = 0 := by simp [weight]
  rw [hw] at hround
  have hlt : 9 * chain 0 (divisors n) < 1 := by
    by_contra! h
    have h1 := mul_le_mul_of_nonneg_left hchain hG.le
    have h2 := mul_le_mul_of_nonneg_left h hG.le
    nlinarith only [h1,h2,hrat,hround]
  have hscale := normalized hn
  have hn2 : (0:ℚ) < (n:ℚ)^2 := by positivity
  exact_mod_cast (show (9:ℚ)*total (divisors n) < (n:ℚ)^2 by
    nlinarith only [hscale,mul_lt_mul_of_pos_left hlt hn2])



lemma small_bound {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hd : p ∣ n) :
    OeisA251758.a n ≤ p := by
  have hsub : [1,p] ⊆ divisors n := by
    intro d h
    simp at h
    rcases h with rfl|rfl <;> simp [mem_divs hn,hd]
  have hnodup : [1,p].Nodup := by simp [Ne.symm hp.ne_one]
  have hc : Covers (divisors n) [1,p] := fun k =>
    ((List.subperm_of_subset hnodup hsub).filter (· ≤ k)).length_le
  have hh := chain_le ((divs_sorted n).imp Nat.le_of_lt)
    (u := [1,p]) (by simp [hp.one_le]) (fun _ h => positive_divs hn h) hc (a := 0) (by rfl) (by rfl)
  simp [chain,weight] at hh
  have hp' : (0:ℚ) < p := by exact_mod_cast hp.pos
  have hn' : 0 ≤ (n:ℚ)^2 := sq_nonneg _
  have h1 : 1 ≤ (p:ℚ)*chain 0 (divisors n) := by
    simpa [hp'.ne'] using mul_le_mul_of_nonneg_left hh hp'.le
  have hv := normalized hn
  have h2 : n^2 ≤ p*total (divisors n) := by
    exact_mod_cast (show (n:ℚ)^2 ≤ (p:ℚ)*total (divisors n) by
      rw [hv]; nlinarith only [mul_le_mul_of_nonneg_left h1 hn'])
  rw [a_eq]
  exact Nat.div_le_of_le_mul (by simpa [mul_comm] using h2)

def firstFactors : List Factor := primes.map (·,1)

lemma first_size : size firstFactors = bound := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma first_value : OeisA251758.a bound = 8 := by
  let l := ordered (enumerate firstFactors [1])
  have hp : ∀ f ∈ firstFactors, f.1.Prime := by decide
  have hmem {d : ℕ} : d ∈ l ↔ d ∣ bound := by
    change d ∈ (enumerate firstFactors [1]).insertionSort (· ≤ ·) ↔ _
    rw [(List.perm_insertionSort (· ≤ ·) _).mem_iff,enumerate_spec hp,first_size]
    simp
  have hl : l.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hd : l.Nodup := by decide +kernel
  have heq : l = divisors bound := by
    apply List.Perm.eq_of_pairwise' hl ((divs_sorted _).imp Nat.le_of_lt)
    apply (List.perm_ext_iff_of_nodup hd ((divs_sorted _).imp Nat.ne_of_lt)).mpr
    exact fun d => hmem.trans (mem_divs (by decide : 0 < bound)).symm
  rw [a_eq,← heq]
  decide +kernel

lemma first_index : Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8) = bound := by
  have hk : Nat.primeCounting' 8 = 4 := by decide
  rw [hk,Nat.kthPrimorial_four]
  norm_num [bound,Nat.kthPrimorial,Finset.prod_range_succ]

lemma least_of_certificate (hv : verify primes 1 [1] = true) :
    IsLeast {x : ℕ | 2 ≤ x ∧ OeisA251758.a x = 8} bound := by
  refine ⟨⟨by decide,first_value⟩,?_⟩
  rintro n ⟨hn,he⟩
  by_contra! h
  have hn' : 0 < n := by omega
  have hsmall (p) (hp : p.Prime) (hd : p ∣ n) : 7 < p := by
    have := small_bound hn' hp hd
    omega
  have hlt := rough_bound hn' h hsmall hv
  rw [a_eq] at he
  have hpos : 0 < total (divisors n) := by
    by_contra! h0; simp [Nat.eq_zero_of_le_zero h0] at he
  have h9 := (Nat.le_div_iff_mul_le hpos).mpr hlt.le
  omega



/-- Split the computational certificate by the first exponents, so the
kernel can check each small subtree separately. -/
lemma verify_step {b c : ℕ} {bs l : List ℕ}
    (h : 9*coarse 0 (ordered l) < grid)
    (branches : ∀ i : Fin 10, c*b^(i.val+1) < bound →
      verify bs (c*b^(i.val+1)) (expand b (i.val+1) l) = true) :
    verify (b::bs) c l = true := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, h, true_and, List.all_eq_true]
  intro i hi
  split
  · exact branches ⟨i,List.mem_range.mp hi⟩ (by assumption)
  · rfl

def remainingPrimes : List ℕ := [17,19,23,29,31,37]

def goodSecond (a i : ℕ) :=
  if 11^a*13^(i+1) < bound then
    verify remainingPrimes (11^a*13^(i+1)) (expand 13 (i+1) (expand 11 a [1]))
  else true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_1 (i : Fin 10) : goodSecond 1 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_2 (i : Fin 10) : goodSecond 2 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_3 (i : Fin 10) : goodSecond 3 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_4 (i : Fin 10) : goodSecond 4 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_5 (i : Fin 10) : goodSecond 5 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_6 (i : Fin 10) : goodSecond 6 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_7 (i : Fin 10) : goodSecond 7 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_8 (i : Fin 10) : goodSecond 8 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_9 (i : Fin 10) : goodSecond 9 i.val = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma second_10 (i : Fin 10) : goodSecond 10 i.val = true := by
  fin_cases i <;> decide +kernel

lemma verified : verify primes 1 [1] = true := by
  apply verify_step (by decide)
  intro a ha
  apply verify_step
  · fin_cases a <;> decide +kernel
  · intro i hi
    have h1 : 11^(a.val+1)*13^(i.val+1) < bound := by simpa using hi
    have h2 : goodSecond (a.val+1) i.val = true := by
      fin_cases a
      · exact second_1 i
      · exact second_2 i
      · exact second_3 i
      · exact second_4 i
      · exact second_5 i
      · exact second_6 i
      · exact second_7 i
      · exact second_8 i
      · exact second_9 i
      · exact second_10 i
    simpa [goodSecond,h1,remainingPrimes] using h2


end
end OMA.DivisorMinimum
open OMA.DivisorMinimum in
theorem OMA.solution : type_of% @OeisA251758.conjecture := by
  rw [first_index]
  exact least_of_certificate verified
