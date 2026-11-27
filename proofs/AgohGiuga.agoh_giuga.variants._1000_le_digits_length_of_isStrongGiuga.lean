import FormalConjectures.Wikipedia.AgohGiuga
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Bitwise

/-! The block power sum in a prime field gives both necessary
divisibilities for a counterexample to Giuga's primality criterion.
Following Giuga, Bedocchi, and D. Borwein, J. M. Borwein, P. B. Borwein
and R. Girgensohn (American Mathematical Monthly 103, 1996), exploit that
no prime factor can divide another prime factor minus one. We bound the
reciprocal sum by charging an allowance for each binary logarithm of p⁴.
A group contains a center p and numbers pk+1. Only the center or the leaves
can contribute, so a maximum bounds their combined excess. The sieve coverage
and each group's charge is checked by kernel reduction. -/

namespace OMA.GiugaBounds
open AgohGiuga Finset
noncomputable section

lemma blocks (p d k : ℕ) :
    (∑ i ∈ range (d*p), (i:ZMod p)^k) = (d:ZMod p) * ∑ i ∈ range p, (i:ZMod p)^k := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    push_cast
    simp [add_mul]

lemma field_sum {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (∑ i ∈ range p, (i:ZMod p)^k) = if p-1 ∣ k then -1 else 0 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hf : (∑ i ∈ range p, (i:ZMod p)^k) = ∑ x : ZMod p, x^k := by
    rw [← Fin.sum_univ_eq_sum_range]
    have h (x : Fin p) : (x.val : ZMod p) = ZMod.finEquiv p x := by
      cases p with
      | zero => exact (Nat.not_prime_zero hp).elim
      | succ p => exact ZMod.natCast_zmod_val (n := p+1) x
    simp only [h]
    exact (ZMod.finEquiv p).toEquiv.sum_comp (fun x => x^k)
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨Units.val,Units.val_injective⟩
  have himg : univ.map emb = univ \ {(0:ZMod p)} := by
    ext x
    simp only [mem_map,mem_univ,true_and,mem_sdiff,mem_singleton,emb,Function.Embedding.coeFn_mk]
    exact isUnit_iff_ne_zero
  calc
    _ = ∑ x : ZMod p, x^k := hf
    _ = ∑ x ∈ univ \ {(0:ZMod p)}, x^k := by
      rw [← sum_sdiff ({0}:Finset (ZMod p)).subset_univ (f := fun x => x^k)]
      simp [hk]
    _ = ∑ x : (ZMod p)ˣ, (x:ZMod p)^k := by rw [← himg, sum_map]; rfl
    _ = _ := by simpa using FiniteField.sum_pow_units (ZMod p) k

lemma local_conditions {n : ℕ} (hh : IsStrongGiuga n) {p : ℕ} (hp : p.Prime) (hd : p ∣ n) :
    (p-1 ∣ n-1) ∧ (p ∣ n/p-1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hn : 1 < n := hh.1.1
  have hk : n-1 ≠ 0 := by omega
  have he : (Ioo 0 n) = (range n).erase 0 := by ext i; simp; omega
  have hs : (∑ i ∈ Ioo 0 n, i^(n-1)) = ∑ i ∈ range n, i^(n-1) := by
    rw [he]
    have hz := add_sum_erase (range n) (fun i => i^(n-1)) (mem_range.mpr (by omega : 0<n))
    simpa [zero_pow hk] using hz
  have hsum := hd.trans hh.2
  rw [hs,← ZMod.natCast_eq_zero_iff, Nat.cast_add,Nat.cast_one,Nat.cast_sum] at hsum
  push_cast at hsum
  have hblock := blocks p (n/p) (n-1)
  rw [Nat.div_mul_cancel hd,field_sum hp hk] at hblock
  rw [hblock] at hsum
  split_ifs at hsum with hc
  · refine ⟨hc,?_⟩
    have hpos : 1 ≤ n/p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    rw [← ZMod.natCast_eq_zero_iff,Nat.cast_sub hpos,Nat.cast_one]
    linear_combination -hsum
  · simp at hsum

lemma squarefree {n : ℕ} (h : IsStrongGiuga n) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hp0 := hp.pos
  obtain ⟨k,hk⟩ := hd
  have hd' : p ∣ n := ⟨p*k,by rw [hk];ring⟩
  have hq := (local_conditions h hp hd').2
  have hdiv : n/p = p*k := by rw [hk,mul_assoc,Nat.mul_div_cancel_left _ hp0]
  rw [hdiv] at hq
  have hn : 1<n := h.1.1
  have hpos : 1 ≤ p*k := by rw [← hdiv]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hd') hp0
  have heq : 1 + (p*k-1) = p*k := by omega
  have h01 : p ∣ 1 := (Nat.dvd_add_left hq).mp (heq.symm ▸ dvd_mul_right p k)
  exact hp.not_dvd_one h01

lemma carmichael {n : ℕ} (h : IsStrongGiuga n) : IsCarmichael n := by
  exact (korselts_criterion n h.1).mpr ⟨squarefree h,fun _ hp hd => (local_conditions h hp hd).1⟩

def Normal (s : Finset ℕ) := ∀ p ∈ s, ∀ q ∈ s, ¬p ∣ q-1

lemma normal {n : ℕ} (h : IsStrongGiuga n) : Normal n.primeFactors := by
  intro p hp q hq hbad
  obtain ⟨pr,hd,_⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨qr,hqd,_⟩ := Nat.mem_primeFactors.mp hq
  have hh := hbad.trans (local_conditions h qr hqd).1
  have hn : 1<n := h.1.1
  have he : 1+(n-1)=n := by omega
  exact pr.not_dvd_one ((Nat.dvd_add_left hh).mp (he.symm ▸ hd))

lemma no_two {n : ℕ} (h : IsStrongGiuga n) : 2 ∉ n.primeFactors := by
  intro ht
  have hs : n.primeFactors = {2} := by
    ext p
    simp only [mem_singleton]
    constructor
    · intro hp
      by_contra hh
      exact normal h 2 ht p hp ((even_iff_two_dvd.mp ((Nat.prime_of_mem_primeFactors hp).even_sub_one hh)))
    · rintro rfl; exact ht
  have hn := Nat.prod_primeFactors_of_squarefree (squarefree h)
  rw [hs] at hn
  simp at hn
  exact h.1.2 (hn ▸ Nat.prime_two)

def grid : ℕ := 1000000000
def weight (p : ℕ) := (grid-1)/p+1
def cost (p : ℕ) := (p^4).log2

lemma sum_quotients {n : ℕ} (h : IsStrongGiuga n) :
    n < ∑ p ∈ n.primeFactors, n/p := by
  classical
  let s := n.primeFactors
  let W := ∑ p ∈ s, n/p
  have hn : 1 < n := h.1.1
  have hdW (p : ℕ) (hp : p ∈ s) : p ∣ W-1 := by
    obtain ⟨pr,hd,_⟩ := Nat.mem_primeFactors.mp hp
    have hm := (local_conditions h pr hd).2
    have hp1 : 1 ≤ n/p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) pr.pos
    have hs : p ∣ ∑ q ∈ s.erase p, n/q := by
      apply dvd_sum
      intro q hq
      obtain ⟨hne,hq'⟩ := mem_erase.mp hq
      obtain ⟨qr,qd,_⟩ := Nat.mem_primeFactors.mp hq'
      apply ((Nat.coprime_primes pr qr).mpr hne.symm).dvd_of_dvd_mul_right
      rwa [Nat.div_mul_cancel qd]
    have he := add_sum_erase s (fun q => n/q) hp
    change n/p + _ = W at he
    rw [← he,show n/p+(∑ q ∈ s.erase p, n/q)-1 = n/p-1 + (∑ q ∈ s.erase p, n/q) by omega]
    exact dvd_add hm hs
  have hdiv : n ∣ W-1 := by
    rw [← Nat.prod_primeFactors_of_squarefree (squarefree h)]
    apply Finset.prod_dvd_of_isRelPrime _ hdW
    intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hne)
  obtain ⟨p,pr,hd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hp : p ∈ s := Nat.mem_primeFactors.mpr ⟨pr,hd,by omega⟩
  have hpos : 1 ≤ n/p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) pr.pos
  have hp2 : 1 < n/p := by
    by_contra! hle
    have he := Nat.div_mul_cancel hd
    rw [show n/p=1 by omega,one_mul] at he
    exact h.1.2 (he ▸ pr)
  have hle : n/p ≤ W := single_le_sum (f := fun q => n/q) (fun _ _ => Nat.zero_le _) hp
  have := Nat.le_of_dvd (by omega : 0 < W-1) hdiv
  change n < W
  omega

lemma mass {n : ℕ} (h : IsStrongGiuga n) : grid < ∑ p ∈ n.primeFactors, weight p := by
  have hin : 0 < grid := by decide
  have term (p : ℕ) (hp : p ∈ n.primeFactors) :
      grid*(n/p) ≤ n*weight p := by
    obtain ⟨pr,hd,_⟩ := Nat.mem_primeFactors.mp hp
    have h1 := Nat.lt_mul_div_succ (grid-1) pr.pos
    have h2 : grid ≤ p * weight p := by unfold weight; omega
    calc
      _ ≤ p * weight p * (n/p) := Nat.mul_le_mul_right _ h2
      _ = (n/p*p)*weight p := by ring
      _ = _ := by rw [Nat.div_mul_cancel hd]
  have ht := sum_le_sum term
  rw [← mul_sum, ← mul_sum] at ht
  have hh := Nat.mul_lt_mul_of_pos_left (sum_quotients h) hin
  rw [Nat.mul_comm grid n] at hh
  exact Nat.lt_of_mul_lt_mul_left (hh.trans_le ht)

lemma budget {n D L : ℕ} (hn : 0 < n) (hd : (Nat.digits 10 n).length ≤ D)
    (hb : (10^D)^4 ≤ 2^L) : (∑ p ∈ n.primeFactors, cost p) ≤ L := by
  have upper : n < 10^D := (Nat.lt_base_pow_length_digits (b := 10) (by decide)).trans_le
    (Nat.pow_le_pow_right (by decide) hd)
  have hs : 2^(∑ p ∈ n.primeFactors, cost p) ≤ n^4 := calc
    _ = ∏ p ∈ n.primeFactors, 2^cost p := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ n.primeFactors, p^4 := by
      apply Finset.prod_le_prod' (fun p hp => ?_)
      rw [cost,Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
    _ ≤ _ := by
      rw [Finset.prod_pow]
      exact Nat.pow_le_pow_left (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)) _
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hs.trans ((Nat.pow_le_pow_left upper.le 4).trans hb))



/-- Surplus above the current allowance per unit of binary logarithm. -/
def excess (b p : ℕ) := weight p-b*cost p

lemma excess_zero {p T b : ℕ} (hT : 0<T) (hp : T≤p) (h : weight T ≤ b*cost T) :
    excess b p = 0 := by
  have hw : weight p ≤ weight T := Nat.add_le_add_right (Nat.div_le_div_left hp hT) 1
  have hc : cost T ≤ cost p := by
    simp only [cost,Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.pow_le_pow_left hp _)
  exact Nat.sub_eq_zero_of_le (hw.trans (h.trans (Nat.mul_le_mul_left b hc)))

def listMask : List ℕ → ℕ
  | [] => 0
  | p::ps => 2^p ||| listMask ps

def onMask (b : ℕ) (s : Finset ℕ) (mask : ℕ) :=
  ∑ p ∈ s, if mask.testBit p then excess b p else 0

lemma on_zero (b : ℕ) (s : Finset ℕ) : onMask b s 0 = 0 := by simp [onMask]

lemma on_union (b : ℕ) (s : Finset ℕ) (m k : ℕ) :
    onMask b s (m ||| k) ≤ onMask b s m + onMask b s k := by
  unfold onMask
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  cases h : m.testBit p <;> cases h' : k.testBit p <;> simp [h,h']

lemma on_bit (b : ℕ) (s : Finset ℕ) (p : ℕ) :
    onMask b s (2^p) = if p ∈ s then excess b p else 0 := by
  simp [onMask,Nat.testBit_two_pow]

lemma on_list (b : ℕ) (s : Finset ℕ) (ps : List ℕ) :
    onMask b s (listMask ps) ≤ (ps.map (fun p => if p ∈ s then excess b p else 0)).sum := by
  induction ps with
  | nil => simp [listMask,on_zero]
  | cons p ps ih =>
    exact (on_union _ _ _ _).trans (by simpa [on_bit] using Nat.add_le_add_left ih (if p ∈ s then excess b p else 0))

abbrev Group := ℕ × List ℕ

def leaves (g : Group) := g.2.map (fun k => g.1*k+1)
def groupMask (g : Group) := listMask (g.1 :: leaves g)
def charge (b : ℕ) (g : Group) := max (excess b g.1) (((leaves g).map (excess b)).sum)

lemma group_bound {s : Finset ℕ} (hn : Normal s) (b : ℕ) (g : Group) :
    onMask b s (groupMask g) ≤ charge b g := by
  have h := on_list b s (g.1 :: leaves g)
  change onMask b s (listMask (g.1 :: leaves g)) ≤ _
  apply h.trans
  by_cases hc : g.1 ∈ s
  · have hh (q) (hq : q ∈ leaves g) : q ∉ s := by
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
      intro hq'
      exact hn _ hc _ hq' (by simp)
    have hsum : ((leaves g).map (fun q => if q ∈ s then excess b q else 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      simp [hh q hq]
    simp [hc,hsum,charge]
  · have hb (l : List ℕ) : (l.map (fun q => if q ∈ s then excess b q else 0)).sum ≤
        (l.map (excess b)).sum := by
      induction l with
      | nil => rfl
      | cons q qs ih => simp only [List.map_cons,List.sum_cons]; split <;> omega
    simpa [hc,charge] using (hb (leaves g)).trans (le_max_right (excess b g.1) _)

def allMask : List Group → ℕ
  | [] => 0
  | g::gs => groupMask g ||| allMask gs

def totalCharge (b : ℕ) (gs : List Group) := (gs.map (charge b)).sum

lemma all_bound {s : Finset ℕ} (hn : Normal s) (b : ℕ) (gs : List Group) :
    onMask b s (allMask gs) ≤ totalCharge b gs := by
  induction gs with
  | nil => simp [allMask,totalCharge,on_zero]
  | cons g gs ih =>
    exact (on_union _ _ _ _).trans (Nat.add_le_add (group_bound hn b g) ih)

def possible (yes no : List ℕ) (p : ℕ) : Bool :=
  (p != 2) && !(no.contains p) && yes.all (fun q => decide (¬q ∣ p-1)) && decide p.Prime

lemma possible_true {n : ℕ} (h : IsStrongGiuga n) {yes no : List ℕ}
    (hy : ∀ q ∈ yes, q ∈ n.primeFactors) (hn : ∀ q ∈ no, q ∉ n.primeFactors)
    {p : ℕ} (hp : p ∈ n.primeFactors) : possible yes no p = true := by
  have h2 : p ≠ 2 := fun he => no_two h (he ▸ hp)
  have hn' : p ∉ no := fun he => hn p he hp
  have hnrm (q) (hq : q ∈ yes) := normal h q (hy _ hq) p hp
  simp [possible,h2,hn',List.all_eq_true,Nat.prime_of_mem_primeFactors hp]
  exact hnrm

def Covers (yes no : List ℕ) (b mask lo hi : ℕ) : Prop :=
  ∀ p, lo ≤ p → p < hi → possible yes no p = true → excess b p ≠ 0 → mask.testBit p = true

/-- A finite pattern whose set bits have positions divisible by d. -/
def periodic (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => let m := periodic d k; m ||| (m <<< (d*2^k))

lemma periodic_sound {d k p : ℕ} (hh : (periodic d k).testBit p = true) : d ∣ p := by
  induction k generalizing p with
  | zero =>
    change (2^0 : ℕ).testBit p = true at hh
    simp only [Nat.testBit_two_pow,decide_eq_true_eq] at hh
    simp [← hh]
  | succ k ih =>
    simp only [periodic,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftLeft,
      Bool.and_eq_true,decide_eq_true_eq] at hh
    rcases hh with h | ⟨hle, h⟩
    · exact ih h
    · simpa only [Nat.sub_add_cancel hle] using dvd_add (ih h) (dvd_mul_right d (2^k))

def progressive (d T : ℕ) := periodic d ((T/d).log2+1)

def maskOf (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => f x ||| maskOf f xs

lemma maskOf_sound {f : ℕ → ℕ} {xs : List ℕ} {p : ℕ} (h : (maskOf f xs).testBit p = true) :
    ∃ x ∈ xs, (f x).testBit p = true := by
  induction xs with
  | nil => simp [maskOf] at h
  | cons x xs ih =>
    simp only [maskOf,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨x,by simp,h⟩
    · obtain ⟨y,hy,hh⟩ := ih h
      exact ⟨y,by simp [hy],hh⟩

lemma listMask_sound {xs : List ℕ} {p : ℕ} (h : (listMask xs).testBit p = true) : p ∈ xs := by
  induction xs with
  | nil => simp [listMask] at h
  | cons x xs ih =>
    simp only [listMask,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at h
    rcases h with rfl|h
    · simp
    · simp [ih h]

def badMask (T : ℕ) (yes no ds : List ℕ) :=
  listMask (0::1::2::no) |||
    maskOf (fun i => progressive (i+2) T <<< (2*(i+2))) ds |||
    maskOf (fun q => progressive q T <<< 1) yes

lemma badMask_false {T p : ℕ} {yes no ds : List ℕ} (hp : possible yes no p = true) :
    (badMask T yes no ds).testBit p = false := by
  simp [possible,List.all_eq_true] at hp
  obtain ⟨⟨⟨h2,hn⟩,hy⟩,pr⟩ := hp
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [badMask,Nat.testBit_or,Bool.or_eq_true] at h
  rcases h with (h|h)|h
  · have hs := listMask_sound h
    simp [pr.ne_zero,pr.ne_one,h2,hn] at hs
  · obtain ⟨i,_,hi⟩ := maskOf_sound h
    simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at hi
    obtain ⟨hle,hh⟩ := hi
    have hd := periodic_sound hh
    have hmul : i+2 ∣ 2*(i+2) := dvd_mul_left _ _
    have ht : i+2 ∣ p := by simpa only [Nat.sub_add_cancel hle] using dvd_add hd hmul
    have he := (Nat.dvd_prime_two_le pr (by omega)).mp ht
    omega
  · obtain ⟨q,hq,hh⟩ := maskOf_sound h
    simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hy q hq (periodic_sound hh.2)

lemma covers_sieve {T b m : ℕ} {yes no ds : List ℕ}
    (hm : ((m ||| badMask T yes no ds) &&& (2^T-1)) = 2^T-1) : Covers yes no b m 0 T := by
  intro p _ hT hp _
  have hh := congrArg (fun x : ℕ => x.testBit p) hm
  simpa [Nat.testBit_two_pow_sub_one,hT,badMask_false (ds := ds) hp] using hh


lemma enough {n L : ℕ} (h : IsStrongGiuga n) (hL : (∑ p ∈ n.primeFactors, cost p) ≤ L)
    {yes no : List ℕ} (hy : ∀ p ∈ yes, p ∈ n.primeFactors)
    (hn : ∀ p ∈ no, p ∉ n.primeFactors) (b T : ℕ) (gs : List Group)
    (hT : 0<T) (ht : weight T ≤ b*cost T)
    (hcover : Covers yes no b (allMask gs) 0 T)
    (hc : b*L+totalCharge b gs ≤ grid) : False := by
  have hbonus (p) (hp : p ∈ n.primeFactors) :
      weight p ≤ b*cost p + (if (allMask gs).testBit p then excess b p else 0) := by
    by_cases he : excess b p = 0
    · have hh : weight p ≤ b*cost p := Nat.sub_eq_zero_iff_le.mp he
      simp [he,hh]
    · have hl : p < T := by_contra fun hh => he (excess_zero hT (by omega) ht)
      have hh := hcover p (Nat.zero_le _) hl (possible_true h hy hn hp) he
      simp [hh,excess]; omega
  have hsum := sum_le_sum hbonus
  rw [sum_add_distrib,← mul_sum] at hsum
  have hcap := all_bound (normal h) b gs
  have hb := Nat.mul_le_mul_left b hL
  have hm := mass h
  unfold onMask at hcap
  omega



private def case1Group1 : List Group := [
  (3,[]),(5,[2,8,14,20,26,38,50,56,62,80,86,92,98,104,128,140,152,164,176,182,188,194,206,212,218,230,236,260,272,290,296,302,314,320,344,362,374,380,386,416,422,428,470,476,482,488,506,518,524,542,548,560,572,602,608,638,644,650,674,692,698,716,734,740,752,764,770,776,782,800,818,842,848,854,878,884,890,896,938]),(17,[]),(23,[]),(29,[]),(47,[]),
  (53,[]),(59,[]),(83,[]),(89,[]),(107,[]),(113,[]),
  (137,[]),(149,[]),(167,[]),(173,[]),(179,[]),(197,[]),
  (227,[]),(233,[]),(239,[]),(257,[]),(263,[]),(269,[]),
  (293,[]),(317,[]),(347,[]),(353,[]),(359,[]),(383,[]),
  (389,[]),(419,[]),(443,[]),(449,[]),(467,[]),(479,[]),
  (503,[]),(509,[]),(557,[]),(563,[]),(569,[]),(587,[]),
  (593,[]),(599,[]),(617,[]),(647,[]),(653,[]),(659,[])]

private def case1Group2 : List Group := [
  (677,[]),(683,[]),(719,[]),(743,[]),(773,[]),(797,[]),
  (809,[]),(827,[]),(839,[]),(857,[]),(863,[]),(887,[]),
  (929,[]),(947,[]),(953,[]),(977,[]),(983,[]),(1013,[]),
  (1019,[]),(1049,[]),(1097,[]),(1103,[]),(1109,[]),(1163,[]),
  (1187,[]),(1193,[]),(1217,[]),(1223,[]),(1229,[]),(1259,[]),
  (1277,[]),(1283,[]),(1289,[]),(1307,[]),(1319,[]),(1367,[]),
  (1373,[]),(1409,[]),(1427,[]),(1433,[]),(1439,[]),(1487,[]),
  (1493,[]),(1499,[]),(1523,[]),(1553,[]),(1559,[]),(1583,[])]

private def case1Group3 : List Group := [
  (1607,[]),(1613,[]),(1619,[]),(1637,[]),(1667,[]),(1697,[]),
  (1709,[]),(1733,[]),(1787,[]),(1823,[]),(1847,[]),(1877,[]),
  (1889,[]),(1907,[]),(1913,[]),(1949,[]),(1973,[]),(1979,[]),
  (1997,[]),(2003,[]),(2027,[]),(2039,[]),(2063,[]),(2069,[]),
  (2087,[]),(2099,[]),(2129,[]),(2153,[]),(2207,[]),(2213,[]),
  (2237,[]),(2243,[]),(2267,[]),(2273,[]),(2297,[]),(2309,[]),
  (2333,[]),(2339,[]),(2357,[]),(2393,[]),(2399,[]),(2417,[]),
  (2423,[]),(2447,[]),(2459,[]),(2477,[]),(2543,[]),(2549,[])]

private def case1Group4 : List Group := [
  (2579,[]),(2609,[]),(2633,[]),(2657,[]),(2663,[]),(2687,[]),
  (2693,[]),(2699,[]),(2729,[]),(2753,[]),(2777,[]),(2789,[]),
  (2819,[]),(2837,[]),(2843,[]),(2879,[]),(2897,[]),(2903,[]),
  (2909,[]),(2927,[]),(2939,[]),(2957,[]),(2963,[]),(2969,[]),
  (2999,[]),(3023,[]),(3083,[]),(3089,[]),(3119,[]),(3137,[]),
  (3167,[]),(3203,[]),(3209,[]),(3257,[]),(3299,[]),(3323,[]),
  (3329,[]),(3347,[]),(3359,[]),(3389,[]),(3407,[]),(3413,[]),
  (3449,[]),(3467,[]),(3527,[]),(3533,[]),(3539,[]),(3557,[])]

private def case1Group5 : List Group := [
  (3593,[]),(3617,[]),(3623,[]),(3659,[]),(3677,[]),(3719,[]),
  (3767,[]),(3779,[]),(3797,[]),(3803,[]),(3833,[]),(3863,[]),
  (3917,[]),(3923,[]),(3929,[]),(3947,[]),(3989,[]),(4007,[]),
  (4013,[]),(4019,[]),(4049,[]),(4073,[]),(4079,[]),(4127,[]),
  (4133,[]),(4139,[]),(4157,[]),(4217,[]),(4229,[]),(4253,[]),
  (4259,[]),(4283,[]),(4289,[]),(4337,[]),(4349,[]),(4373,[]),
  (4397,[]),(4409,[]),(4457,[]),(4463,[]),(4493,[]),(4517,[]),
  (4523,[]),(4547,[]),(4583,[]),(4637,[]),(4643,[]),(4649,[])]

private def case1Group6 : List Group := [
  (4673,[]),(4679,[])]

private def case1Groups : List Group := List.flatten [case1Group1, case1Group2, case1Group3, case1Group4, case1Group5, case1Group6]

private def case1Mask : ℕ := 0x800820000020820000000000000800000000800000820000020020000820800000020020020800020000020020000000000020800800820020020020800000000000020000820800000000800820000020000000820820020000000000800020820800000020000800800020020000820000800820000000000800020000020800800000000820000020020000020000820800000000800000820020000000020800020000800800800020800000800000000020800000020020800800000800000020000800000020800000000020000800800800000020820000800800020820000800020000820000800020020020000020020020000800820800000820000020020020000800800000020800800000000000020000800820000820800820020000020800820000020020000020800000820000020800000000000020020020000800800820020800000800800000820000820000020000800020820020020800000800000800800000800000000000020020020020000000800000020000820820000800800820000000800800820820000000800820800020000000020820000000000800820020820000800000020820000020820000800800000000020820800000020020000800820000000820800020820020000800000820000820000800820020020000020020000800000800020000820000820820000020000820800020820000000020020800800800820020800800800020020800000820800000020800020020020820800820800000020800820800020020800020820020800800820820020820828

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case1Mask_eq : allMask case1Groups = case1Mask := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case1Charge : 4430*13334+totalCharge 4430 case1Groups ≤ grid := by decide +kernel

private def case1Divisors : List ℕ := [0,1,3,5,9,11,15,17,21,27,29,35,39,41,45,51,57,59,65]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case1Covers : Covers [3] [] 4430 (allMask case1Groups) 0 4703 := by
  rw [case1Mask_eq]
  apply covers_sieve (ds := case1Divisors)
  decide +kernel

private lemma case1Impossible {n : ℕ} (h : IsStrongGiuga n)
    (hL : (∑ p ∈ n.primeFactors, cost p) ≤ 13334)
    (hy : ∀ p ∈ [3], p ∈ n.primeFactors) (hn : ∀ p ∈ [], p ∉ n.primeFactors) : False :=
  enough h hL hy hn 4430 4703 case1Groups (by decide) (by decide) case1Covers case1Charge

private def case2Group1 : List Group := [
  (5,[2,6,8,12,14,20,26,30]),(7,[4,6,16,18,28,30,34,40,48,54,60,64,66,70,78,88,90,94,96,100,106,108,118,126,130,136,138,144,150,156,166,184,186,196,204,210,214,226,228,238,244,246,268,276,286,288,298,304,306,316,324,328,330,334,340]),(13,[4,6,12,24,34,40,46,52,66,72,90,94,96,100,102,114,124,142,144,150,156,160,172,180]),(17,[6,8,18,24,36,38,54,60,66,74,80,90,110,116,138]),(19,[10,12,22,24,30,40,58,64,82,94,100,108,118,120,124]),(23,[2,6,12,20,30,36,44,50,60,62,72,86]),
  (37,[4,6,16,40,48,54,60]),(59,[12,18,20,32]),(67,[4,24,30]),(73,[4,6,12,22,24]),(83,[2,6,12,24]),(89,[]),
  (97,[]),(107,[]),(109,[]),(163,[]),(173,[]),(179,[]),
  (181,[]),(193,[]),(199,[]),(227,[]),(233,[]),(241,[]),
  (251,[]),(257,[]),(263,[]),(271,[]),(283,[]),(311,[]),
  (317,[]),(331,[]),(347,[]),(349,[]),(353,[]),(359,[]),
  (367,[]),(373,[]),(383,[]),(389,[]),(397,[]),(401,[]),
  (431,[]),(433,[]),(467,[]),(479,[]),(487,[]),(503,[])]

private def case2Group2 : List Group := [
  (509,[]),(523,[]),(541,[]),(557,[]),(563,[]),(569,[]),
  (577,[]),(587,[]),(601,[]),(607,[]),(619,[]),(641,[]),
  (643,[]),(653,[]),(661,[]),(683,[]),(719,[]),(727,[]),
  (733,[]),(739,[]),(751,[]),(769,[]),(773,[]),(787,[]),
  (797,[]),(809,[]),(811,[]),(821,[]),(823,[]),(839,[]),
  (853,[]),(857,[]),(863,[]),(881,[]),(887,[]),(907,[]),
  (929,[]),(941,[]),(947,[]),(971,[]),(977,[]),(983,[]),
  (991,[]),(1019,[]),(1031,[]),(1033,[]),(1039,[]),(1049,[])]

private def case2Group3 : List Group := [
  (1061,[]),(1069,[]),(1087,[]),(1091,[]),(1097,[]),(1109,[]),
  (1117,[]),(1129,[]),(1153,[]),(1187,[]),(1193,[]),(1201,[]),
  (1213,[]),(1229,[]),(1231,[]),(1237,[]),(1277,[]),(1279,[]),
  (1283,[]),(1291,[]),(1297,[]),(1307,[]),(1319,[]),(1321,[]),
  (1367,[]),(1399,[]),(1409,[]),(1423,[]),(1433,[]),(1439,[]),
  (1447,[]),(1451,[]),(1453,[]),(1459,[]),(1487,[]),(1489,[]),
  (1493,[]),(1511,[]),(1523,[]),(1543,[]),(1549,[]),(1553,[]),
  (1567,[]),(1571,[]),(1579,[]),(1601,[]),(1619,[]),(1621,[])]

private def case2Group4 : List Group := [
  (1627,[]),(1637,[]),(1663,[]),(1669,[]),(1693,[]),(1697,[]),
  (1699,[]),(1721,[]),(1733,[]),(1741,[]),(1747,[]),(1759,[]),
  (1783,[]),(1789,[]),(1801,[]),(1811,[]),(1823,[]),(1831,[]),
  (1861,[]),(1867,[]),(1879,[]),(1907,[]),(1913,[]),(1931,[]),
  (1949,[]),(1987,[]),(1997,[]),(2027,[]),(2039,[]),(2063,[]),
  (2069,[]),(2083,[]),(2089,[]),(2099,[]),(2111,[]),(2113,[]),
  (2131,[]),(2137,[]),(2141,[]),(2153,[]),(2161,[]),(2179,[]),
  (2203,[]),(2207,[]),(2239,[]),(2251,[]),(2267,[]),(2273,[])]

private def case2Group5 : List Group := [
  (2287,[]),(2293,[]),(2309,[]),(2333,[]),(2351,[]),(2371,[]),
  (2377,[]),(2383,[]),(2389,[])]

private def case2Groups : List Group := List.flatten [case2Group1, case2Group2, case2Group3, case2Group4, case2Group5]

private def case2Mask : ℕ := 0x20a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28a0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case2Mask_eq : allMask case2Groups = case2Mask := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case2Charge : 9498*13334+totalCharge 9498 case2Groups ≤ grid := by decide +kernel

private def case2Divisors : List ℕ := [0,1,3,5,9,11,15,17,21,27,29,35,39,41,45]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private lemma case2Covers : Covers [] [3] 9498 (allMask case2Groups) 0 2393 := by
  rw [case2Mask_eq]
  apply covers_sieve (ds := case2Divisors)
  decide +kernel

private lemma case2Impossible {n : ℕ} (h : IsStrongGiuga n)
    (hL : (∑ p ∈ n.primeFactors, cost p) ≤ 13334)
    (hy : ∀ p ∈ [], p ∈ n.primeFactors) (hn : ∀ p ∈ [3], p ∉ n.primeFactors) : False :=
  enough h hL hy hn 9498 2393 case2Groups (by decide) (by decide) case2Covers case2Charge

lemma digit_bound (n : ℕ) (h : IsStrongGiuga n) : 1000 < (Nat.digits 10 n).length := by
  by_contra! hd
  have hL := budget (n := n) (L := 13334) (Nat.zero_lt_of_lt h.1.1) hd (by decide +kernel)
  by_cases h3 : 3 ∈ n.primeFactors
  · exact case1Impossible h hL (by simpa using h3) (by simp)

  · exact case2Impossible h hL (by simp) (by simpa using h3)

end
end OMA.GiugaBounds

theorem OMA.solution : type_of% @AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga := by
  intro n hn
  have := OMA.GiugaBounds.digit_bound n hn
  omega
