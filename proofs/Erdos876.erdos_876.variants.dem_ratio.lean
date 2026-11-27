import FormalConjectures.ErdosProblems.«876»
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.PSeries

/-! Fractional-part construction of Deshouillers, Erdős and Melfi (1999).
The rotation by sqrt 2 hits every interval of width w in O(1/w)
successive steps, by rational approximation and a permuted grid. -/

namespace OMA.SumFreeConstruction
open Finset Filter Real Erdos876
open scoped Topology
noncomputable section

lemma approx (N : ℕ) (hN : 0 < N) : ∃ q : ℚ, 0 ≤ q.num ∧ q.den ≤ N ∧
    (N:ℝ) ≤ 5*q.den ∧ |√2 - (q:ℝ)| ≤ 1/(((N:ℝ)+1)*q.den) := by
  obtain ⟨q,err,den⟩ := exists_rat_abs_sub_le_and_den_le (√2) hN
  have pd : (0:ℝ) < q.den := by exact_mod_cast q.pos
  have d1 : (1:ℝ) ≤ q.den := by exact_mod_cast q.pos
  have N1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have e1 : 1/(((N:ℝ)+1)*q.den) ≤ 1 := by
    apply div_le_one_of_le₀ _ (by positivity)
    nlinarith
  have rt := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have nr := Real.sqrt_nonneg (2:ℝ)
  have hb := abs_le.mp (err.trans e1)
  have ht₁ : 1 < √(2:ℝ) := by nlinarith
  have ht₂ : √(2:ℝ) < 1.5 := by nlinarith
  have qpos : 0 < (q:ℝ) := by linarith
  have num : (q.num:ℝ) / q.den = q := by exact_mod_cast q.num_div_den
  have numpos : 0 ≤ q.num := by
    have : (0:ℝ) ≤ q.num := by rw [← num] at qpos; exact (pos_of_mul_pos_left (by simpa [div_mul_cancel₀ _ pd.ne'] using mul_pos qpos pd : 0 < (q.num:ℝ) * 1) (by norm_num)).le
    exact_mod_cast this
  have neq : q.num^2 - 2*(q.den:ℤ)^2 ≠ 0 := by
    intro z
    have z' : (q.num:ℝ)^2 - 2*(q.den:ℝ)^2 = 0 := by exact_mod_cast z
    have q2 : (q:ℝ)^2 = 2 := by rw [←num,div_pow]; field_simp; linarith
    have eq : √(2:ℝ) = q := by nlinarith
    exact irrational_sqrt_two ⟨q,eq.symm⟩
  have iabs : (1:ℤ) ≤ |q.num^2-2*(q.den:ℤ)^2| := by
    have hh := abs_pos.mpr neq
    omega
  have idef : (1:ℝ) ≤ |(q.num:ℝ)^2-2*(q.den:ℝ)^2| := by exact_mod_cast iabs
  have qd : (q:ℝ)*q.den = q.num := (eq_div_iff pd.ne').mp num.symm
  have eq : |(q.num:ℝ)^2-2*(q.den:ℝ)^2| = (q.den:ℝ)^2 * |√2-(q:ℝ)| * (√2+(q:ℝ)) := by
    calc
      _ = |(q.den:ℝ)^2 * (√2-(q:ℝ)) * (√2+(q:ℝ))| := by
        rw [← abs_neg ((q.num:ℝ)^2-2*(q.den:ℝ)^2)]
        congr 1
        nlinarith [congrArg (fun t : ℝ => t^2) qd,congrArg (fun t : ℝ => t*(q.den:ℝ)^2) rt]
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (show 0 ≤ √2+(q:ℝ) by positivity)]
  have e' := (le_div_iff₀ (by positivity : (0:ℝ) < ((N:ℝ)+1)*q.den)).mp err
  have b : √2+(q:ℝ) ≤ 5 := by linarith
  have cmp : 1 ≤ (q.den:ℝ)^2*|√2-(q:ℝ)| *5 :=
    (idef.trans_eq eq).trans (mul_le_mul_of_nonneg_left b (by positivity))
  have h := mul_le_mul_of_nonneg_right e' (show 0 ≤ (q.den:ℝ)*5 by positivity)
  have dd := mul_le_mul_of_nonneg_right cmp (show 0 ≤ (N:ℝ)+1 by positivity)
  refine ⟨q,numpos,den,?_,err⟩
  nlinarith

lemma hit (M L : ℕ) {u w : ℝ} (hu : 0 ≤ u) (hw : 0 < w) (hu' : u+w ≤ 1)
    (hL : 40 ≤ (L:ℝ)*w) :
    ∃ n, M ≤ n ∧ n < M+L ∧ u < Int.fract (√2*(n:ℝ)) ∧ Int.fract (√2*(n:ℝ)) < u+w := by
  have Lpos : 0 < L := by cases L with
    | zero => norm_num at hL
    | succ => omega
  obtain ⟨q,num,den,low,approxq⟩ := approx L Lpos
  let d := q.den
  let _ : NeZero d := ⟨q.den_nz⟩
  have pd : (0:ℝ) < d := by exact_mod_cast q.pos
  let b := u+w/2-√2*(M:ℝ)
  let r : ℤ := ⌊(d:ℝ)*b⌋
  let v := ZMod.unitOfCoprime q.num.natAbs q.reduced
  let j : ℕ := ((↑v⁻¹ : ZMod d)*(r:ZMod d)).val
  have jd : j < d := ZMod.val_lt _
  have castv : (↑v : ZMod d) = (q.num : ZMod d) := by
    change (q.num.natAbs : ZMod d) = (q.num:ZMod d)
    rw [← Int.cast_natCast (R:=ZMod d), Int.natCast_natAbs, abs_of_nonneg num]
  have con : ((r:ℤ):ZMod d) = ((j * q.num:ℤ):ZMod d) := by
    push_cast
    rw [←castv]
    unfold j
    rw [ZMod.natCast_zmod_val]
    simp [mul_comm,mul_left_comm]
  obtain ⟨h,hh⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp con
  have eqr : (j:ℝ)*q.num-(r:ℝ) = d*(h:ℝ) := by exact_mod_cast hh
  have numq : (q:ℝ)*d = q.num := by
    apply (eq_div_iff pd.ne').mp
    exact_mod_cast q.num_div_den.symm
  have err : |√2-(q:ℝ)| * (((L:ℝ)+1)*d) ≤ 1 := (le_div_iff₀ (by positivity)).mp approxq
  have jL : (j:ℝ) ≤ L+1 := by exact_mod_cast (show j ≤ L+1 by omega)
  have ej : |(j:ℝ)*(√2-(q:ℝ))*d| ≤ 1 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg j),abs_of_pos pd]
    calc
      _ ≤ ((L:ℝ)+1)*|√2-(q:ℝ)| *d := by gcongr
      _ ≤ 1 := by linarith only [err,show ((L:ℝ)+1)*|√2-(q:ℝ)| *d = |√2-(q:ℝ)| *(((L:ℝ)+1)*d) by ring]
  have fl : (r:ℝ) ≤ (d:ℝ)*b := Int.floor_le _
  have fr : (d:ℝ)*b < r+1 := Int.lt_floor_add_one _
  have room : 8 ≤ d*w := by nlinarith [mul_le_mul_of_nonneg_right low hw.le]
  let x := √2*((M:ℝ)+j) - (h:ℝ)
  have ident : (x-(u+w/2))*d = ((j:ℝ)*(√2-(q:ℝ))*d) + (r-d*b) := by
    dsimp [x,b]
    nlinarith [congrArg (fun t : ℝ => t*j) numq]
  have ex := abs_le.mp ej
  have lo : u < x := by
    apply (mul_lt_mul_iff_left₀ pd).mp
    nlinarith
  have hi : x < u+w := by
    apply (mul_lt_mul_iff_left₀ pd).mp
    nlinarith
  have fract : Int.fract (√2*((M+j:ℕ):ℝ)) = x := by
    have ax : √2*((M+j:ℕ):ℝ) = (h:ℝ)+x := by dsimp [x]; push_cast; ring
    rw [ax,Int.fract_intCast_add,Int.fract_eq_self.mpr ⟨hu.trans lo.le,hi.trans_le hu'⟩]
  exact ⟨M+j,by omega,by omega,fract.symm ▸ lo,fract.symm ▸ hi⟩


lemma window {x a c : ℝ} (hx : 1 < x) (ha : 1 ≤ a) (hc : 0 < c) :
    c/x^a + c/x^(a+1) ≤ c/(x-1)^a := by
  have px : 0 < x := by linarith
  have py : 0 < x-1 := by linarith
  have comp := Real.rpow_le_rpow py.le (show x-1 ≤ x by linarith) (show 0 ≤ a-1 by linarith)
  have fac (y : ℝ) (hy : 0 < y) : y^a = y^(a-1)*y := by
    conv_lhs => rw [show a = (a-1)+1 by ring]
    rw [rpow_add_one hy.ne']
  rw [rpow_add_one px.ne', fac (x-1) py, fac x px]
  have yp := rpow_pos_of_pos py (a-1)
  have xp := rpow_pos_of_pos px (a-1)
  calc
    _ ≤ c/(x^(a-1)*(x-1)) := by
      field_simp
      nlinarith
    _ ≤ _ := by gcongr

lemma step {a c : ℝ} (ha : 1 ≤ a) (hc : 0 < c) (hc' : c ≤ 1) (n : ℕ) :
    let K := 40/c+2
    ∃ f : ℕ, K*((n:ℝ)+2)^(a+2) ≤ f ∧ (f:ℝ) < K*((n:ℝ)+3)^(a+2) ∧
      c/((n:ℝ)+2)^a < Int.fract (√2*(f:ℝ)) ∧ Int.fract (√2*(f:ℝ)) < c/((n:ℝ)+1)^a := by
  let x := (n:ℝ)+2
  let K := 40/c+2
  let w := c/x^(a+1)
  have x1 : 1 < x := by dsimp [x]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have px : 0 < x := by linarith
  have py : 0 < x-1 := by linarith
  have pw : 0 < w := by dsimp [w]; positivity
  have pK : 0 < K := by dsimp [K]; positivity
  have u1 : 0 ≤ c/x^a := by positivity
  have W := window x1 ha hc
  have gap : c/x^a+w ≤ 1 := by
    refine W.trans ((div_le_one (rpow_pos_of_pos py a)).mpr ?_)
    have yy : 1 ≤ x-1 := by dsimp [x]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    exact hc'.trans (one_le_rpow yy (by linarith))
  let M := ⌈K*x^(a+2)⌉₊
  let L := ⌈40/w⌉₊
  have room : 40 ≤ (L:ℝ)*w := (div_le_iff₀ pw).mp (Nat.le_ceil _)
  obtain ⟨f,lo,hi,fr,fr'⟩ := hit M L u1 pw gap room
  have hi' : (f:ℝ) < M+(L:ℝ) := by exact_mod_cast hi
  have bM : (M:ℝ) < K*x^(a+2)+1 := Nat.ceil_lt_add_one (by positivity)
  have bL : (L:ℝ) < 40/w+1 := Nat.ceil_lt_add_one (by positivity)
  have eq : 40/w = (40/c)*x^(a+1) := by dsimp [w]; field_simp
  have g : 1 ≤ x^(a+1) := one_le_rpow x1.le (by linarith)
  have gain : x^(a+2) + x^(a+1) ≤ (x+1)^(a+2) := by
    rw [show a+2 = (a+1)+1 by ring,rpow_add_one px.ne',rpow_add_one (by positivity : x+1 ≠ 0)]
    calc
      _ = x^(a+1)*(x+1) := by ring
      _ ≤ _ := by gcongr; linarith
  refine ⟨f,(Nat.le_ceil (K*x^(a+2))).trans (show (M:ℝ) ≤ f by exact_mod_cast lo), ?_,fr, ?_⟩
  · change (f:ℝ) < K*((n:ℝ)+3)^(a+2)
    rw [show (n:ℝ)+3=x+1 by dsimp [x]; ring]
    have more : (40/c)*x^(a+1)+2 ≤ K*x^(a+1) := by dsimp [K]; nlinarith
    linarith [mul_le_mul_of_nonneg_left gain pK.le]
  · have := fr'.trans_le W
    rwa [show x-1=(n:ℝ)+1 by dsimp [x]; ring] at this

lemma constructed (δ : ℝ) (hδ : 0 < δ) :
    ∃ (f : ℕ → ℕ) (K : ℝ), StrictMono f ∧ 0 < K ∧
      (∀ n : ℕ, K*((n:ℝ)+2)^(3+δ) ≤ f n ∧ (f n:ℝ) < K*((n:ℝ)+3)^(3+δ)) ∧
      (∀ n, 0 < f n) ∧ StrictAnti (fun n => Int.fract (√2*(f n:ℝ))) ∧
      (∀ V : Finset ℕ, ∑ n ∈ V, Int.fract (√2*(f n:ℝ)) < 1) := by
  let a := 1+δ
  have ha : 1 < a := by dsimp [a]; linarith
  let g (n : ℕ) := 1/((n:ℝ)+1)^a
  have summ : Summable g := ((Real.summable_one_div_nat_add_rpow 1 a).mpr ha).congr fun n => by
    dsimp [g]
    rw [abs_of_nonneg (by positivity)]
  let Z := ∑' n, g n
  have nz : 0 ≤ Z := tsum_nonneg fun n => by dsimp [g]; positivity
  let c := 1/(1+Z+1)
  have pc : 0 < c := by dsimp [c]; positivity
  have sc : c ≤ 1 := by dsimp [c]; apply div_le_one_of_le₀ <;> linarith
  choose f hf using step ha.le pc sc
  let K := 40/c+2
  have pk : 0 < K := by dsimp [K]; positivity
  have eq : a+2 = 3+δ := by dsimp [a]; ring
  have bounds (n : ℕ) : K*((n:ℝ)+2)^(3+δ) ≤ f n ∧ (f n:ℝ) < K*((n:ℝ)+3)^(3+δ) := by
    rw [←eq]; exact ⟨(hf n).1,(hf n).2.1⟩
  refine ⟨f,K,?_,pk,bounds,?_,?_,?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    have h := (bounds (n+1)).1
    push_cast at h
    rw [show (n:ℝ)+1+2=n+3 by ring] at h
    exact_mod_cast (bounds n).2.trans_le h
  · intro n
    have := (bounds n).1
    exact_mod_cast (show (0:ℝ) < f n from (by positivity : 0 < K*((n:ℝ)+2)^(3+δ)).trans_le this)
  · apply strictAnti_nat_of_succ_lt
    intro n
    have h := (hf (n+1)).2.2.2
    push_cast at h
    rw [show (n:ℝ)+1+1=n+2 by ring] at h
    exact h.trans (hf n).2.2.1
  · intro V
    have b := summ.sum_le_tsum V (fun n _ => by dsimp [g]; positivity)
    calc
      _ ≤ ∑ n ∈ V, c*g n := sum_le_sum fun n _ => by
        simpa [g,div_eq_mul_inv] using (hf n).2.2.2.le
      _ = c * ∑ n ∈ V, g n := (mul_sum ..).symm
      _ ≤ c*Z := mul_le_mul_of_nonneg_left b pc.le
      _ < 1 := by dsimp [c]; rw [one_div_mul_eq_div]; apply (div_lt_one (by positivity)).mpr; linarith

lemma free {f : ℕ → ℕ} (hf : StrictMono f) (hp : ∀ n, 0 < f n)
    (ha : StrictAnti (fun n => Int.fract (√2*(f n:ℝ))))
    (ht : ∀ V : Finset ℕ, ∑ n ∈ V, Int.fract (√2*(f n:ℝ)) < 1) :
    IsSubsetSumFree (Set.range f) := by
  classical
  rintro _ ⟨k,rfl⟩
  refine ⟨hp k,?_⟩
  rintro ⟨T,hT,eq⟩
  let V := T.preimage f hf.injective.injOn
  have image : V.image f = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact mem_preimage.mp hi
    · intro hx
      obtain ⟨i,rfl⟩ := (hT hx).1
      exact mem_image.mpr ⟨i,mem_preimage.mpr hx,rfl⟩
  have es : f k = ∑ i ∈ V, f i := by
    rw [←image, sum_image (fun _ _ _ _ e => hf.injective e)] at eq
    exact eq
  have ne : V.Nonempty := by
    by_contra! H
    simp [H] at es
    exact (hp k).ne' es
  obtain ⟨i,hi⟩ := ne
  have ik : i < k := hf.lt_iff_lt.mp (hT (mem_preimage.mp hi)).2
  let F (n : ℕ) := √2*(f n:ℝ)
  have es' : F k = ∑ j ∈ V, F j := by
    dsimp [F]
    rw [←mul_sum]
    exact congrArg (√2 * ·) (by exact_mod_cast es)
  let z : ℤ := ∑ j ∈ V, ⌊F j⌋
  have split : F k = (z:ℝ) + ∑ j ∈ V, Int.fract (F j) := by
    rw [es']
    dsimp [z]
    push_cast
    rw [←sum_add_distrib]
    simp [Int.floor_add_fract]
  have fs : Int.fract (F k) = ∑ j ∈ V, Int.fract (F j) := by
    rw [split,Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨sum_nonneg fun _ _ => Int.fract_nonneg _,ht V⟩
  have lb := single_le_sum (fun j (_ : j ∈ V) => Int.fract_nonneg (F j)) hi
  rw [← fs] at lb
  exact (ha ik).not_ge lb

lemma nth_range {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : Nat.nth (· ∈ Set.range f) n = f n := by
  have infinite := Set.infinite_range_of_injective hf.injective
  have h := Nat.nth_comp_of_strictMono (n:=n) (p:=fun x => x ∈ Set.range f) hf
    (fun _ hh => hh) (fun finite => (infinite finite).elim)
  have eq : (fun i => f i ∈ Set.range f) = (fun _ : ℕ => True) := by funext; simp
  simpa [eq] using h.symm

lemma ratio : ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      Tendsto (fun k : ℕ => (Nat.nth (· ∈ A) (k+1) : ℝ)/(Nat.nth (· ∈ A) k:ℝ)) atTop (𝓝 1) := by
  obtain ⟨f,K,hf,hK,bounds,hp,ha,ht⟩ := constructed 1 (by norm_num)
  refine ⟨Set.range f,Set.infinite_range_of_injective hf.injective,free hf hp ha ht,?_⟩
  simp only [nth_range hf]
  have B (n : ℕ) : K*((n:ℝ)+2)^4 ≤ f n ∧ (f n:ℝ) < K*((n:ℝ)+3)^4 := by
    convert bounds n using 1 <;> norm_num
  have top : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have t : Tendsto (fun n : ℕ => 1 + 2/((n:ℝ)+2)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add ((tendsto_const_nhds (x:=(2:ℝ))).div_atTop top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using t.pow 4)
  · exact .of_forall fun n => (one_le_div (by exact_mod_cast hp n)).mpr (by exact_mod_cast hf.monotone (Nat.le_succ n))
  · refine .of_forall fun n => ?_
    have u := (B (n+1)).2.le
    push_cast at u
    rw [show (n:ℝ)+1+3=n+4 by ring] at u
    calc
      _ ≤ (K*((n:ℝ)+4)^4)/(K*((n:ℝ)+2)^4) := div_le_div₀ (by positivity) u (by positivity) (B n).1
      _ = _ := by field_simp; ring

end
end OMA.SumFreeConstruction

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.dem_ratio :=
  OMA.SumFreeConstruction.ratio
