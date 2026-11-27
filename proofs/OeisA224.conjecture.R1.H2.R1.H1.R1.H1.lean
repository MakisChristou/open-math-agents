import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H1_R1

/-! For two distinct odd prime bases, the closed square-count formula
confines the putative quotient (n²−1)/(a(n)(a(n)−1)) to short intervals.
A square quotient is excluded by the gap between consecutive squares.
The finite certificates below cover the prime and exponent ranges. -/

open Finset OeisA224
namespace OMA.ResiduePairs
open OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1

def grid : ℕ := 10^12

structure Band where
  lo : ℕ
  hi : ℕ
  amin : ℕ
  num : ℕ
  den : ℕ

structure Cell where
  el : ℕ
  eh : ℕ
  b : Band

def core (p : ℕ) : ℚ := p / (2*((p:ℚ)+1))
def single (p : ℕ) : ℚ := ((p:ℚ)+1)/(2*p)
def sizeAt (p e : ℕ) := (p^(e+1) + (if Even e then p+2 else 2*p+1))/(2*(p+1))

lemma core_mono {p q : ℕ} (h : p≤q) : core p≤core q := by
  unfold core
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h' : (p:ℚ)≤q := by exact_mod_cast h
  linarith
lemma core_half (p : ℕ) : core p ≤ 1/2 := by
  unfold core
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith
lemma single_anti {p q : ℕ} (hp : 0<p) (h : p≤q) : single q ≤ single p := by
  have hq : 0<q := by omega
  unfold single
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h' : (p:ℚ)≤q := by exact_mod_cast h
  linarith
lemma single_half {p : ℕ} (hp : 0<p) : 1/2 ≤ single p := by
  unfold single
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

lemma formula {p : ℕ} (hp : p.Prime) (ho : Odd p) (e : ℕ) :
    2*(p+1)*a (p^e) = p*p^e + (if Even e then p+2 else 2*p+1) := by
  have hf := count_formula p hp ho e
  have ha : 1 ≤ a (p^e) := by
    rw [a,if_neg (pow_ne_zero _ hp.ne_zero),Finset.one_le_card]
    exact ⟨0,mem_image.mpr ⟨0,mem_range.mpr (pow_pos hp.pos e),by simp⟩⟩
  have h := congrArg (2*(p+1)*·) (Nat.sub_add_cancel ha)
  rw [pow_succ'] at hf
  by_cases hh : Even e <;> simp only [hh,if_true,if_false] at * <;> nlinarith only [hf,h]

lemma size_eq {p : ℕ} (hp : p.Prime) (ho : Odd p) (e : ℕ) : a (p^e) = sizeAt p e := by
  rw [sizeAt,pow_succ',←formula hp ho e,Nat.mul_div_cancel_left _ (by positivity)]

def lowQ (pl ph el eh : ℕ) : ℚ :=
  if el=1 ∧ eh=1 then (if ph=0 then 1/2 else single ph) else core pl

def highQ (pl ph el : ℕ) : ℚ :=
  min (single pl) ((if ph=0 then 1/2 else core ph) + 1/(pl^el : ℕ))

/-- Certification of a prime and exponent interval. An upper endpoint of zero is unbounded. -/
def validCell (pl ph : ℕ) (c : Cell) : Bool :=
  if pl=ph ∧ c.el=c.eh then
    let N := pl^c.el
    let A := sizeAt pl c.el
    decide (c.b.num=N ∧ c.b.den=A ∧ c.b.amin≤A ∧ c.b.lo*N≤grid*A ∧ grid*A≤c.b.hi*N)
  else decide (c.b.num=0 ∧ c.b.amin≤pl^c.el/4 ∧
    (c.b.lo:ℚ)≤grid*lowQ pl ph c.el c.eh ∧ (grid:ℚ)*highQ pl ph c.el≤c.b.hi)

def Fits (b : Band) (N A : ℕ) := b.lo*N ≤ grid*A ∧ grid*A ≤ b.hi*N ∧
  b.amin≤A ∧ (b.num≠0 → N=b.num ∧ A=b.den)

lemma cell_sound {p e pl ph : ℕ} {c : Cell} (hp : p.Prime) (ho : Odd p)
    (hpl : 0<pl) (hl : pl≤p) (hh : ph=0 ∨ p≤ph) (hel : 0<c.el)
    (he : c.el≤e) (heh : c.eh=0 ∨ e≤c.eh) (hv : validCell pl ph c = true) :
    Fits c.b (p^e) (a (p^e)) := by
  unfold validCell at hv
  split_ifs at hv with hx
  · simp only [decide_eq_true_eq] at hv
    have hpe : pl=p := by omega
    have hee : c.el=e := by omega
    rw [hpe,hee] at hv
    rw [size_eq hp ho e]
    exact ⟨hv.2.2.2.1,hv.2.2.2.2,hv.2.2.1,fun _ => ⟨hv.1.symm,hv.2.1.symm⟩⟩
  · simp only [decide_eq_true_eq] at hv
    let N := p^e
    let A := a N
    let D := if Even e then p+2 else 2*p+1
    have hp' : 0<(p:ℚ) := by exact_mod_cast hp.pos
    have hN : 0<N := pow_pos hp.pos _
    have hN' : 0<(N:ℚ) := by exact_mod_cast hN
    have hP : pl^c.el ≤ N := (Nat.pow_le_pow_left hl _).trans (Nat.pow_le_pow_right hp.pos he)
    have hpN : p≤N := Nat.le_pow (by omega)
    have hd : D ≤ 2*p+1 := by dsimp [D]; split <;> have := hp.pos <;> omega
    have hf : 2*(p+1)*A = p*N+D := formula hp ho e
    have fq : 2*((p:ℚ)+1)*A = p*N+D := by exact_mod_cast hf
    have hd' : (D:ℚ) ≤ 2*p+1 := by exact_mod_cast hd
    have hpN' : (p:ℚ) ≤ N := by exact_mod_cast hpN
    have hP' : (pl^c.el:ℕ) ≤ (N:ℚ) := by exact_mod_cast hP
    have hcore : core p ≤ (A:ℚ)/N := by
      unfold core
      rw [div_le_div_iff₀ (by positivity) hN']
      nlinarith [Nat.cast_nonneg (α := ℚ) D]
    have hs : (A:ℚ)/N ≤ single p := by
      unfold single
      rw [div_le_div_iff₀ hN' (by positivity)]
      apply (mul_le_mul_iff_right₀ (show 0<(p:ℚ)+1 by positivity)).mp
      nlinarith only [congrArg (· * (p:ℚ)) fq,
        mul_le_mul_of_nonneg_right hd' hp'.le,mul_le_mul_of_nonneg_left hpN' (by positivity : (0:ℚ)≤2*p+1)]
    have single_eq (heq : e=1) : (A:ℚ)/N=single p := by
      dsimp [A,N]
      rw [heq,pow_one,OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp (by
        rintro rfl; norm_num at ho)]
      have hodd := Nat.odd_iff.mp ho
      unfold single
      have hdv : (p+1)/2*2=p+1 := by omega
      have hdv' : (((p+1)/2:ℕ):ℚ)*2=(p:ℚ)+1 := by exact_mod_cast hdv
      field_simp
      nlinarith [congrArg (· *(p:ℚ)) hdv']
    have hlow : lowQ pl ph c.el c.eh ≤ (A:ℚ)/N := by
      unfold lowQ
      split_ifs with h hph
      · rw [single_eq (by omega)]
        exact single_half hp.pos
      · rw [single_eq (by omega)]
        exact single_anti hp.pos (hh.resolve_left hph)
      · exact (core_mono hl).trans hcore
    have hcorrection : (A:ℚ)/N ≤ core p+1/N := by
      unfold core
      field_simp
      nlinarith only [fq,hd']
    have hhigh : (A:ℚ)/N ≤ highQ pl ph c.el := by
      apply le_min (hs.trans (single_anti hpl hl))
      refine hcorrection.trans (add_le_add ?_ ?_)
      · split_ifs with h
        · exact core_half p
        · exact core_mono (hh.resolve_left h)
      · exact one_div_le_one_div_of_le (by positivity) hP'
    have hamin : c.b.amin ≤ A := by
      have hfrac : 1/4 ≤ core p := by
        unfold core
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have hh : (1:ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
        linarith
      have hb := (le_div_iff₀ hN').mp (hfrac.trans hcore)
      have : N ≤ 4*A := by exact_mod_cast (show (N:ℚ) ≤ 4*A by linarith)
      omega
    have hL := hv.2.2.1.trans (mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℚ)≤grid))
    have hH := (mul_le_mul_of_nonneg_left hhigh (by positivity : (0:ℚ)≤grid)).trans hv.2.2.2
    rw [←mul_div_assoc,le_div_iff₀ hN'] at hL
    rw [←mul_div_assoc,div_le_iff₀ hN'] at hH
    exact ⟨by exact_mod_cast hL,by exact_mod_cast hH,hamin,by simp [hv.1]⟩

lemma non_square_quotient {n A s : ℕ} (hs : 3 ≤ s) (ha : s≤A) :
    n^2 ≠ s^2*(A*(A-1))+1 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : A≠0)
  simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
  intro he
  let T := s*(2*a+1)
  have hgap : (2*n)^2+s^2 = T^2+4 := by dsimp [T]; nlinarith only [he]
  have hT : s^2 ≤ T := by
    dsimp [T]
    rw [sq]
    exact Nat.mul_le_mul_left _ (by omega)
  rcases le_or_gt T (2*n) with h|h
  · nlinarith [Nat.pow_le_pow_left h 2,Nat.mul_le_mul hs hs]
  · have hh := Nat.mul_le_mul_right (T+2*n) (show 2*n+1≤T by omega)
    nlinarith only [hgap,hT,hh,Nat.zero_le n]

lemma quotient_bounds {N A k l h a : ℕ} (hN : 2≤N) (hl : 0<l) (hh : 0<h)
    (hmin : 2≤a) (hA : a≤A)
    (hlo : l*N≤grid^2*A) (hhi : grid^2*A≤h*N) (he : N^2=k*(A*(A-1))+1) :
    grid^4/h^2 < k ∧ k ≤ grid^4*a/(l^2*(a-1)) := by
  have hAp : 0<A := by omega
  have hp : 0<k := by
    by_contra! hz
    have := Nat.pow_le_pow_left hN 2
    simp [show k=0 by omega] at he
    norm_num at this
    omega
  have hAA : A-1+1=A := by omega
  have he' : N^2+k*A=k*A^2+1 := by
    nlinarith only [he,congrArg (fun t => k*A*t) hAA]
  have hg : N^2 < k*A^2 := by
    have h2 := Nat.mul_le_mul (show 1≤k by omega) (show 2≤A by omega)
    omega
  constructor
  · apply (Nat.div_lt_iff_lt_mul (pow_pos hh 2)).mpr
    apply Nat.lt_of_mul_lt_mul_right (a := A^2)
    have h1 := Nat.pow_le_pow_left hhi 2
    have h2 := Nat.mul_lt_mul_of_pos_left hg (pow_pos hh 2)
    nlinarith only [h1,h2]
  · apply (Nat.le_div_iff_mul_le (Nat.mul_pos (pow_pos hl 2) (by omega))).mpr
    have hn : k*(A*(A-1)) ≤ N^2 := by omega
    have h1 := Nat.pow_le_pow_left hlo 2
    have h2 := Nat.mul_le_mul_left (l^2) hn
    have h3 : k*l^2*(A-1) ≤ grid^4*A := by
      apply Nat.le_of_mul_le_mul_right (c := A) _ hAp
      nlinarith only [h1,h2]
    have h4 : A*(a-1) ≤ a*(A-1) := by
      nlinarith only [hA,congrArg (a*·) hAA,congrArg (A*·) (show a-1+1=a by omega)]
    apply Nat.le_of_mul_le_mul_right (c := A) _ hAp
    nlinarith only [Nat.mul_le_mul_left (k*l^2) h4,Nat.mul_le_mul_left a h3]

def pairOK (x y : Cell) : Bool :=
  if x.eh=1 ∧ y.eh=1 then true
  else if x.b.num≠0 ∧ y.b.num≠0 then
    decide (¬(x.b.num*y.b.num)^2 ≡ 1 [MOD (x.b.den*y.b.den)*(x.b.den*y.b.den-1)])
  else
    let l := x.b.lo*y.b.lo
    let h := x.b.hi*y.b.hi
    let a := x.b.amin*y.b.amin
    let low := grid^4/h^2+1
    let high := grid^4*a/(l^2*(a-1))
    decide (0<l ∧ 0<h ∧ 2≤a) && (List.range (high+1-low)).all fun i =>
      let k := low+i
      decide (k.sqrt^2=k ∧ 3≤k.sqrt ∧ k.sqrt≤a)

lemma pair_sound {x y : Cell} {P Q X Y : ℕ} (hx : Fits x.b P X) (hy : Fits y.b Q Y)
    (hn : 2≤P*Q) (he : ¬(x.eh=1 ∧ y.eh=1)) (hok : pairOK x y=true) :
    ¬(P*Q)^2 ≡ 1 [MOD (X*Y)*(X*Y-1)] := by
  intro htest
  unfold pairOK at hok
  rw [if_neg he] at hok
  split_ifs at hok with exacts
  · have h1 := hx.2.2.2 exacts.1
    have h2 := hy.2.2.2 exacts.2
    rw [decide_eq_true_eq] at hok
    exact hok (by simpa only [←h1.1,←h1.2,←h2.1,←h2.2] using htest)
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hok
    obtain ⟨⟨hl,hh,hm⟩,hc⟩ := hok
    let N := P*Q
    let A := X*Y
    let l := x.b.lo*y.b.lo
    let h := x.b.hi*y.b.hi
    let a := x.b.amin*y.b.amin
    have hlo : l*N≤grid^2*A := by dsimp [l,N,A]; nlinarith only [Nat.mul_le_mul hx.1 hy.1]
    have hhi : grid^2*A≤h*N := by dsimp [h,N,A]; nlinarith only [Nat.mul_le_mul hx.2.1 hy.2.1]
    have hA : a≤A := Nat.mul_le_mul hx.2.2.1 hy.2.2.1
    have hN : 1≤N^2 := Nat.one_le_pow _ _ (by omega : 0<N)
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hN).mp htest.symm
    change N^2-1=(A*(A-1))*k at hk
    have heq : N^2=k*(A*(A-1))+1 := by rw [Nat.mul_comm k]; omega
    obtain ⟨kl,ku⟩ := quotient_bounds hn hl hh hm hA hlo hhi heq
    let low := grid^4/h^2+1
    let high := grid^4*a/(l^2*(a-1))
    have hkl : low≤k := kl
    have hku : k≤high := ku
    have hs := List.all_eq_true.mp hc (k-low) (by
      apply List.mem_range.mpr
      change k-low < high+1-low
      omega)
    change decide ((low+(k-low)).sqrt^2=low+(k-low) ∧ 3≤(low+(k-low)).sqrt ∧ (low+(k-low)).sqrt≤a) = true at hs
    rw [Nat.add_sub_of_le hkl,decide_eq_true_eq] at hs
    exact non_square_quotient hs.2.1 (hs.2.2.trans hA) (by simpa only [hs.1] using heq)

structure Row where
  pl : ℕ
  ph : ℕ
  cells : List Cell

def coverCells (pl ph : ℕ) : List Cell → ℕ → Bool
  | [], _ => false
  | c::cs, first => decide (c.el=first) && validCell pl ph c &&
      (decide (c.eh=0) || coverCells pl ph cs (c.eh+1))

lemma chooseCell {pl ph first e : ℕ} {cs : List Cell} (h : coverCells pl ph cs first=true)
    (hpos : 0<first) (he : first≤e) :
    ∃ c ∈ cs, 0<c.el ∧ c.el≤e ∧ (c.eh=0 ∨ e≤c.eh) ∧ validCell pl ph c=true := by
  induction cs generalizing first with
  | nil => simp [coverCells] at h
  | cons c cs ih =>
    simp only [coverCells,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
    by_cases ht : c.eh=0 ∨ e≤c.eh
    · exact ⟨c,by simp,by omega,by omega,ht,h.1.2⟩
    · obtain ⟨x,hx,hr⟩ := ih (h.2.resolve_left (by omega)) (by omega) (by omega)
      exact ⟨x,by simp [hx],hr⟩

def rowOK (r : Row) : Bool :=
  if r.cells.isEmpty then
    decide (r.ph≠0) && (List.range (r.ph+1-r.pl)).all (fun i => decide (¬(r.pl+i).Prime))
  else coverCells r.pl r.ph r.cells 1

def coverRows (stop : ℕ) : List Row → ℕ → Bool
  | [], _ => false
  | r::rs, first => decide (r.pl=first) && rowOK r &&
      (decide (r.ph=0 ∨ (stop≠0 ∧ stop≤r.ph)) || coverRows stop rs (r.ph+1))

lemma chooseRow {start stop p : ℕ} {rs : List Row} (h : coverRows stop rs start = true)
    (hp : p.Prime) (hpos : 0<start) (hl : start≤p) (hu : stop=0 ∨ p ≤ stop) :
    ∃ r ∈ rs, 0<r.pl ∧ r.pl≤p ∧ (r.ph=0 ∨ p≤r.ph) ∧ coverCells r.pl r.ph r.cells 1=true := by
  induction rs generalizing start with
  | nil => simp [coverRows] at h
  | cons r rs ih =>
    simp only [coverRows,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
    by_cases hbound : r.ph=0 ∨ p≤r.ph
    · refine ⟨r,by simp,by omega,by omega,hbound,?_⟩
      have hr := h.1.2
      unfold rowOK at hr
      split_ifs at hr with ht
      · simp only [Bool.and_eq_true,decide_eq_true_eq] at hr
        have hh := List.all_eq_true.mp hr.2 (p-r.pl) (List.mem_range.mpr (by omega))
        have hp' : r.pl+(p-r.pl)=p := by omega
        simp [hp',hp] at hh
      · exact hr
    · obtain ⟨x,hx,hh⟩ := ih (h.2.resolve_left (by omega)) (by omega) (by omega)
      exact ⟨x,by simp [hx],hh⟩

def rowPair (r s : Row) : Bool :=
  decide (s.ph≠0 ∧ s.ph≤r.pl) || r.cells.all (fun x => s.cells.all (pairOK x))

lemma region {ps qs : List Row} {lp up lq uq : ℕ}
    (hps : coverRows up ps lp = true) (hqs : coverRows uq qs lq = true)
    (ht : ∀ r ∈ ps, ∀ s ∈ qs, rowPair r s=true)
    {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hop : Odd p) (hoq : Odd q)
    (hpq : p<q) (hp0 : 0<lp) (hq0 : 0<lq) (hpl : lp≤p) (hph : up=0 ∨ p≤up)
    (hql : lq≤q) (hqh : uq=0 ∨ q≤uq) (he : 0<e) (hf : 0<f) (hsum : 3≤e+f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  obtain ⟨r,hr,hpr,hl,hh,hcs⟩ := chooseRow hps hp hp0 hpl hph
  obtain ⟨s,hs,hps',hl',hh',hcs'⟩ := chooseRow hqs hq hq0 hql hqh
  obtain ⟨x,hx,hel,he1,he2,hv⟩ := chooseCell hcs (by decide) he
  obtain ⟨y,hy,hfl,hf1,hf2,hv'⟩ := chooseCell hcs' (by decide) hf
  have hb := ht r hr s hs
  simp only [rowPair,Bool.or_eq_true,decide_eq_true_eq] at hb
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp (hb.resolve_left (by omega)) x hx) y hy
  have hc := (Nat.coprime_primes hp hq).mpr hpq.ne
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _)
    ((hc.pow_left _).pow_right _)]
  apply pair_sound (cell_sound hp hop hpr hl hh hel he1 he2 hv) (cell_sound hq hoq hps' hl' hh' hfl hf1 hf2 hv') _ (by omega) hpair
  exact hp.two_le.trans ((Nat.le_pow he).trans (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _)))

private def small1 : List Row := [
  ⟨3,3,[⟨1,1,⟨666666666666,666666666667,2,3,2⟩⟩,⟨2,2,⟨444444444444,444444444445,4,9,4⟩⟩,⟨3,3,⟨407407407407,407407407408,11,27,11⟩⟩,⟨4,4,⟨382716049382,382716049383,31,81,31⟩⟩,⟨5,5,⟨378600823045,378600823046,92,243,92⟩⟩,⟨6,6,⟨375857338820,375857338821,274,729,274⟩⟩,⟨7,7,⟨375400091449,375400091450,821,2187,821⟩⟩,⟨8,8,⟨375095259868,375095259869,2461,6561,2461⟩⟩,⟨9,9,⟨375044454605,375044454606,7382,19683,7382⟩⟩,⟨10,10,⟨375010584429,375010584430,22144,59049,22144⟩⟩,⟨11,11,⟨375004939400,375004939401,66431,177147,66431⟩⟩,⟨12,12,⟨375001176047,375001176048,199291,531441,199291⟩⟩,⟨13,13,⟨375000548822,375000548823,597872,1594323,597872⟩⟩,⟨14,14,⟨375000130671,375000130672,1793614,4782969,1793614⟩⟩,⟨15,15,⟨375000060980,375000060981,5380841,14348907,5380841⟩⟩,⟨16,16,⟨375000014519,375000014520,16142521,43046721,16142521⟩⟩,⟨17,0,⟨375000000000,375000007744,32285040,0,0⟩⟩]⟩,
  ⟨4,4,[]⟩,
  ⟨5,5,[⟨1,1,⟨600000000000,600000000000,3,5,3⟩⟩,⟨2,2,⟨440000000000,440000000000,11,25,11⟩⟩,⟨3,3,⟨424000000000,424000000000,53,125,53⟩⟩,⟨4,4,⟨417600000000,417600000000,261,625,261⟩⟩,⟨5,5,⟨416960000000,416960000000,1303,3125,1303⟩⟩,⟨6,6,⟨416704000000,416704000000,6511,15625,6511⟩⟩,⟨7,7,⟨416678400000,416678400000,32553,78125,32553⟩⟩,⟨8,8,⟨416668160000,416668160000,162761,390625,162761⟩⟩,⟨9,9,⟨416667136000,416667136000,813803,1953125,813803⟩⟩,⟨10,10,⟨416666726400,416666726400,4069011,9765625,4069011⟩⟩,⟨11,11,⟨416666685440,416666685440,20345053,48828125,20345053⟩⟩,⟨12,0,⟨416666666666,416666670763,61035156,0,0⟩⟩]⟩,
  ⟨6,6,[]⟩]

private def small2 : List Row := [
  ⟨7,7,[⟨1,1,⟨571428571428,571428571429,4,7,4⟩⟩,⟨2,2,⟨448979591836,448979591837,22,49,22⟩⟩,⟨3,3,⟨440233236151,440233236152,151,343,151⟩⟩,⟨4,4,⟨437734277384,437734277385,1051,2401,1051⟩⟩,⟨5,5,⟨437555780329,437555780330,7354,16807,7354⟩⟩,⟨6,6,⟨437504781171,437504781172,51472,117649,51472⟩⟩,⟨7,7,⟨437501138374,437501138375,360301,823543,360301⟩⟩,⟨8,8,⟨437500097574,437500097575,2522101,5764801,2522101⟩⟩,⟨9,9,⟨437500023232,437500023233,17654704,40353607,17654704⟩⟩,⟨10,0,⟨437500000000,437500003541,70618812,0,0⟩⟩]⟩,
  ⟨8,10,[]⟩,
  ⟨11,11,[⟨1,1,⟨545454545454,545454545455,6,11,6⟩⟩,⟨2,2,⟨462809917355,462809917356,56,121,56⟩⟩,⟨3,3,⟨459053343350,459053343351,611,1331,611⟩⟩,⟨4,4,⟨458370329895,458370329896,6711,14641,6711⟩⟩,⟨5,5,⟨458339283829,458339283830,73816,161051,73816⟩⟩,⟨6,6,⟨458333639090,458333639091,811966,1771561,811966⟩⟩,⟨7,7,⟨458333382510,458333382511,8931621,19487171,8931621⟩⟩,⟨8,0,⟨458333333333,458333337999,53589720,0,0⟩⟩]⟩,
  ⟨12,12,[]⟩]

private def small3 : List Row := [
  ⟨13,13,[⟨1,1,⟨538461538461,538461538462,7,13,7⟩⟩,⟨2,2,⟨467455621301,467455621302,79,169,79⟩⟩,⟨3,3,⟨464724624487,464724624488,1021,2197,1021⟩⟩,⟨4,4,⟨464304471131,464304471132,13261,28561,13261⟩⟩,⟨5,5,⟨464288311387,464288311388,172387,371293,172387⟩⟩,⟨6,6,⟨464285825272,464285825273,2241019,4826809,2241019⟩⟩,⟨7,7,⟨464285729653,464285729654,29133241,62748517,29133241⟩⟩,⟨8,0,⟨464285714285,464285715512,203932680,0,0⟩⟩]⟩,
  ⟨14,16,[]⟩,
  ⟨17,17,[⟨1,1,⟨529411764705,529411764706,9,17,9⟩⟩,⟨2,2,⟨474048442906,474048442907,137,289,137⟩⟩,⟨3,3,⟨472420109912,472420109913,2321,4913,2321⟩⟩,⟨4,4,⟨472228541324,472228541325,39441,83521,39441⟩⟩,⟨5,5,⟨472222906954,472222906955,670489,1419857,670489⟩⟩,⟨6,6,⟨472222244087,472222244088,11398297,24137569,11398297⟩⟩,⟨7,0,⟨472222222222,472222224660,102584668,0,0⟩⟩]⟩,
  ⟨18,18,[]⟩]

private def small4 : List Row := [
  ⟨19,19,[⟨1,1,⟨526315789473,526315789474,10,19,10⟩⟩,⟨2,2,⟨476454293628,476454293629,172,361,172⟩⟩,⟨3,3,⟨475142149001,475142149002,3259,6859,3259⟩⟩,⟨4,4,⟨475004028514,475004028515,61903,130321,61903⟩⟩,⟨5,5,⟨475000393764,475000393765,1176148,2476099,1176148⟩⟩,⟨6,6,⟨475000011159,475000011160,22346794,47045881,22346794⟩⟩,⟨7,0,⟨475000000000,475000001119,223467934,0,0⟩⟩]⟩,
  ⟨20,22,[]⟩,
  ⟨23,23,[⟨1,1,⟨521739130434,521739130435,12,23,12⟩⟩,⟨2,2,⟨480151228733,480151228734,254,529,254⟩⟩,⟨3,3,⟨479247143913,479247143914,5831,12167,5831⟩⟩,⟨4,4,⟨479168527842,479168527843,134091,279841,134091⟩⟩,⟨5,5,⟨479166818797,479166818798,3084082,6436343,3084082⟩⟩,⟨6,0,⟨479166666666,479166673422,37008972,0,0⟩⟩]⟩,
  ⟨24,28,[]⟩]

private def small5 : List Row := [
  ⟨29,29,[⟨1,1,⟨517241379310,517241379311,15,29,15⟩⟩,⟨2,2,⟨483947681331,483947681332,407,841,407⟩⟩,⟨3,3,⟨483373652056,483373652057,11789,24389,11789⟩⟩,⟨4,4,⟨483334063830,483334063831,341853,707281,341853⟩⟩,⟨5,5,⟨483333381274,483333381275,9913723,20511149,9913723⟩⟩,⟨6,0,⟨483333333333,483333335015,148705830,0,0⟩⟩]⟩,
  ⟨30,30,[]⟩,
  ⟨31,31,[⟨1,1,⟨516129032258,516129032259,16,31,16⟩⟩,⟨2,2,⟨484911550468,484911550469,466,961,466⟩⟩,⟨3,3,⟨484408042697,484408042698,14431,29791,14431⟩⟩,⟨4,4,⟨484375558325,484375558326,447331,923521,447331⟩⟩,⟨5,5,⟨484375034383,484375034384,13867246,28629151,13867246⟩⟩,⟨6,0,⟨484375000000,484375001127,221875920,0,0⟩⟩]⟩,
  ⟨32,36,[]⟩]

private def small6 : List Row := [
  ⟨37,37,[⟨1,1,⟨513513513513,513513513514,19,37,19⟩⟩,⟨2,2,⟨487216946676,487216946677,667,1369,667⟩⟩,⟨3,3,⟨486861587665,486861587666,24661,50653,24661⟩⟩,⟨4,4,⟨486842379069,486842379070,912421,1874161,912421⟩⟩,⟨5,5,⟨486842119494,486842119495,33759559,69343957,33759559⟩⟩,⟨6,0,⟨486842105263,486842105653,641431602,0,0⟩⟩]⟩,
  ⟨38,40,[]⟩,
  ⟨41,41,[⟨1,1,⟨512195121951,512195121952,21,41,21⟩⟩,⟨2,2,⟨488399762046,488399762047,821,1681,821⟩⟩,⟨3,3,⟨488109574730,488109574731,33641,68921,33641⟩⟩,⟨4,4,⟨488095419251,488095419252,1379241,2825761,1379241⟩⟩,⟨5,0,⟨488095238095,488095246727,28964050,0,0⟩⟩]⟩,
  ⟨42,42,[]⟩]

private def small7 : List Row := [
  ⟨43,43,[⟨1,1,⟨511627906976,511627906977,22,43,22⟩⟩,⟨2,2,⟨488912925905,488912925906,904,1849,904⟩⟩,⟨3,3,⟨488648798219,488648798220,38851,79507,38851⟩⟩,⟨4,4,⟨488636513210,488636513211,1670551,3418801,1670551⟩⟩,⟨5,0,⟨488636363636,488636370439,36752110,0,0⟩⟩]⟩,
  ⟨44,46,[]⟩,
  ⟨47,47,[⟨1,1,⟨510638297872,510638297873,24,47,24⟩⟩,⟨2,2,⟨489814395654,489814395655,1082,2209,1082⟩⟩,⟨3,3,⟨489592864779,489592864780,50831,103823,50831⟩⟩,⟨4,4,⟨489583437933,489583437934,2389011,4879681,2389011⟩⟩,⟨5,0,⟨489583333333,489583337694,57336251,0,0⟩⟩]⟩,
  ⟨48,52,[]⟩]

private def small8 : List Row := [
  ⟨53,53,[⟨1,1,⟨509433962264,509433962265,27,53,27⟩⟩,⟨2,2,⟨490922036311,490922036312,1379,2809,1379⟩⟩,⟨3,3,⟨490747395500,490747395501,73061,148877,73061⟩⟩,⟨4,4,⟨490740805281,490740805282,3872181,7890481,3872181⟩⟩,⟨5,0,⟨490740740740,490740743132,104548873,0,0⟩⟩]⟩,
  ⟨54,58,[]⟩,
  ⟨59,59,[⟨1,1,⟨508474576271,508474576272,30,59,30⟩⟩,⟨2,2,⟨491812697500,491812697501,1712,3481,1712⟩⟩,⟨3,3,⟨491671495138,491671495139,100979,205379,100979⟩⟩,⟨4,4,⟨491666708617,491666708618,5957703,12117361,5957703⟩⟩,⟨5,0,⟨491666666666,491666668066,178731074,0,0⟩⟩]⟩,
  ⟨60,60,[]⟩]

private def small9 : List Row := [
  ⟨61,61,[⟨1,1,⟨508196721311,508196721312,31,61,31⟩⟩,⟨2,2,⟨492072023649,492072023650,1831,3721,1831⟩⟩,⟨3,3,⟨491939853996,491939853997,111661,226981,111661⟩⟩,⟨4,4,⟨491935520565,491935520566,6811261,13845841,6811261⟩⟩,⟨5,0,⟨491935483870,491935485055,211149075,0,0⟩⟩]⟩,
  ⟨62,66,[]⟩,
  ⟨67,67,[⟨1,1,⟨507462686567,507462686568,34,67,34⟩⟩,⟨2,2,⟨492760080196,492760080197,2212,4489,2212⟩⟩,⟨3,3,⟨492650359252,492650359253,148171,300763,148171⟩⟩,⟨4,4,⟨492647084000,492647084001,9927391,20151121,9927391⟩⟩,⟨5,0,⟨492647058823,492647059565,337531276,0,0⟩⟩]⟩,
  ⟨68,70,[]⟩]

private def small10 : List Row := [
  ⟨71,71,[⟨1,1,⟨507042253521,507042253522,36,71,36⟩⟩,⟨2,2,⟨493156119817,493156119818,2486,5041,2486⟩⟩,⟨3,3,⟨493058330143,493058330144,176471,357911,176471⟩⟩,⟨4,4,⟨493055575504,493055575505,12529371,25411681,12529371⟩⟩,⟨5,0,⟨493055555555,493055556110,451057337,0,0⟩⟩]⟩,
  ⟨72,72,[]⟩,
  ⟨73,73,[⟨1,1,⟨506849315068,506849315069,37,73,37⟩⟩,⟨2,2,⟨493338337399,493338337400,2629,5329,2629⟩⟩,⟨3,3,⟨493245796456,493245796457,191881,389017,191881⟩⟩,⟨4,4,⟨493243261087,493243261088,14007241,28398241,14007241⟩⟩,⟨5,0,⟨493243243243,493243243726,518267898,0,0⟩⟩]⟩,
  ⟨74,78,[]⟩]

private def small11 : List Row := [
  ⟨79,79,[⟨1,1,⟨506329113924,506329113925,40,79,40⟩⟩,⟨2,2,⟨493831116808,493831116809,3082,6241,3082⟩⟩,⟨3,3,⟨493752015560,493752015561,243439,493039,243439⟩⟩,⟨4,4,⟨493750012997,493750012998,19231603,38950081,19231603⟩⟩,⟨5,0,⟨493750000000,493750000325,769264099,0,0⟩⟩]⟩,
  ⟨80,82,[]⟩,
  ⟨83,83,[⟨1,1,⟨506024096385,506024096386,42,83,42⟩⟩,⟨2,2,⟨494121062563,494121062564,3404,6889,3404⟩⟩,⟨3,3,⟨494049357540,494049357541,282491,571787,282491⟩⟩,⟨4,4,⟨494047629708,494047629709,23446671,47458321,23446671⟩⟩,⟨5,0,⟨494047619047,494047619302,984760160,0,0⟩⟩]⟩,
  ⟨84,88,[]⟩]

private def small12 : List Row := [
  ⟨89,89,[⟨1,1,⟨505617977528,505617977529,45,89,45⟩⟩,⟨2,2,⟨494508269157,494508269158,3917,7921,3917⟩⟩,⟨3,3,⟨494445855065,494445855066,348569,704969,348569⟩⟩,⟨4,4,⟨494444452502,494444452503,31022553,62742241,31022553⟩⟩,⟨5,0,⟨494444444444,494444444624,1396014862,0,0⟩⟩]⟩,
  ⟨90,96,[]⟩,
  ⟨97,97,[⟨1,1,⟨505154639175,505154639176,49,97,49⟩⟩,⟨2,2,⟨494951642044,494951642045,4657,9409,4657⟩⟩,⟨3,3,⟨494899049276,494899049277,451681,912673,451681⟩⟩,⟨4,4,⟨494897964889,494897964890,43812961,88529281,43812961⟩⟩,⟨5,0,⟨494897959183,494897959301,2146835064,0,0⟩⟩]⟩,
  ⟨98,100,[]⟩]

private def small13 : List Row := [
  ⟨101,101,[⟨1,1,⟨504950495049,504950495050,51,101,51⟩⟩,⟨2,2,⟨495147534555,495147534556,5051,10201,5051⟩⟩,⟨3,3,⟨495099005048,495099005049,510101,1030301,510101⟩⟩,⟨4,0,⟨495098039215,495098048826,26015100,0,0⟩⟩]⟩,
  ⟨102,102,[]⟩,
  ⟨103,103,[⟨1,1,⟨504854368932,504854368933,52,103,52⟩⟩,⟨2,2,⟨495239890658,495239890659,5254,10609,5254⟩⟩,⟨3,3,⟨495193218434,495193218435,541111,1092727,541111⟩⟩,⟨4,0,⟨495192307692,495192316578,28137720,0,0⟩⟩]⟩,
  ⟨104,106,[]⟩]

private def small14 : List Row := [
  ⟨107,107,[⟨1,1,⟨504672897196,504672897197,54,107,54⟩⟩,⟨2,2,⟨495414446676,495414446677,5672,11449,5672⟩⟩,⟨3,3,⟨495371182889,495371182890,606851,1225043,606851⟩⟩,⟨4,0,⟨495370370370,495370378000,32769900,0,0⟩⟩]⟩,
  ⟨108,108,[]⟩,
  ⟨109,109,[⟨1,1,⟨504587155963,504587155964,55,109,55⟩⟩,⟨2,2,⟨495497012036,495497012037,5887,11881,5887⟩⟩,⟨3,3,⟨495455314128,495455314129,641629,1295029,641629⟩⟩,⟨4,0,⟨495454545454,495454552539,35289540,0,0⟩⟩]⟩,
  ⟨110,112,[]⟩]

private def small15 : List Row := [
  ⟨113,113,[⟨1,1,⟨504424778761,504424778762,57,113,57⟩⟩,⟨2,2,⟨495653535907,495653535908,6329,12769,6329⟩⟩,⟨3,3,⟨495614725098,495614725099,715121,1442897,715121⟩⟩,⟨4,0,⟨495614035087,495614041221,40761840,0,0⟩⟩]⟩,
  ⟨114,126,[]⟩,
  ⟨127,127,[⟨1,1,⟨503937007874,503937007875,64,127,64⟩⟩,⟨2,2,⟨496124992249,496124992250,8002,16129,8002⟩⟩,⟨3,3,⟨496094236282,496094236283,1016191,2048383,1016191⟩⟩,⟨4,0,⟨496093750000,496093753845,65036160,0,0⟩⟩]⟩,
  ⟨128,130,[]⟩]

private def small16 : List Row := [
  ⟨131,131,[⟨1,1,⟨503816793893,503816793894,66,131,66⟩⟩,⟨2,2,⟨496241477769,496241477770,8516,17161,8516⟩⟩,⟨3,3,⟨496212564349,496212564350,1115531,2248091,1115531⟩⟩,⟨4,0,⟨496212121212,496212124608,73624980,0,0⟩⟩]⟩,
  ⟨132,136,[]⟩,
  ⟨137,137,[⟨1,1,⟨503649635036,503649635037,69,137,69⟩⟩,⟨2,2,⟨496403644307,496403644308,9317,18769,9317⟩⟩,⟨3,3,⟨496377199085,496377199086,1276361,2571353,1276361⟩⟩,⟨4,0,⟨496376811594,496376814433,88068840,0,0⟩⟩]⟩,
  ⟨138,138,[]⟩]

private def small17 : List Row := [
  ⟨139,139,[⟨1,1,⟨503597122302,503597122303,70,139,70⟩⟩,⟨2,2,⟨496454634853,496454634854,9592,19321,9592⟩⟩,⟨3,3,⟨496428942452,496428942453,1333219,2685619,1333219⟩⟩,⟨4,0,⟨496428571428,496428574108,93325260,0,0⟩⟩]⟩,
  ⟨140,148,[]⟩,
  ⟨149,149,[⟨1,1,⟨503355704697,503355704698,75,149,75⟩⟩,⟨2,2,⟨496689338318,496689338319,11027,22201,11027⟩⟩,⟨3,3,⟨496666967961,496666967962,1642949,3307949,1642949⟩⟩,⟨4,0,⟨496666666666,496666668696,123221100,0,0⟩⟩]⟩,
  ⟨150,150,[]⟩]

private def small18 : List Row := [
  ⟨151,151,[⟨1,1,⟨503311258278,503311258279,76,151,76⟩⟩,⟨2,2,⟨496732599447,496732599448,11326,22801,11326⟩⟩,⟨3,3,⟨496710815808,496710815809,1710151,3442951,1710151⟩⟩,⟨4,0,⟨496710526315,496710528240,129971400,0,0⟩⟩]⟩,
  ⟨152,156,[]⟩,
  ⟨157,157,[⟨1,1,⟨503184713375,503184713376,79,157,79⟩⟩,⟨2,2,⟨496855856221,496855856222,12247,24649,12247⟩⟩,⟨3,3,⟨496835700625,496835700626,1922701,3869893,1922701⟩⟩,⟨4,0,⟨496835443037,496835444684,151893300,0,0⟩⟩]⟩,
  ⟨158,162,[]⟩]

private def small19 : List Row := [
  ⟨163,163,[⟨1,1,⟨503067484662,503067484663,82,163,82⟩⟩,⟨2,2,⟨496970153186,496970153187,13204,26569,13204⟩⟩,⟨3,3,⟨496951449715,496951449716,2152171,4330747,2152171⟩⟩,⟨4,0,⟨496951219512,496951220929,176477940,0,0⟩⟩]⟩,
  ⟨164,166,[]⟩,
  ⟨167,167,[⟨1,1,⟨502994011976,502994011977,84,167,84⟩⟩,⟨2,2,⟨497041844454,497041844455,13862,27889,13862⟩⟩,⟨3,3,⟨497024023593,497024023594,2314871,4657463,2314871⟩⟩,⟨4,0,⟨497023809523,497023810810,194449080,0,0⟩⟩]⟩,
  ⟨168,172,[]⟩]

private def small20 : List Row := [
  ⟨173,173,[⟨1,1,⟨502890173410,502890173411,87,173,87⟩⟩,⟨2,2,⟨497143238998,497143238999,14879,29929,14879⟩⟩,⟨3,3,⟨497126629361,497126629362,2573981,5177717,2573981⟩⟩,⟨4,0,⟨497126436781,497126437898,223936260,0,0⟩⟩]⟩,
  ⟨174,178,[]⟩,
  ⟨179,179,[⟨1,1,⟨502793296089,502793296090,90,179,90⟩⟩,⟨2,2,⟨497237913922,497237913923,15932,32041,15932⟩⟩,⟨3,3,⟨497222396095,497222396096,2851739,5735339,2851739⟩⟩,⟨4,0,⟨497222222222,497222223197,256656420,0,0⟩⟩]⟩,
  ⟨180,180,[]⟩]

private def small21 : List Row := [
  ⟨181,181,[⟨1,1,⟨502762430939,502762430940,91,181,91⟩⟩,⟨2,2,⟨497268093159,497268093160,16291,32761,16291⟩⟩,⟨3,3,⟨497252915430,497252915431,2948581,5929741,2948581⟩⟩,⟨4,0,⟨497252747252,497252748185,268320780,0,0⟩⟩]⟩,
  ⟨182,190,[]⟩,
  ⟨191,191,[⟨1,1,⟨502617801047,502617801048,96,191,96⟩⟩,⟨2,2,⟨497409610482,497409610483,18146,36481,18146⟩⟩,⟨3,3,⟨497395976475,497395976476,3465791,6967871,3465791⟩⟩,⟨4,0,⟨497395833333,497395834085,332715840,0,0⟩⟩]⟩,
  ⟨192,192,[]⟩]

private def small22 : List Row := [
  ⟨193,193,[⟨1,1,⟨502590673575,502590673576,97,193,97⟩⟩,⟨2,2,⟨497436172783,497436172784,18529,37249,18529⟩⟩,⟨3,3,⟨497422819154,497422819155,3576001,7189057,3576001⟩⟩,⟨4,0,⟨497422680412,497422681134,346872000,0,0⟩⟩]⟩,
  ⟨194,196,[]⟩,
  ⟨197,197,[⟨1,1,⟨502538071065,502538071066,99,197,99⟩⟩,⟨2,2,⟨497487696152,497487696153,19307,38809,19307⟩⟩,⟨3,3,⟨497474877942,497474877943,3803381,7645373,3803381⟩⟩,⟨4,0,⟨497474747474,497474748139,376534620,0,0⟩⟩]⟩,
  ⟨198,198,[]⟩]

private def small23 : List Row := [
  ⟨199,199,[⟨1,1,⟨502512562814,502512562815,100,199,100⟩⟩,⟨2,2,⟨497512689073,497512689074,19702,39601,19702⟩⟩,⟨3,3,⟨497500126576,497500126577,3920599,7880599,3920599⟩⟩,⟨4,0,⟨497500000000,497500000638,392059800,0,0⟩⟩]⟩,
  ⟨200,200,[]⟩]

private def smallRows : List Row := small1 ++ small2 ++ small3 ++ small4 ++ small5 ++ small6 ++ small7 ++ small8 ++ small9 ++ small10 ++ small11 ++ small12 ++ small13 ++ small14 ++ small15 ++ small16 ++ small17 ++ small18 ++ small19 ++ small20 ++ small21 ++ small22 ++ small23

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma smallCover : coverRows 200 smallRows 3 = true := by decide +kernel

private def checkedRow (r : Row) := smallRows.all (rowPair r)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small1Checked : small1.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small2Checked : small2.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small3Checked : small3.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small4Checked : small4.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small5Checked : small5.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small6Checked : small6.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small7Checked : small7.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small8Checked : small8.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small9Checked : small9.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small10Checked : small10.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small11Checked : small11.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small12Checked : small12.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small13Checked : small13.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small14Checked : small14.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small15Checked : small15.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small16Checked : small16.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small17Checked : small17.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small18Checked : small18.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small19Checked : small19.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small20Checked : small20.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small21Checked : small21.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small22Checked : small22.all checkedRow = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma small23Checked : small23.all checkedRow = true := by decide +kernel

private lemma append_ok {xs ys : List Row} (h₁ : xs.all checkedRow = true) (h₂ : ys.all checkedRow = true) : (xs++ys).all checkedRow = true := by rw [List.all_append,h₁,h₂]; decide

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
private lemma fullCheck : smallRows.all checkedRow = true := (append_ok (xs := small1) small1Checked (append_ok (xs := small2) small2Checked (append_ok (xs := small3) small3Checked (append_ok (xs := small4) small4Checked (append_ok (xs := small5) small5Checked (append_ok (xs := small6) small6Checked (append_ok (xs := small7) small7Checked (append_ok (xs := small8) small8Checked (append_ok (xs := small9) small9Checked (append_ok (xs := small10) small10Checked (append_ok (xs := small11) small11Checked (append_ok (xs := small12) small12Checked (append_ok (xs := small13) small13Checked (append_ok (xs := small14) small14Checked (append_ok (xs := small15) small15Checked (append_ok (xs := small16) small16Checked (append_ok (xs := small17) small17Checked (append_ok (xs := small18) small18Checked (append_ok (xs := small19) small19Checked (append_ok (xs := small20) small20Checked (append_ok (xs := small21) small21Checked (append_ok (xs := small22) small22Checked small23Checked))))))))))))))))))))))

private lemma assembled : ∀ r ∈ smallRows, ∀ s ∈ smallRows, rowPair r s = true := by
  intro r hr s hs
  have h : smallRows.all (rowPair r) = true := List.all_eq_true.mp fullCheck r hr
  exact List.all_eq_true.mp h s hs

end OMA.ResiduePairs

theorem OMA.solution : OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1.H1 := by
  intro p q e f hp hq hop hoq hpq hq2 he hf hsum
  have hp3 : 3≤p := by
    have := hp.two_le
    by_contra! hh
    have : p=2 := by omega
    rw [this] at hop
    norm_num at hop
  exact OMA.ResiduePairs.region OMA.ResiduePairs.smallCover OMA.ResiduePairs.smallCover
    OMA.ResiduePairs.assembled hp hq hop hoq hpq (by decide) (by decide) hp3 (by omega) (by omega) (by omega) he hf hsum
