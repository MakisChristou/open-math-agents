import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.BigOperators.Intervals

/-! Amdeberhan, Medina and Moll obtained nonvanishing from the 2-adic
valuation of the arctangent sum. We track the parity of the two Gaussian
coordinates directly. Pairing j with 8s−j controls the valuations at
the four exceptional positions around each multiple of eight. -/

namespace OMA.Arctan
open Finset GaussianInt

def F (j : ℤ) : GaussianInt := ⟨1,j⟩
def G (n : ℕ) : GaussianInt := ∏ j ∈ range (n+1), F j

lemma imag (n : ℕ) : OeisA105751.a n=(G n).im := by
  have hh : GaussianInt.toComplex (G n)=∏ k ∈ range (n+1), (1+(k : ℂ)*Complex.I) := by
    simp [G,F,map_prod,GaussianInt.toComplex_def']
  change ⌊(∏ k ∈ range (n+1), (1+(k : ℂ)*Complex.I)).im⌋=_
  rw [←hh,←GaussianInt.intCast_im,Int.floor_intCast]

/-- After removal of a nonzero common integer factor, the real part is
odd and the imaginary part is t times a number of prescribed parity. -/
def Shape (t : ℤ) (e : ZMod 2) (z : GaussianInt) := ∃ c a b : ℤ, c≠0 ∧
  (a:ZMod 2)=1 ∧ (b:ZMod 2)=e ∧ z.re=c*a ∧ z.im=c*t*b

lemma shapeOne (t : ℤ) : Shape t 0 1 :=
  ⟨1,1,0,by decide,by simp,by simp,by simp,by simp⟩

lemma combine {t : ℤ} {e f : ZMod 2} {u v : GaussianInt} (ht : (t:ZMod 2)=0)
    (hu : Shape t e u) (hv : Shape t f v) : Shape t (e+f) (u*v) := by
  obtain ⟨c,a,b,hc,ha,hb,ua,ub⟩ := hu
  obtain ⟨C,A,B,hC,hA,hB,va,vb⟩ := hv
  refine ⟨c*C,a*A-t*t*b*B,a*B+b*A,mul_ne_zero hc hC,?_,?_,?_,?_⟩
  · push_cast
    simp [ht,ha,hA]
  · push_cast
    simp [ha,hA,hb,hB,add_comm]
  · simp only [Zsqrtd.re_mul,ua,ub,va,vb]
    ring
  · simp only [Zsqrtd.im_mul,ua,ub,va,vb]
    ring

lemma nonzero {t : ℤ} {z : GaussianInt} (ht : t≠0) (hz : Shape t 1 z) : z.im≠0 := by
  obtain ⟨c,_,b,hc,_,hb,_,hi⟩ := hz
  have hn : b≠0 := by rintro rfl; norm_num at hb
  rw [hi]
  exact mul_ne_zero (mul_ne_zero hc ht) hn

lemma before {t : ℤ} {z v : GaussianInt} (ht : t≠0) (hv : Shape t 0 v)
    (hzv : Shape t 1 (z*v)) : z.im≠0 := by
  intro hi
  obtain ⟨c,a,b,hc,ha,hb,va,vb⟩ := hv
  obtain ⟨C,A,B,hC,hA,hB,za,zb⟩ := hzv
  simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hi,va,vb,mul_zero,zero_mul,add_zero] at za zb
  have he : C*t*(B*a-A*b)=0 := by
    linear_combination (norm := ring) -a*zb+t*b*za
  have hBA : B*a=A*b := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hC ht))
  have hbad := congrArg (fun v : ℤ => (v:ZMod 2)) hBA
  push_cast at hbad
  simp [ha,hb,hA,hB] at hbad

lemma pairEven (s j : ℤ) : Shape (4*s) 0 (F (2*j)*F (8*s-2*j)) := by
  refine ⟨1,1-2*j*(8*s-2*j),2,by decide,?_,by decide,?_,?_⟩
  · push_cast
    simp [show (2:ZMod 2)=0 by decide]
  · simp [F,Zsqrtd.re_mul]; ring
  · simp [F,Zsqrtd.im_mul]; ring

lemma pairOdd (s j : ℤ) : Shape (4*s) 1 (F (2*j+1)*F (8*s-(2*j+1))) := by
  refine ⟨2,1+2*j+2*j*j-4*s*(2*j+1),1,by decide,?_,by simp,?_,?_⟩
  · push_cast
    simp [show (2:ZMod 2)=0 by decide,show (4:ZMod 2)=0 by decide]
  · simp [F,Zsqrtd.re_mul]; ring
  · simp [F,Zsqrtd.im_mul]; ring

def paired (s : ℤ) (j : ℕ) := F j*F (8*s-j)

lemma pairs (s : ℤ) (h : ℕ) : Shape (4*s) (h:ZMod 2) (∏ j∈range (2*h),paired s j) := by
  have ht : ((4*s:ℤ):ZMod 2)=0 := by push_cast; simp [show (4:ZMod 2)=0 by decide]
  induction h with
  | zero => simpa using shapeOne (4*s)
  | succ h ih =>
    rw [show 2*(h+1)=2*h+1+1 by omega,prod_range_succ,prod_range_succ,Nat.cast_succ]
    have he : paired s (2*h)=F (2*(h:ℤ))*F (8*s-2*h) := by simp [paired]
    have ho : paired s (2*h+1)=F (2*(h:ℤ)+1)*F (8*s-(2*h+1)) := by simp [paired]
    rw [he,ho]
    exact combine ht (by simpa using combine ht ih (pairEven s h)) (pairOdd s h)

lemma reflectProd {M : Type*} [CommMonoid M] (f : ℕ→M) (k : ℕ) :
    ∏ j∈range (2*k+1), f j = (∏ j∈range k,(f j*f (2*k-j)))*f k := by
  rw [show 2*k+1=(k+1)+k by omega,prod_range_add,prod_range_succ,prod_mul_distrib]
  rw [←prod_range_reflect (fun j => f (k+1+j)) k]
  have he : (∏ j∈range k,f (k+1+(k-1-j)))=∏ j∈range k,f (2*k-j) := by
    apply prod_congr rfl
    intro j hj
    congr 1
    have := mem_range.mp hj
    omega
  rw [he]
  ac_rfl

lemma center (s : ℕ) : Shape (4*(s:ℤ)) 1 (G (8*s)) := by
  have ht : ((4*(s:ℤ):ℤ):ZMod 2)=0 := by push_cast; simp [show (4:ZMod 2)=0 by decide]
  have h := pairs (s:ℤ) (2*s)
  have h0 : ((2*s:ℕ):ZMod 2)=0 := by push_cast; simp [show (2:ZMod 2)=0 by decide]
  rw [h0,show 2*(2*s)=4*s by omega] at h
  have hmid : Shape (4*(s:ℤ)) 1 (F (4*s)) := ⟨1,1,1,by decide,by simp,by simp,by simp [F],by simp [F]⟩
  unfold G
  rw [show 8*s=2*(4*s) by omega,reflectProd]
  have he : (∏ j∈range (4*s), (F j*F ((2*(4*s)-j:ℕ):ℤ)))=∏ j∈range (4*s), paired s j := by
    apply prod_congr rfl
    intro j hj
    have := mem_range.mp hj
    unfold paired
    congr 2
    rw [Nat.cast_sub (show j≤2*(4*s) by omega)]
    push_cast
    ring
  rw [he]
  simpa using combine ht h hmid

lemma centerFactor (t j : ℤ) : Shape t 0 (F (2*t*j)) := by
  refine ⟨1,1,2*j,by decide,by simp,?_,by simp [F],?_⟩
  · push_cast
    simp [show (2:ZMod 2)=0 by decide]
  · simp [F]; ring

lemma triple (t j e : ℤ) (he : e=1 ∨ e= -1) :
    Shape t 0 (F (2*t*j+e)*F (2*t*j+2*e)*F (2*t*j+3*e)) := by
  refine ⟨2,-6*(t*j)^2-12*(t*j)*e-5,-j*(2*t*j+2*e)*(2*t*j+4*e),by decide,?_,?_,?_,?_⟩
  · push_cast
    simp [show (6:ZMod 2)=0 by decide,show (12:ZMod 2)=0 by decide,show (5:ZMod 2)=1 by decide]
  · push_cast
    simp [show (2:ZMod 2)=0 by decide]
  · rcases he with rfl|rfl <;> simp [F,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
  · rcases he with rfl|rfl <;> simp [F,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

lemma block (t j : ℤ) (ht : (t:ZMod 2)=0) :
    Shape t 0 (F (2*t*j-3)*F (2*t*j-2)*F (2*t*j-1)*F (2*t*j)) := by
  have h := triple t j (-1) (Or.inr rfl)
  convert (by simpa only [add_zero] using combine ht h (centerFactor t j) :
    Shape t 0 ((F (2*t*j+ -1)*F (2*t*j+2* -1)*F (2*t*j+3* -1))*F (2*t*j))) using 1
  simp only [mul_neg_one,←sub_eq_add_neg]
  ac_rfl

lemma succG (n : ℕ) : G (n+1)=G n*F ((n:ℤ)+1) := by simp [G,prod_range_succ]

lemma addThree (n : ℕ) : G (n+3)=G n*(F ((n:ℤ)+1)*F ((n:ℤ)+2)*F ((n:ℤ)+3)) := by
  simp only [succG,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  ring_nf

lemma addFour (n : ℕ) : G (n+4)=G n*(F ((n:ℤ)+1)*F ((n:ℤ)+2)*F ((n:ℤ)+3)*F ((n:ℤ)+4)) := by
  rw [show n+4=n+3+1 by omega,succG,addThree]
  push_cast
  ring_nf

lemma fourShape (m : ℕ) : Shape 2 0 (G (4*m)) := by
  induction m with
  | zero => exact shapeOne 2
  | succ m ih =>
    rw [show 4*(m+1)=4*m+4 by omega,addFour]
    have h := block 2 ((m:ℤ)+1) (by decide)
    convert (by simpa using combine (by decide : ((2:ℤ):ZMod 2)=0) ih h :
      Shape 2 0 (G (4*m)*(F (2*2*((m:ℤ)+1)-3)*F (2*2*(m+1)-2)*F (2*2*(m+1)-1)*F (2*2*(m+1))))) using 1
    push_cast
    ring_nf

lemma afterParity {z B : GaussianInt} (h : Shape 2 0 z) (hb : (B.im:ZMod 2)=1) :
    (z*B).im≠0 := by
  obtain ⟨c,a,b,hc,ha,_,zr,zi⟩ := h
  intro hh
  have hh' : c*(a*B.im+2*b*B.re)=0 := by
    rw [Zsqrtd.im_mul,zr,zi] at hh
    linear_combination hh
  have hkill := (mul_eq_zero.mp hh').resolve_left hc
  have he := congrArg (fun x : ℤ => (x:ZMod 2)) hkill
  push_cast at he
  simp [ha,hb,show (2:ZMod 2)=0 by decide] at he

lemma afterOne (m : ℕ) : (G (4*m+1)).im≠0 := by
  rw [succG]
  apply afterParity (fourShape m)
  simp [F,show (4:ZMod 2)=0 by decide]

lemma afterTwo (m : ℕ) : (G (4*m+2)).im≠0 := by
  rw [show 4*m+2=4*m+1+1 by omega,succG,succG,mul_assoc]
  apply afterParity (fourShape m)
  simp [F,Zsqrtd.im_mul,show (4:ZMod 2)=0 by decide]
  decide

lemma nonvanishing {n : ℕ} (hn : 4≤n) : (G n).im≠0 := by
  let s := n/8
  have hrem : n=8*s+n%8 := by dsimp [s]; omega
  have h4s : ((4*(s:ℤ):ℤ):ZMod 2)=0 := by push_cast; simp [show (4:ZMod 2)=0 by decide]
  have hs1 : (4*((s:ℤ)+1):ℤ)≠0 := by positivity
  rcases show n%4=1 ∨ n%4=2 ∨ n%8=0 ∨ n%8=3 ∨ n%8=4 ∨ n%8=7 by omega with h|h|h|h|h|h
  · rw [show n=4*(n/4)+1 by omega]
    exact afterOne _
  · rw [show n=4*(n/4)+2 by omega]
    exact afterTwo _
  · have hs : 0<s := by omega
    rw [show n=8*s by omega]
    exact nonzero (by positivity) (center s)
  · have hs : 0<s := by omega
    rw [show n=8*s+3 by omega,addThree]
    have hT := triple (4*(s:ℤ)) 1 1 (Or.inl rfl)
    apply nonzero (t:=4*(s:ℤ)) (by positivity)
    convert (by simpa only [add_zero] using combine h4s (center s) hT :
      Shape (4*(s:ℤ)) 1 (G (8*s)*(F (2*(4*(s:ℤ))*1+1)*F (2*(4*s)*1+2*1)*F (2*(4*s)*1+3*1)))) using 1
    push_cast
    ring_nf
  · have hN : n+4 = 8*(s+1) := by omega
    have hC := center (s+1)
    rw [←hN,addFour] at hC
    have hB := block (4*((s:ℤ)+1)) 1 (by push_cast; simp [show (4:ZMod 2)=0 by decide])
    apply before (t:=4*((s:ℤ)+1)) hs1 _ (by simpa using hC)
    have hn' : (n:ℤ)=8*(s:ℤ)+4 := by exact_mod_cast (show n=8*s+4 by omega)
    rw [hn']
    convert hB using 1
    ring_nf
  · have hN : n+1=8*(s+1) := by omega
    have hC := center (s+1)
    rw [←hN,succG] at hC
    apply before (t:=4*((s:ℤ)+1)) hs1 _ (by simpa using hC)
    have he : (n:ℤ)+1=2*(4*((s:ℤ)+1))*1 := by
      have := (show (n:ℤ)+1=8*((s:ℤ)+1) by exact_mod_cast hN)
      linarith
    rw [he]
    exact centerFactor _ _

end OMA.Arctan

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H2 := by
  intro n hn
  rw [OMA.Arctan.imag]
  exact OMA.Arctan.nonvanishing hn
