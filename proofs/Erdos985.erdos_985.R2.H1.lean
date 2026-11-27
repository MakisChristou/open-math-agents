import OMAReductions.R_Erdos985_erdos_985_R2

/-! Prime primitive roots for all odd primes through 2791. For each candidate
the certificate checks the powers at the prime divisors of p-1. -/
namespace OMA.SmallPrimitive
def b0 : ℕ := 0xe105040c10b041c1030414103840c10b840a1030416102840c1058414103041c103840c105040a103040e107040c105841e103040a105040c102840a1030414102840c1070416103040e107840c1028414103040e102840c1050416103040a103840c102840a103040e102840a00000
def b1 : ℕ := 0xc10b042e1030434105040c107841e1030414103840c107840a103040e10d040c1070414103040a10b040c105041c103040e102840c105844e103042c105040c102840a1030414102840c10d0416103040a107040c1058414103041e102840c105042c103040a103840c107040a10304
def b2 : ℕ := 0x16103040a10d040c102841c103042e105040c113041e1030414103840c102840a103041c10b040c1138414103040e107040c1050444103042c102840c11184461030416105040c10704341030414102840c111041c103040e103840c105841410304ae102840c1050416103041c10384
def b3 : ℕ := 0x1c102840c1050416103041e107040c111040a103040e105040c10d0436103041410b040c107040a103040e102840c10d8414103042c103840c105040a1030446113040c105841e103041c105040c102840a1030414107040c11d842c1030434103840c10584141030444102840c10504
def b4 : ℕ := 0xc1070414103040e111040c105041c103040a103840c1028434103040e105040c107841e1030414103840c113040a103042c107040c1058414103040e103840c105040a1030434102840c107044c103040a105040c102841c103041410d040c1170444103040a103840c10b041410304
def b5 : ℕ := 0x34103041c107840c1028414103040e107040c1050416103040e10b040c10784441030416105040c107042e1030414117040c102841c103044c102840c1110414103040e10d040c1050416103041c102840c105842c103045c105040c102840a1030414102840c10b0416103042e10384
def b6 : ℕ := 0x14113040c1070416103040a103840c1028414103043410b040c1050416103040a103840c102845c103041c105040c11d042e1030414107040c102840a103040e102840c1130414103040e103840c105042c1030444102840c10d041c103040a105040c10b044c1030414102840c10b84
def b7 : ℕ := 0xc11f840a1030414103840c10b844c1030444107040c1078414103041e117040c1050416103042c103840c107042e1030416105040c11f041c1030414103840c10d040a103045c102840c1058414103041c103840c1050434103041e107040c10b0446103040a105040c111047410304
def b8 : ℕ := 0x46103047c105040c1070444103041410b040c10b841c103040a113040c1028414103042c102840c1050416103041c103840c105840a103040e105040c1170434103041411d040c107842c103040e102840c1070414103041e103840c105041c103040e111040c1058496103043410504
def b9 : ℕ := 0xe102840c113047c103041c105040c10d040a1030414107040c1078474103042c111040c1028414103040e102840c1050416103045c103840c102841c1030444105040c10b842c1030414103840c11d040a103041c107840c10b0414103040a107040c1050416103044c10d040c10584
def b10 : ℕ := 0xc105045c103043610b040c1070434103044c105040c102841c1030414102840c12504161030474103840c1170414103041c113040c10504441030434107040c11f042c103040e105040c10d8436103041410d040c107040a103041e102840c1118414103040a10b840c105040a10304
def b11 : ℕ := 0x14103040a10b040c105040a103041c125040c111042e103042c105040c113040a1030414102840c11d8416103040a103840c1070414103041e10d040c105041c103040e11f040c102840a103040e105040c10b041e1030414103840c10b840a103040e107040c10d0414103044410384
def b12 : ℕ := 0xe10b040c10b84141030434111040c105047c103042c102840c117041c103040e105040c102840a1030414103840c1078416103041c103840c10b84141030494107040c1050416103040e113040c10b040a103040e105040c107044e1030414103840c102841c1030416117040c11d04
def b13 : ℕ := 0xc113840a103042e10d040c1058414103041c11d040c10504a4103041e107040c1078444103040a105040c10284941030414102840c107042c103040e103840c11104141030474103840c1050434103040e103840c102844c103041c105040c129045c1030414107040c102840a10304
def b14 : ℕ := 0x4c1030414103840c117040a103042c102840c1070414103047c103840c105041c103042e102840c125844e103040a105040c102842c1030414111040c12b0416103044c107040c10b0414103040e11f040c10504161030444117040c10704a61030434105040c10b841c103041410b04
def b15 : ℕ := 0x5c105040c10d041e1030414113040c102840a103041c12b040c1058414103040e107040c1050416103040e102840c105842c103040a105040c107040a1030414102840c10b041c1030434125040c1130414103040e102840c1050474103041c10d040c105840a10304a4105040c11104
def b16 : ℕ := 0xc1290434103042c105040c11784441030414103840c107044c103040e102840c1178414103040a103840c105042c103043411d040c105841e103041c105040c10b040a1030414107040c1078416103040a103840c11f0414103044c102840c1050416103047410b040c102841c10304
def b17 : ℕ := 0x1c103042c105840c1028474103044e105040c10784ac1030414103840c102840a103047c107040c1250414103041e10d040c105040a103040e102840c107045c1030444105040c102841c1030414102840c12f0416103041611f040c10d0414103041c10b040c1050494103041e10704
def b18 : ℕ := 0x2c107040c105041610304a4103840c11304461030474105040c107042e1030414103840c102841c1030416103840c1058414103040a117040c1050444103041c102840c10d0436103040e105040c107840a1030414102840c1110434103045c10b040c1070414103040e102840c10504
def b19 : ℕ := 0xc1028414103044e102840c1050416103040a12b040c111040a103041c105040c111842c1030414107040c10d045c103040e129040c10b041410304bc113040c10504341030494102840c105841c103040a105040c117040a103041410b040c11f0416103041c10b840c102841410304
def b20 : ℕ := 0x16103040a107040c1028414103041e111040c1050416103040a103840c107042c103040e105040c113041c1030414103840c10b049410304ac102840c1058414103041c103840c105044c103045c107040c107841e1030434105040c11d040a103041411f040c1070444103042c10d04
def b21 : ℕ := 0xd6102840c105042c103041c103840c12f0444103040e105040c10b047c1030414103840c10d84a41030434102840c1070414103040e103840c105041c103040e10b040c105841e103040a105040c125040a1030414102840c11384
def code (p : ℕ) := ((if p<1408 then (if p<640 then (if p<256 then (if p<128 then b0 else b1) else (if p<384 then b2 else (if p<512 then b3 else b4))) else (if p<1024 then (if p<768 then b5 else (if p<896 then b6 else b7)) else (if p<1152 then b8 else (if p<1280 then b9 else b10)))) else (if p<2048 then (if p<1664 then (if p<1536 then b11 else b12) else (if p<1792 then b13 else (if p<1920 then b14 else b15))) else (if p<2432 then (if p<2176 then b16 else (if p<2304 then b17 else b18)) else (if p<2560 then b19 else (if p<2688 then b20 else b21))))) >>> (7*(p%128))) % 128
def powMod (q a e : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => if e=0 then 1 else
    let v := powMod q a (e/2) k
    let t := v*v%q
    if e%2=0 then t else t*a%q

lemma powMod_cast {q a e f : ℕ} (h : e<2^f) :
    (powMod q a e f : ZMod q)=(a : ZMod q)^e := by
  induction f generalizing e with
  | zero =>
    have : e=0 := by simpa using h
    simp [this,powMod]
  | succ f ih =>
    have he : e/2<2^f := by rw [pow_succ] at h; omega
    by_cases h0 : e=0
    · simp [powMod,h0]
    · simp only [powMod,h0,if_false]
      split
      · rename_i hb
        have hx : e/2*2=e := by omega
        simp only [ZMod.natCast_mod,Nat.cast_mul,ih he,←pow_add]
        congr 1
        omega
      · rename_i hb
        simp only [ZMod.natCast_mod,Nat.cast_mul,ih he,←pow_add,←pow_succ]
        congr 1
        omega

lemma powMod_lt {q a e : ℕ} (h : 1<q) (f : ℕ) : powMod q a e f < q := by
  cases f with
  | zero => exact h
  | succ f => simp only [powMod]; split <;> first | exact h | split <;> exact Nat.mod_lt _ (by omega)

def check (p : ℕ) : Bool :=
  let q := code p/2
  if code p%2=0 then
    decide (p≤2 ∨ (1<q ∧ q<p ∧ p%q=0))
  else
    decide (q ∈ ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53] : List ℕ) ∧ q < p) &&
      (powMod p q (p-1) 12 == 1) &&
      (p-1).primeFactorsList.all (fun r => powMod p q ((p-1)/r) 12 != 1)

lemma correct {p : ℕ} (hp : p.Prime) (h2 : p≠2) (bound : p≤2791) (hc : check p=true) :
    ∃ q : ℕ, q.Prime ∧ q<p ∧ orderOf (q : ZMod p) = p-1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let q := code p/2
  have p2 := hp.two_le
  unfold check at hc
  dsimp only at hc
  split_ifs at hc with flag
  · rcases of_decide_eq_true hc with low|⟨hq,hqp,hd⟩
    · omega
    · rcases (Nat.dvd_prime hp).1 (Nat.dvd_of_mod_eq_zero hd) with h|h <;> omega
  · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at hc
    have hsmall : q.Prime := by
      have hm := hc.1.1.1
      change q ∈ _ at hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel
    have hpos : 0<p-1 := by omega
    refine ⟨q,hsmall,hc.1.1.2,orderOf_eq_of_pow_and_pow_div_prime hpos ?_ ?_⟩
    · rw [← powMod_cast (q:=p) (a:=q) (f:=12) (by omega : p-1<2^12)]
      rw [show powMod p q (p-1) 12 = 1 from hc.1.2, Nat.cast_one]
    · intro r hr hd h
      have mem := (Nat.mem_primeFactorsList_iff_dvd (by omega : p-1 ≠ 0) hr).2 hd
      have ne := bne_iff_ne.mp (hc.2 r mem)
      have hf : (p-1)/r<2^12 := Nat.lt_of_le_of_lt (Nat.div_le_self ..) (by omega)
      rw [← powMod_cast (q:=p) (a:=q) hf] at h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast,ZMod.val_one,Nat.mod_eq_of_lt (powMod_lt hp.one_lt _)] at hv
      exact ne hv

def interval (lo count : ℕ) := (List.range count).all (fun j => check (lo+j))

lemma from_interval {lo count : ℕ} (h : interval lo count=true) (n : ℕ)
    (hl : lo≤n) (hr : n<lo+count) : check n=true := by
  have := List.all_eq_true.mp h (n-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hl] using this
lemma blockOK0 : interval 0 64=true := by decide +kernel
lemma blockOK64 : interval 64 64=true := by decide +kernel
lemma blockOK128 : interval 128 64=true := by decide +kernel
lemma blockOK192 : interval 192 64=true := by decide +kernel
lemma blockOK256 : interval 256 64=true := by decide +kernel
lemma blockOK320 : interval 320 64=true := by decide +kernel
lemma blockOK384 : interval 384 64=true := by decide +kernel
lemma blockOK448 : interval 448 64=true := by decide +kernel
lemma blockOK512 : interval 512 64=true := by decide +kernel
lemma blockOK576 : interval 576 64=true := by decide +kernel
lemma blockOK640 : interval 640 64=true := by decide +kernel
lemma blockOK704 : interval 704 64=true := by decide +kernel
lemma blockOK768 : interval 768 64=true := by decide +kernel
lemma blockOK832 : interval 832 64=true := by decide +kernel
lemma blockOK896 : interval 896 64=true := by decide +kernel
lemma blockOK960 : interval 960 64=true := by decide +kernel
lemma blockOK1024 : interval 1024 64=true := by decide +kernel
lemma blockOK1088 : interval 1088 64=true := by decide +kernel
lemma blockOK1152 : interval 1152 64=true := by decide +kernel
lemma blockOK1216 : interval 1216 64=true := by decide +kernel
lemma blockOK1280 : interval 1280 64=true := by decide +kernel
lemma blockOK1344 : interval 1344 64=true := by decide +kernel
lemma blockOK1408 : interval 1408 64=true := by decide +kernel
lemma blockOK1472 : interval 1472 64=true := by decide +kernel
lemma blockOK1536 : interval 1536 64=true := by decide +kernel
lemma blockOK1600 : interval 1600 64=true := by decide +kernel
lemma blockOK1664 : interval 1664 64=true := by decide +kernel
lemma blockOK1728 : interval 1728 64=true := by decide +kernel
lemma blockOK1792 : interval 1792 64=true := by decide +kernel
lemma blockOK1856 : interval 1856 64=true := by decide +kernel
lemma blockOK1920 : interval 1920 64=true := by decide +kernel
lemma blockOK1984 : interval 1984 64=true := by decide +kernel
lemma blockOK2048 : interval 2048 64=true := by decide +kernel
lemma blockOK2112 : interval 2112 64=true := by decide +kernel
lemma blockOK2176 : interval 2176 64=true := by decide +kernel
lemma blockOK2240 : interval 2240 64=true := by decide +kernel
lemma blockOK2304 : interval 2304 64=true := by decide +kernel
lemma blockOK2368 : interval 2368 64=true := by decide +kernel
lemma blockOK2432 : interval 2432 64=true := by decide +kernel
lemma blockOK2496 : interval 2496 64=true := by decide +kernel
lemma blockOK2560 : interval 2560 64=true := by decide +kernel
lemma blockOK2624 : interval 2624 64=true := by decide +kernel
lemma blockOK2688 : interval 2688 64=true := by decide +kernel
lemma blockOK2752 : interval 2752 40=true := by decide +kernel
end OMA.SmallPrimitive

open OMA.SmallPrimitive in
theorem OMA.solution : OMA.R_Erdos985_erdos_985_R2.H1 := by
  intro p hp h2 bound
  apply correct hp h2 bound
  exact if h : p < 1408 then if h : p < 704 then if h : p < 320 then if h : p < 128 then if h : p < 64 then from_interval blockOK0 p (by omega) (by omega) else from_interval blockOK64 p (by omega) (by omega) else if h : p < 192 then from_interval blockOK128 p (by omega) (by omega) else if h : p < 256 then from_interval blockOK192 p (by omega) (by omega) else from_interval blockOK256 p (by omega) (by omega) else if h : p < 512 then if h : p < 384 then from_interval blockOK320 p (by omega) (by omega) else if h : p < 448 then from_interval blockOK384 p (by omega) (by omega) else from_interval blockOK448 p (by omega) (by omega) else if h : p < 576 then from_interval blockOK512 p (by omega) (by omega) else if h : p < 640 then from_interval blockOK576 p (by omega) (by omega) else from_interval blockOK640 p (by omega) (by omega) else if h : p < 1024 then if h : p < 832 then if h : p < 768 then from_interval blockOK704 p (by omega) (by omega) else from_interval blockOK768 p (by omega) (by omega) else if h : p < 896 then from_interval blockOK832 p (by omega) (by omega) else if h : p < 960 then from_interval blockOK896 p (by omega) (by omega) else from_interval blockOK960 p (by omega) (by omega) else if h : p < 1216 then if h : p < 1088 then from_interval blockOK1024 p (by omega) (by omega) else if h : p < 1152 then from_interval blockOK1088 p (by omega) (by omega) else from_interval blockOK1152 p (by omega) (by omega) else if h : p < 1280 then from_interval blockOK1216 p (by omega) (by omega) else if h : p < 1344 then from_interval blockOK1280 p (by omega) (by omega) else from_interval blockOK1344 p (by omega) (by omega) else if h : p < 2112 then if h : p < 1728 then if h : p < 1536 then if h : p < 1472 then from_interval blockOK1408 p (by omega) (by omega) else from_interval blockOK1472 p (by omega) (by omega) else if h : p < 1600 then from_interval blockOK1536 p (by omega) (by omega) else if h : p < 1664 then from_interval blockOK1600 p (by omega) (by omega) else from_interval blockOK1664 p (by omega) (by omega) else if h : p < 1920 then if h : p < 1792 then from_interval blockOK1728 p (by omega) (by omega) else if h : p < 1856 then from_interval blockOK1792 p (by omega) (by omega) else from_interval blockOK1856 p (by omega) (by omega) else if h : p < 1984 then from_interval blockOK1920 p (by omega) (by omega) else if h : p < 2048 then from_interval blockOK1984 p (by omega) (by omega) else from_interval blockOK2048 p (by omega) (by omega) else if h : p < 2432 then if h : p < 2240 then if h : p < 2176 then from_interval blockOK2112 p (by omega) (by omega) else from_interval blockOK2176 p (by omega) (by omega) else if h : p < 2304 then from_interval blockOK2240 p (by omega) (by omega) else if h : p < 2368 then from_interval blockOK2304 p (by omega) (by omega) else from_interval blockOK2368 p (by omega) (by omega) else if h : p < 2624 then if h : p < 2496 then from_interval blockOK2432 p (by omega) (by omega) else if h : p < 2560 then from_interval blockOK2496 p (by omega) (by omega) else from_interval blockOK2560 p (by omega) (by omega) else if h : p < 2688 then from_interval blockOK2624 p (by omega) (by omega) else if h : p < 2752 then from_interval blockOK2688 p (by omega) (by omega) else from_interval blockOK2752 p (by omega) (by omega)
