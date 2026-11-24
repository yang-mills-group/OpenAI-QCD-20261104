import YM.QCD.Pearl.Salt

/-!
# The paired valuation; exact at fixed antiperiodic grids
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch Pine
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p : Site n} {i : Axis} {μ κ η c s q b B r ε e a d : ℝ}{j:ℕ}{F : Momentum→Para}
variable (C:su.Color){P:Plan j}{v:Train j} {G:I→Gleam}{U:J→ Bloom 1}{V:D→Bloom 2}

def roundoff (A W: Shine→Bundle)(F:Momentum→Para)(n:Side)(k:Site n)(i:Axis)(z:ℝ):= modelX A W F (menu k) i z
variable {A W : Shine→ Bundle}
abbrev storm (A W:Shine→Bundle)(F:Momentum→Para)(p:Site n)(i:Axis)(x:ℝ):=roundoff A W F n p i x

def stroke (A W : Shine→Bundle)(F : Momentum→Para)(p: Site n)(i: Axis):ℝ:= let t:=beamH n; storm A W F p i t +storm A W F p i (-t) - 2*storm A W F p i 0
def lush (x:Gₐ)(a:Axis):=f0 (ix x) a
lemma isLift (h:4≤ n.val): lift (step i:Site n)=step i:=by
  rw [lift_eq_iff]; constructor; · simp
  intro a; by_cases hz:a=i <;> simp [hz] <;> omega
lemma arrow (h:4 ≤ n.val)(i:Axis): mon (step i:Site n)=boost (beamH n) i:=by
  ext1 a; unfold boost mon Laurent.reciprocal; rw [isLift (i:=i) h]; by_cases he:a=i <;> simp [he,beamH]; ring
lemma garage (hp: p∈Set.univ) (he:beamH n<zone)(x : ℝ)(hx:|x|≤ beamH n)(i:Axis): tuning p+boost x i∈realCube zone:= by
  constructor
  · change physical (castP (menu p)+boost x i); rw [liftV]; exact arcP _
  intro a; simp only [Pi.add_apply,Complex.add_re]; apply (abs_add_le ..).trans_lt; apply add_lt_add_of_le_of_lt ((keyboard p).2 a)
  exact ((Complex.abs_re_le_norm _).trans (norm_le_pi_norm _ a)).trans_lt (by rw [camp_cast]; exact hx.trans_lt he)

def testN (M:Weather n→Sheet n)(i : Axis):= (polarization M 1 (step i)).re
lemma gun (he:4≤n.val)(hk:beamH n<zone)(h:Package η a b c P v G U V):
    let X:=extent C G U V n; let Y:=v₁ G U C 1; let Z:=v₂ G U V C 1
    2*testN X 0= (∑ i : Site n,(stroke Y Z (Dir v) i 0-stroke Y Z (Dir v) i 1)):=by
  intro X Y Z; let t:=beamH n
  have hx : 0<t:=beamP n
  have hv (a:Axis) : (∑ i:Site n, stroke Y Z (Dir v) i a) = (testN X a+testN X a)-2*∑ i: Site n,storm Y Z (Dir v) i 0 0:=by
    let p:Site n:=step a; have hu : Fans p (boost t a):= arrow he a▸ fanN p
    have hs:= path_price C h 1 hu (fun k=>garage (p:=k) (Set.mem_univ _) hk t (by rw [abs_of_pos hx]) a)
    have hh: Fans (-p) (boost (-t) a):= cast_N t a|>.symm ▸ hu.negative; have hT:=path_price C h 1 hh (fun k=>garage (p:=k) (Set.mem_univ _) hk (-t) (by rw [abs_neg,abs_of_pos hx]) a)
    rw [← pol_even C h 1 p] at hT
    have hy i: storm Y Z (Dir v) i a 0=storm (n:=n) Y Z (Dir v) i 0 0:=by unfold storm roundoff modelX; simp [boost]
    have hΛ: testN X a= ∑ i:Site n, storm Y Z (Dir v) i a t:=by unfold testN X; rw [show step a =p from rfl,hs,Complex.re_sum]; rfl
    have hΩ: testN X a= ∑ i:Site n, storm Y Z (Dir v) i a (-t):=by unfold testN X; rw [show step a =p from rfl,hT,Complex.re_sum]; rfl
    simp only [stroke, t,hy,sum_sub_distrib,sum_add_distrib,mul_sum]; rw [← hΛ,← hΩ]
  have hX : testN X 1=0:=by
    have he' : step 1≠ (0:Site n):=by intro h; have ht:=isLift (i:=1) he; rw [h] at ht; replace ht:= congr_fun ht 1; simp [lift] at ht
    have hh:= transverse C h (step 1:Site n) 1 he' (fun i hi=>by rw [cell_step,arrow he 1]; simp [boost,hi]); exact congr_arg Complex.re hh
  rw [sum_sub_distrib,hv,hv,hX]; ring
lemma wrapped (C:su.Color)(hC : ‖C‖=1)(S) (h: Pinch F r c B)(hS: Pinch shaft r c B)(e:Bright r c B ε)
    (hw:Wall η b A)(hQ:Wall η S W)(hε:ε*Real.pi≤η/2)(he:0<η)(hA:A 0=touch (echo C)*wave (gamma 1)) (p:Site n)(hp:8<κ*ε) (hx: p∉ smallH n κ)(i:Axis):
    let t:=beamH n
    let k:=tuning p; let Y:=centerZ p
    |stroke A W F p i-2*t^2*lush Y i| ≤ (16*wobble2 r c B η b S)/(ε^2)*t^2/‖k‖^3+2*(480*t^3/‖Y‖^5):=by
  intro t k Y; have ht:0<t:=beamP n
  have hN:=tune_nonzero p; have hK:= keyboard p
  let d:=‖Y‖; have hd : κ*t < d:= lt_of_not_ge (mt small_h.mpr hx); have hg : d=fry (menu p):=whirl _
  have hh : d≤ 2*‖k‖:= (whirl p).trans_le (fry_upper _); have hr: ε>0 := e.seed; have hc:=e.span
  have hκ: 8<κ:=by nlinarith
  have hL:t< ε*‖k‖ /4:= by
    have h: κ*t*ε < 2*‖k‖*ε:= mul_lt_mul_of_pos_right (hd.trans_le hh) hr
    nlinarith
  have hy : lush Y i=f0 (menu p) i:= by unfold lush Y centerZ; rw [ix.apply_symm_apply]
  have hu:= orbitClose C h hS e hε he hw hQ hA (menu p) hK hN i ht.le hL
  have H:= glistle C hC (menu p) (by rw [← hg]; nlinarith) i ht.le (by rw [← hg]; nlinarith)
  rw [← hg,← hy] at H
  change |stroke A W F p i-(trekS C (menu p) i t+trekS C (menu p) i (-t)-2*trekS C (menu p) i 0)|≤_ at hu
  exact (abs_sub_le (stroke A W F p i) _ (2*t^2*lush Y i)).trans (add_le_add hu H)
end YM.QCD.Pearl
