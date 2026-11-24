import YM.QCD.Pearl.Signal

/-! # Errors with finite bills per volume -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p : Site n} {i : Axis} {κ η c s q b B r ε K : ℝ}{j:ℕ}{F : Momentum→Para}{A W: Shine→Bundle}

def shock (A W: Shine→Bundle)(F: Momentum→Para)(p : Site n):= (beamH n)^4/(2*(beamH n)^2)*(stroke A W F p 0-stroke A W F p 1)
lemma lowCliff {p: Site n}{v:Train j}(hw:Wall η b A)(hQ:Wall η s W)(he:0<η)(h : Pinch (Dir v) r c B)(e:Bright r c B ε) (hn: 4≤n.val)(ht: beamH n≤1)(hq:beamH n<zone) :
    |shock A W (Dir v) p| ≤ 4*lowCost r c B b s:=by
  let d:=beamH n; have hd:0<d:=beamP _
  let ZQ:= lowCost r c B b s; have hk:=keyboard p
  have hZ (x:ℝ)(i:Axis): physical (boost x i):=by unfold boost; ext a; by_cases h:a=i <;> simp [h]
  have hv (k: Axis) (t:ℝ) (h₁:|t|≤beamH n)(x: Site n)(hx:Fans x (boost t k)): |storm A W (Dir v) p k t| ≤ ZQ/d^2:= low_bound hw hQ he h e (hZ _ _) hx ht (garage (Set.mem_univ p) hq t h₁ k)
  have hs (k:Axis): |stroke A W (Dir v) p k| ≤ 4*ZQ/d^2:=by
    have hl : Fans (step k : Site n) (boost (beamH n) k):= arrow hn k ▸ fanN _
    have h₁:= hv k d (by rw [abs_of_pos hd]) _ hl
    have h₂:= hv k (-d) (by rw [abs_neg,abs_of_pos hd]) _ ((cast_N d k).symm ▸ hl.negative)
    have hν : Fans (0:Site n) (boost 0 k):=by simpa [boost] using fanN (0:Site n)
    have h₃:= hv k 0 (by rw [abs_zero]; exact hd.le) _ hν
    apply (abs_sub ..).trans; rw [abs_mul]
    refine (add_le_add ((abs_add_le ..).trans (add_le_add h₁ h₂)) (mul_le_mul_of_nonneg_left h₃ (abs_nonneg _))).trans_eq ?_; norm_num; ring
  unfold shock; change |d^4/(2*d^2)*_| ≤ 4*ZQ; rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ d^4/(2*d^2))];
  exact (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add (hs 0) (hs 1))) (by positivity)).trans_eq (by field_simp; ring)

def overH (A W: Shine→ Bundle)(F:Momentum→Para)(p: Site n):= shock A W F p-(beamH n)^4 *windward (centerZ p)
lemma highStep (C:su.Color)(hC:‖C‖=1)(S:ℝ) (h: Pinch F r c B)(hS: Pinch shaft r c B)(e:Bright r c B ε)(he:0<η)(hw:Wall η b A)(hQ: Wall η S W)(hε:ε*Real.pi≤η/2)(hA:A 0=touch (echo C)*wave (gamma 1)) (K:ℝ)(hK:8 < κ*ε)(h' : |wobble2 r c B η b S| ≤ K) (hx:p∉smallH n κ):
    |overH A W F p| ≤ (beamH n)^4*( (128*K/ε^2)*radial 3 (centerZ p)+ 960*beamH n*radial 5 (centerZ p)):=by
  let t:=beamH n; let L:=wobble2 r c B η b S
  let a:=stroke A W F p
  let Y:=centerZ p
  let d:=‖Y‖; let y:= tuning p
  have hi: d≤ 2*‖y‖:= (whirl p).trans_le (fry_upper _)
  have hb: 0<‖y‖:=norm_pos_iff.mpr (tune_nonzero _); have hr:0<d:= hb.trans_le ((fry_lower _).trans_eq (whirl p).symm)
  have ht:0<t:=beamP _; have he' := e.seed
  have hz (i:Axis):|a i - 2*t^2* lush Y i| ≤ (128*K)/ε^2*t^2*radial 3 Y+960*t^3*radial 5 Y :=by
    apply (wrapped C hC S h hS e hw hQ hε he hA p hK hx i).trans; apply add_le_add; swap
    · exact le_of_eq (by unfold radial; dsimp only [t,Y]; ring)
    change 16*L/ε^2*t^2/‖y‖^3 ≤ (128*K)/ε^2*t^2*(d^3)⁻¹
    have hκ : 0≤K:= (abs_nonneg _).trans h'
    apply le_trans (b:=16*K/ε^2*t^2/‖y‖^3)
    · gcongr; exact (le_abs_self _).trans h'
    have hd : d^3≤ (2*‖y‖)^3:=pow_le_pow_left₀ hr.le hi _; field_simp; nlinarith only [mul_le_mul_of_nonneg_left hd hκ]
  unfold overH; rw [show shock A W F p - _ = t^4/(2*t^2)*((a 0-2*t^2*lush Y 0)-(a 1-2*t^2*lush Y 1)) from ?_, abs_mul,abs_of_nonneg (by positivity : 0 ≤ t^4/(2*t^2))]
  · apply (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add (hz 0) (hz 1))) (by positivity)).trans_eq; change _ = t^4*(_*_+960*t*radial 5 Y); field_simp; ring
  change t^4/(2*t^2)*(a 0 -a 1)-t^4*(lush Y 0-lush Y 1)=_; field_simp; ring
end YM.QCD.Pearl
