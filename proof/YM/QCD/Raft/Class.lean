import YM.QCD.Raft.Valued
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # cancellation at log-price accuracy by probe over independent arbitrarily large meshes -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi Asymptotics
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace ComplexConjugate
variable {n:Side}{a:su.Color}{η C D M W:ℝ}
def cap (n:Side):ℝ:=Fintype.card (Site n)
lemma cap_pos (n:Side):0<cap n:=by unfold cap; positivity
def densityP (n:Side):ℝ:=cap n*Pearl.beamH n^2
lemma density_pos (n):0<densityP n:=mul_pos (cap_pos n) (pow_pos (Pearl.beamP n) _)
def readP (P:Cnr n→ℝ)(a:su.Color):ℝ:=supS P a/densityP n
lemma density_ratio {c f:Side}(g:Ratio c f): densityP f=(g.count.val:ℝ)^2*densityP c:=by
  simp only [densityP,cap,site_card,Pearl.beamH,g.exact_size]; push_cast; field_simp
-- soft h ~ L^-1 normalizer
variable {j k N:ℕ}{F: Next.Free.Flight j k}{H V: Bed} {K:KernelChoices}{T:Towers F.L}{X Y:ℕ→Side}(h:Signal X Y H V T η C D N)
def lowS (T:Towers F.L) (t:ℝ):=sting (bright T (sun 1) t) * (F.L.val:ℝ)^2
variable (he: V.metric.strip η M)(hi:∀ i,Precision.Inputs (Orbit.Venue F K (h.sizes i)) (installed (Orbit.Venue F K (h.sizes i)).ratio T.A0) (H.metric.acts (Y i)) (V.metric.acts (X i)))
include h
lemma horizonG : Tendsto Y atTop atTop:= tendsto_atTop_mono (fun i=> (show (X i).val≤(Y i).val by rw [h.sizes i]; exact Nat.le_mul_of_pos_right _ F.L.property)) h.goes
lemma low_cont : DifferentiableAt ℝ (lowS (F:=F) T) 0:=by
  let g(t:ℝ) := bright T (sun 1) t
  have hp (i:TypeFace 1): ContDiffAt ℝ ω (fun t=>g t i) 0:=by unfold g bright; split; exact contDiffAt_const; exact contDiffAt_pi.mp (short_curve h.more h.deep _ _) _
  have hm : ContDiffAt ℝ ω (fun t=>sting (g t)* (F.L.val:ℝ)^2) 0:=ContDiffAt.mul (ContDiffAt.sum (s:=univ) fun i _=> (contDiff_norm_sq (E:=ℂ) ℝ).contDiffAt.comp _ (hp (coord i))) contDiffAt_const -- instance?
  exact hm.differentiableAt (by simp)
include he hi
lemma low_origin : lowS (F:=F) T 0=1 :=by
  unfold lowS; unfold sting; simp_rw [bright, principal_s h he hi]; rw [sum_eq_single 1]
  · rw [if_neg (show coord 1≠coord 0 from Exterior.axisEquiv.injective.ne (by decide))]
    simp only [Pi.smul_apply, norm_smul,norm_inv,Complex.norm_natCast,sun, Pi.single_eq_same,norm_one,mul_one]; field_simp
  · intro i _ he; split; · simp
    simp [sun,Pi.single_apply, show coord 1 ≠ coord i from axisEquiv.injective.ne he.symm]
  simp
lemma sloping :∃ S:ℝ,Tendsto (fun i=> (lowS (F:=F) T (pulseG X i)-1)/pulseG X i) atTop (𝓝 S):=by
  have H:= (hasDerivAt_iff_tendsto_slope.mp (low_cont h).hasDerivAt); simp_rw [slope_fun_def_field] at H -- maybe name
  have ht:=H.comp (vanishes h); refine ⟨deriv (lowS (F:=F) T) 0,?_⟩; simpa [Function.comp_def,low_origin h he hi] using ht
omit he hi
lemma local_log : Tendsto (fun i=> pulseG X i*Real.log (Y i).val) atTop (𝓝 0):=by
  let t:=pulseG X
  let d:= 2*Real.pi; let L:ℝ:= F.L.val
  have hd:0<d:=by unfold d; positivity
  have hL:0<L:=side_pos F.L
  have hh i : Real.log ((Y i).val)=Real.log L +Real.log d -Real.log (t i):=by
    rw [h.sizes i,Nat.cast_mul,Real.log_mul (by positivity) hL.ne']; unfold t pulseG Pearl.beamH; rw [Real.log_div hd.ne' (by positivity)]; unfold L d; ring
  have ht := Pearl.beam0.comp h.goes
  have hp : Tendsto (fun i=> t i*Real.log (t i)) atTop (𝓝 0):= by simpa only [t,Function.comp_def,zero_mul] using (Real.continuous_mul_log.tendsto 0).comp ht
  have h' : Tendsto (fun i=> t i * (Real.log L+Real.log d)) atTop (𝓝 0):= by simpa only [zero_mul] using! ht.mul_const (Real.log L+Real.log d)
  have he:=h'.sub hp; rw [sub_zero] at he; simp_rw [hh, mul_sub]; exact he
lemma catches (b:ℕ→ℝ)(p:ℝ)(hm:∀ᶠ i in atTop,|b i - p*Real.log (Y i).val|≤W): Tendsto (fun i=>pulseG X i*b i) atTop (𝓝 0):=by
  let t:= pulseG X
  have ht := Pearl.beam0.comp h.goes
  have hh : Tendsto (fun i=> t i*(b i - p*Real.log (Y i).val)) atTop (𝓝 0):=by
    apply squeeze_zero_norm' (a:=fun i=> t i*W) (hm.mono fun i h=> ?_) (by simpa only [zero_mul] using! ht.mul_const W)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Pearl.beamP ..)]; exact mul_le_mul_of_nonneg_left h (Pearl.beamP _).le
  have hp :=hh.add ((local_log h).const_mul p); rw [mul_zero,zero_add] at hp; exact hp.congr' (Eventually.of_forall fun i=>by unfold t; ring)
end YM.QCD.Raft
