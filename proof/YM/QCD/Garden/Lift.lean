import YM.QCD.Orbit.Wharf
import YM.Extra.ITERATION_NO_LOSS.Inherited

/-! # Change at a tree by Schur differencing

For the actual slot action with nonlinear gauge curvature. Tangent affects
first nonzero jet. Entry radii not this file's output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch
open Orbit Orbit.Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
section rays
variable {X Y Z:Type}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedAddCommGroup Z][NormedSpace ℝ X][NormedSpace ℝ Y][NormedSpace ℝ Z]
 [CompleteSpace Y][CompleteSpace Z] {F:X→Y}{G:Y→ Z}
lemma bend {k:ℕ}(h : AnalyticAt ℝ F 0)(hg : AnalyticAt ℝ G 0)(he:F 0=0)(hz:Rays k G)(v:X):
    Tendsto (fun t:ℝ=> (t^k)⁻¹ • (G∘F) (t • v)) cutRay (𝓝 (Tensor.diagonal (Tensor.coeff G k 0) (fderiv ℝ F 0 v))):=by
  have hQ : AnalyticAt ℝ (G ∘ F) 0:= (he.symm ▸ hg : AnalyticAt ℝ G (F 0)).comp h
  have hp:= (rays_jet hg k).1 hz
  have hh (i:ℕ)(hx:i≤k)(a:Fin i→X): iteratedFDeriv ℝ i (G∘F) 0 a=iteratedFDeriv ℝ i G 0 (fderiv ℝ F 0∘a):= by
    rw [quiet_comp _ h (by rw [he]; exact hg) (by intro j H hp'; rw [he]; exact hp _ (lt_of_lt_of_le H hx)), he]
  have HJ:= (rays_jet hQ k).2 fun i hi=> ContinuousMultilinearMap.ext (fun j=> (hh i hi.le j).trans (by rw [hp i hi]; rfl))
  have hB:= ray_limit hQ HJ v; unfold Tensor.diagonal Tensor.coeff at hB ⊢; rw [_root_.smul_apply,hh _ le_rfl] at hB; exact hB

omit [NormedSpace ℝ Z] in
lemma rays_nil {k:ℕ} (h:AnalyticAt ℝ F 0)(H:∀ v:X,Tendsto (fun t:ℝ=> (t^k)⁻¹ • F (t • v)) cutRay (𝓝 0)): ∀ i<k+1,iteratedFDeriv ℝ i F 0=0:=by
  have he:= ray_origin (fun p:X=>⟨_,H p⟩)
  intro i hi; rcases lt_or_eq_of_le (show i ≤ k by omega) with hu|rfl; exact (rays_jet h _).1 he _ hu
  have hf:= h.contDiffAt (n:=ω)
  refine Tensor.ext_diag _ _ hf.iteratedFDeriv_comp_perm (fun _ _=> rfl) (funext fun x:X=>?_)
  have hp : Tensor.diagonal (Tensor.coeff F i 0) x=0:=tendsto_nhds_unique (ray_limit h he x) (H x)
  unfold Tensor.diagonal Tensor.coeff at hp
  rw [_root_.smul_apply] at hp; exact (smul_eq_zero.mp hp).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
end rays
variable {c f L: Side}{K:KernelChoices}{j k m:ℕ}{p:Clip}{D: Flight j k}{E A:Bed}{I:Type}{W:I→Bloom m}{r B:ℝ}
variable {e:f.val=c.val*D.L.val}
variable {R:PathData su} {T:Forest (Venue D K e).ratio} {u:Bid.Dir su c→AxisChart su T}{C : Towers (Venue D K e).patch.L} (hu: Critical T p R u) (ht:Guessed (S:=Venue D K e) T (installed (Venue D K e).ratio C.A0) u)

def rise (H:Forest (Venue D K e).ratio)(Z:Towers (Venue D K e).patch.L)(x : Cnr c):= (arm su f 1).symm (Channel.rising (S:=Venue D K e) H (installed (Venue D K e).ratio Z.A0) (arm su c 1 x))

include hu ht in
lemma germ (hr:0<r)(h:Fractal W r B)(v:Cnr c) : Tendsto (fun t:ℝ=> (t^m)⁻¹ • dust W f (encamp T u (t • v)).1) cutRay (𝓝 (∑' i, epilogue (W i) (rise T C v))):=by
  let X:=chartOf T u; let F:= arm su c 1; let L' := arm su f 1
  let M:= L'.symm ∘ (X∘F); let G:=metastage W f; let H(q:Cnr c):=encamp T u q
  have hX : X 0=0:=by unfold X chartOf; rw [hu.1]; exact congr_arg Prod.snd (Work.F03.inclusion_zero _)
  have hi : AnalyticAt ℝ G 0:= (serenity h hr).analyticAt
  have hb : AnalyticAt ℝ X 0:= (chart_jet u hu.2.1 hu.1).analyticAt
  have he : AnalyticAt ℝ X (F 0):= by rw [map_zero]; exact hb
  have hXF := he.comp (show AnalyticAt ℝ _ (0:Cnr c) from F.analyticAt 0)
  have hXF' : (X ∘ ⇑F) 0=0:=by rw [Function.comp_apply,map_zero,hX]
  have ha:= bend (F:=M) ((L'.symm.analyticAt _).comp hXF) hi (by unfold M; rw [Function.comp_apply,hXF',map_zero]) (ray_origin fun x=> ⟨_,sunrise h x⟩) v
  have heq : fderiv ℝ M 0 v=rise T C v:=by
    unfold M; rw [fderiv_comp 0 L'.symm.differentiableAt hXF.differentiableAt, ContinuousLinearMap.comp_apply,fderiv_comp 0 he.differentiableAt F.differentiableAt, ContinuousLinearMap.comp_apply,map_zero]; unfold X; rw [ContinuousLinearEquiv.fderiv, ContinuousLinearEquiv.fderiv]; simp_rw [ContinuousLinearEquiv.coe_coe]; rw [chart_tangent _ hu ht]; rfl
  have hx := tendsto_nhds_unique (ray_limit hi (ray_origin fun x=> ⟨_,sunrise h x⟩) (rise T C v)) (sunrise h (rise T C v))
  rw [heq,hx] at ha
  let g(x:Cnr c):= (F x,u (F x))
  have hg : Tendsto g (𝓝 0) (𝓝 0):=by
    have hx: g 0=0:=by unfold g; rw [map_zero,hu.1]; rfl
    rw [← hx]; exact ((F.continuousAt (x:=0)).prodMk ((show ContinuousAt u (F 0) by rw [map_zero]; exact hu.2.1.continuousAt).comp F.continuousAt)).tendsto
  apply ha.congr'
  filter_upwards [(hg.comp (along v)).eventually (Work.F03.inclusion_works (G:=su) T)] with t hz
  change (t^m)⁻¹ • dust W f (input su f (M (t • v)))=(t^m)⁻¹ • _
  have hT : input su f (M (t • v))=(H (t • v)).1:=by
    unfold input; rw [show arm su f 1 (M (t • v))= X (F (t • v)) from L'.apply_symm_apply _]; exact hz
  rw [hT]
end YM.QCD.Garden
