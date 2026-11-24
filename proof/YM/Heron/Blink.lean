import YM.Heron.Yalta
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable (A:TinG)(hc:TrueC A){g f:Spins}
theorem sacred {x:E4}
    (H : Way (FlipT A) ({x}ᶜ) f) (K : Way A ({x}ᶜ) g)
    {χ ψ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (Hχ : HasCompactSupport χ) (Hψ : HasCompactSupport ψ)
    (hx : χ =ᶠ[𝓝 x] fun _ => 1) (hp : ψ =ᶠ[𝓝 x] fun _ => 1)
    {v : Drive} (hv : Seam v)(hA:TrueC A) : exportFlux (brook A f g v) χ = exportFlux (brook A f g v) ψ := by
  have he : tsupport (χ-ψ) ⊆ {x}ᶜ := by
    have ht : (χ-ψ) =ᶠ[𝓝 x] 0 := by filter_upwards [hx,hp] with y hy hy'; simp [hy,hy']
    have hq : x ∉ tsupport (χ-ψ) := notMem_tsupport_iff_eventuallyEq.mpr ht
    exact fun y hy h => hq ((show y=x from h) ▸ hy)
  have hy := zeroFlux A hv isOpen_compl_singleton (hχ.sub hψ) (Hχ.sub Hψ) he H K hA
  have ht {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
      (hx : χ =ᶠ[𝓝 x] fun _ => 1) (a : Axis) :
      Integrable fun y => grad a χ y • brook A f g v a y := by
    refine shell_cost hχ Hχ ?_ a; intro y hy
    have he : y ∈ ({x}:Set E4)ᶜ := fun he : y=x => collar hx (he ▸ hy)
    exact (bow A a g f y v hv (H.live y he) (K.live y he)).continuousAt
  have hf (a : Axis) (y) : grad a (χ-ψ) y = grad a χ y - grad a ψ y := grad_dif
    (hχ.differentiable (by simp) y) (hψ.differentiable (by simp) y) _
  unfold exportFlux at *
  have hl (a : Axis) (y : E4) : grad a (χ-ψ) y • brook A f g v a y =
      grad a χ y • brook A f g v a y - grad a ψ y • brook A f g v a y := by rw [hf,sub_smul]
  change -(∑ a : Axis, ∫ y : E4, grad a (χ-ψ) y • brook A f g v a y)=0 at hy
  simp_rw [hl] at hy
  simp_rw [integral_sub (ht hχ Hχ hx _) (ht hψ Hψ hp _), Finset.sum_sub_distrib,
    neg_eq_zero,sub_eq_zero] at hy
  rw [hy]
variable {x : E4} {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
    (hx : χ =ᶠ[𝓝 x] fun _ => 1) {v : Drive} (h : Seam v)
    (H : ∀ (t:ℝ), 0<t → ∀ i:Axis, ∀ z:E4, v i (x+t • z)=t*v i (x+z))
    (p q: List Axis)(d e: Faces)
local notation "L"=>pose A d p x
local notation "R" => pose (FlipT A) e q x
include hχ Hχ hx h H hc
lemma two_suns : exportFlux (brook A L R v) χ=0:=by
  let f:= pose A d p x; let g:=pose (FlipT A) e q x; let w:=brook A f g v; let t:ℝ:=2; have ht:0<t:=by norm_num [t]
  let u:= Units.mk0 t ht.ne'; let s:= ((Homeomorph.addRight (-x)).trans (Homeomorph.smul u⁻¹)).trans (Homeomorph.addLeft x)
  have hs(z:E4):s z=x+t⁻¹ • (z-x):=by simp [s,u,sub_eq_add_neg]; rfl
  let ψ := χ ∘s; have hp : ContDiff ℝ ∞ ψ := by
    have hh : ContDiff ℝ ∞ (s : E4 → E4) := by rw [funext hs]; fun_prop
    exact hχ.comp hh
  have hψ : ψ =ᶠ[𝓝 x] fun _ => 1 := by
    have ha := s.continuous.continuousAt (x := x) |>.tendsto; rw [hs,sub_self,smul_zero,add_zero] at ha; exact ha hx
  have hg: Way A ({x}ᶜ) g:=by
     have he:= care (FlipT A) e (flips A hc) x q; change Way (FlipT (FlipT A)) _ g at he; rw [show FlipT (FlipT A)= A from rfl] at he; exact he
  have hf : Way (FlipT A) ({x}ᶜ) f:= care A d hc x p
  have he:= sacred A hf hg hχ hp Hχ (Hχ.comp_homeomorph s) hx hψ h hc
  let Dp:= t⁻¹^(3+p.length); let Dq:= t⁻¹^(3+q.length); let S:=t⁻¹*Dp*Dq; let C:=t^3*t*S
  have heq (a : Axis) (z:E4) : t^4 • (grad a ψ (x+t • z) • w a (x+t • z)) = C • (grad a χ (x+z) • w a (x+z)) :=by
      by_cases hz:z=0
      · subst z
        rw [smul_zero,add_zero,image_eq_zero_of_notMem_tsupport
          (f := grad a ψ) (x:=x) (fun he => collar hψ (gradient_part ψ a he)),
          image_eq_zero_of_notMem_tsupport (f := grad a χ) (x:=x) (fun he => collar hx (gradient_part χ a he))]; simp
      have hh (a : Axis) : grad a ψ (x+t • z) = t⁻¹ * grad a χ (x+z) := by
        have hj : s (x+t • z) = x+z := by simp [hs,inv_smul_smul₀ ht.ne']
        have hg : HasFDerivAt (s : E4 → E4) (t⁻¹ • ContinuousLinearMap.id ℝ E4) (x+t • z) := by
          rw [funext hs]; exact (((hasFDerivAt_id _).sub_const x).const_smul t⁻¹).const_add x
        unfold grad D ψ; rw [fderiv_comp _ (hχ.differentiable (by simp) _) hg.differentiableAt,hg.fderiv,hj]
        exact map_smul (fderiv ℝ χ _) t⁻¹ _
      have hi(a b:Axis): streak A f g a b (x+t • z)= S • streak A f g a b (x+z):=by
          unfold f g S Dp Dq streak; simp only[grace _ _ _ _ ht _ z hz,touchS _ _ _ _ ht _ z hz,_root_.map_smul, ContinuousLinearMap.smul_apply]; module -- try
      simp_rw [hh a,w,brook,H t ht,blaze, Pi.add_apply,hi]; unfold C t; simp only[Finset.smul_sum]; refine Finset.sum_congr rfl fun _ _=>?_ ; module
  have hh(a:Axis) : (∫ y:E4,grad a ψ y • w a y) = C • ∫ y:E4, grad a χ y • w a y :=by
      rw [dilate_integral (fun y:E4=>grad a ψ y • w a y) x t ht, ← integral_smul]
      rw [show (fun y:E4=> (t^4) • (grad a ψ (x+t • y) • w a (x+t • y)))= (fun y=> C • (grad a χ (x+y) • w a (x+y))) from funext (heq a), integral_smul,
         integral_add_left_eq_self (fun y => grad a χ y • w a y) x]
  let Z:= exportFlux w χ; have hz:Z=C • Z:= he.trans (show exportFlux w ψ=C • Z from (by unfold exportFlux; simp_rw [hh, ← Finset.smul_sum]; rw[← smul_neg]; rfl))
  have hlt:C<1:=by
      have hj:Dp≤t⁻¹^3:= pow_le_pow_of_le_one (by positivity) (by norm_num [t]) (by omega)
      have hk:Dq≤t⁻¹^3:=pow_le_pow_of_le_one (by positivity) (by norm_num [t]) (by omega); unfold C S; calc
      _ ≤ t^3*t*(t⁻¹*t⁻¹^3*t⁻¹^3):=by gcongr
      _ < _:= by norm_num [t]
  exact (smul_eq_zero.mp (show ((1:ℝ)-C) • Z=0 from (by rw[sub_smul,one_smul,← hz, sub_self]))).resolve_left (by linarith)
end YM.Heron
#print axioms YM.Heron.two_suns
