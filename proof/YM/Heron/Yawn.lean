import YM.Heron.Array
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable (A:TinG)(hc:TrueC A)(p:E4)(D₀: Faces){U:Set E4}(hU:IsOpen U)(g:Spins)(v:Drive)(χ:E4→ℝ)(hw:Way A U g)(hv:Seam v)(he:tsupport χ⊆U)(hχ:ContDiff ℝ ∞ χ)(Hχ:HasCompactSupport χ)(hp:χ=ᶠ[𝓝 p] fun _=>1)(L:List Axis)
noncomputable def tax(A:TinG)(g:Spins)(v:Drive)(χ:E4→ℝ)(p:E4)(D₀:Faces)(L:List Axis):ℂ:= exportFlux (brook A (pose A D₀ L p) g v) χ
local notation "X"=> twistS A v g
include hw hv
lemma cycleS(y:E4)(hy:y∈U): ContDiffAt ℝ ∞ X y:=by
   have hh:=hw.live y hy; unfold twistS; apply ContDiffAt.add
   · exact ContDiffAt.sum fun i _=> (hv.smooth i).contDiffAt.smul (Maxwell.grad_smooth i hh (by simp))
   refine ContDiffAt.smul (contDiffAt_const (c:=(1/4:ℝ))) (ContDiffAt.sum fun i _=> ContDiffAt.sum fun j _=>?_); exact (gradient_smooth (hv.smooth j) i).contDiffAt.smul ((cog A i).contDiff.contDiffAt.comp _ ((cog A j).contDiff.contDiffAt.comp _ hh))
omit hw hv
lemma germK (f g:Spins)(u:Spins)(x:E4)(hx:f=ᶠ[𝓝 x] g) : ∀ i,brook A f u v i x=brook A g u v i x:=by
    have he:=hx.self_of_nhds; intro i; unfold brook blaze streak; simp_rw [Pi.add_apply]; simp_rw [grad,fun a:Axis=> GermD (basis a) hx, (show f x=g x from he)]
lemma offCost (f g:Spins)(u:Spins)(h:∀ x:E4,x∈tsupport (fderiv ℝ χ)→ f=ᶠ[𝓝 x]g): exportFlux (brook A f u v) χ=exportFlux (brook A g u v) χ:=by
    unfold exportFlux; congr 1; apply Finset.sum_congr rfl; intro i _; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; dsimp only; by_cases he:x∈tsupport (grad i χ); · rw [germK A v f g u x (h x (gradient_part χ i he))]
    rw[image_eq_zero_of_notMem_tsupport he,zero_smul,zero_smul]
include hw hv hc hp he hχ Hχ hU
lemma tones : tax A g v χ p D₀ L = (-4:ℝ) • dotL D₀ (deriveL L X p):=by
    induction L generalizing p with
    | nil=>
        unfold tax; rw[offCost A v χ (pose A D₀ [] p) (bz A p 0 D₀) g (fun x hx=>?_)]
        · exact sourceP A hc p D₀ hU g v χ hw hv he hχ Hχ hp
        have h:x≠p:=fun h=> collar hp (h ▸ hx); filter_upwards [eventually_ne_nhds h] with y hy; exact zeroH A D₀ p y hy.symm
    | cons a L ih =>
        let P:=arcT p a; have hP:P 0=p:=by simp[P,arcT]
        let f:= deriveL L X; have h:DifferentiableAt ℝ f (P 0):=(balla L X U hU (cycleS A g v hw hv) _ (show P 0∈ U from hP.symm ▸ he (enclosed _ hp))).differentiableAt (by simp)
        have he := lineage A p D₀ g v χ L a hw he hχ Hχ hp (hv:=hv)
        apply he.unique; let V:=(-4:ℝ) • dotL D₀
        have ht:= V.hasFDerivAt.comp_hasDerivAt (0:ℝ) (h.hasFDerivAt.comp_hasDerivAt (0:ℝ) (jetX p 0 a));
        refine (ht.congr_deriv (?_)).congr_of_eventuallyEq (?_)
        · change V (fderiv ℝ f (P 0) (basis a))= _; rw [hP]; rfl
        filter_upwards [(show Tendsto P (𝓝 0) (𝓝 p) from (by have ht':Tendsto P (𝓝 0) (𝓝 (P 0)):=(jetX p 0 a).continuousAt; rwa[hP] at ht')) hp.eventuallyEq_nhds] with t ht'; exact ih _ ht'
end YM.Heron
#print axioms YM.Heron.tones
