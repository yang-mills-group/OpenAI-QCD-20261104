import YM.Kly.Charm
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
variable (T: FlavorTorus→* (V.H≃ₗᵢ[ℂ] V.H))(hT:∀ p:FlavorTorus,∀ v,T p (V.GNS.plant v)=V.GNS.plant (boat p v))
local notation "Θ"=> P.algebra
variable (p:FlavorTorus)
open OS.Ground (Panes)
variable (S₀:Panes P.algebra)(hS:S₀.Shines (dome V) P.algebra.subtype V.omega0)(hw:∀ f:S₀.X→ℂ,Continuous f→∃ i:P.algebra, f=fun x=> S₀.character x i)
local notation "Ω"=>S₀.X
local notation "Z"=> S₀.character
local notation "Tw"=> twin P T hT
include hT hS
lemma elephant :∃ U:FlavorTorus→* Equiv.Perm Ω,∀ p:FlavorTorus,∀ x:Ω, S₀.character (U p x)=(Z x).comp (twin P T hT p⁻¹):=by
      choose u hu using fun p:FlavorTorus=>fun x:Ω=> hS.onto.2 ((Z x).comp (Tw p⁻¹))
      have he(p q:FlavorTorus)(v):u (p*q) v=u p (u q v):=by
             apply hS.onto.1; rw [hu,hu,hu,mul_inv_rev]; apply DFunLike.ext; intro x; change Z v (Tw _ x)= Z v _; rw[twine]; rfl
      have h(v:Ω):u 1 v=v:=by
             apply hS.onto.1; rw [hu,inv_one]; apply DFunLike.ext; intro x; change Z v (Tw 1 x)=_; rw[town]
      let X(p:FlavorTorus):Equiv.Perm Ω:=⟨u p,u p⁻¹,fun i=>by rw[← he,inv_mul_cancel,h],fun i=>by rw [←he,mul_inv_cancel,h]⟩; refine ⟨⟨⟨X,Equiv.ext h⟩,fun x y=>Equiv.ext (he x y)⟩,hu⟩
lemma tidesA (p:Ω): LipschitzWith 1 (Z p):=by
      haveI:IsClosed (P.algebra:Set V.VacuumOp):= isClosed_closure; letI : CStarAlgebra P.algebra:= StarSubalgebra.cstarAlgebra P.algebra
      apply lipschitzWith_iff_dist_le_mul.mpr; intro x y; rw [NNReal.coe_one,one_mul,dist_eq_norm,dist_eq_norm,←map_sub]; exact NonUnitalStarAlgHom.norm_apply_le _ _ -- types
omit hS hT
lemma sprout {U T E:Type*}[TopologicalSpace T][PseudoMetricSpace U][PseudoMetricSpace E](f:T→ U→E)(h:∀ u:U,Continuous fun t=>f t u)(he:∀ v:T,LipschitzWith 1 (f v)) : Continuous (fun x:T×U=>f x.1 x.2):=by
      apply continuous_iff_continuousAt.mpr; intro x; apply Metric.tendsto_nhds.mpr; intro ε hε; have hT: Continuous (fun v:T×U=> f v.1 x.2):= (h _).comp continuous_fst; filter_upwards [Metric.tendsto_nhds.mp (continuous_snd (X:=T) (Y:=U)|>.continuousAt (x:=x)) (ε/2) (half_pos hε), Metric.tendsto_nhds.mp (hT.continuousAt (x:=x)) (ε/2) (half_pos hε)] with y hy hx; change dist (f _ _) (f _ _) < _; apply lt_of_le_of_lt (dist_triangle _ (f y.1 x.2) _); have hh:dist (f y.1 y.2) (f y.1 x.2) ≤ dist y.2 x.2:=by simpa using (he y.1).dist_le_mul y.2 x.2
      change dist (f _ x.2) (f _ x.2) < _ at hx; exact (add_lt_add (hh.trans_lt hy) hx).trans_le (add_halves ε|>.le)
include P E H Y hT hS
variable (U':FlavorTorus→* Equiv.Perm S₀.X)(hU:∀ p:FlavorTorus,∀ x:S₀.X, S₀.character (U' p x)=(S₀.character x).comp (twin P T hT p⁻¹))
include U' hU
lemma stroll: Continuous fun p:FlavorTorus × S₀.X=> U' p.1 p.2:=by
       let Zq(p:S₀.X)(x:P.algebra):ℂ:= S₀.character p x; have hB: Topology.IsEmbedding Zq:= (Continuous.isClosedEmbedding (continuous_pi fun x=> hS.weak x) (fun i j h=>hS.onto.1 (DFunLike.ext _ _ (congr_fun h)))).isEmbedding
       have hf: Continuous (fun u:S₀.X × P.algebra=> Zq u.1 u.2):= sprout Zq (fun x=>hS.weak x) (fun p=>tidesA P T hT S₀ hS p) -- binder
       apply hB.continuous_iff.mpr; refine continuous_pi fun i=>?_ ; change Continuous fun u:FlavorTorus × S₀.X=> S₀.character _ i; simp_rw [hU]; apply hf.comp (f:= fun u:FlavorTorus×S₀.X=>(u.2,Tw u.1⁻¹ i)); exact continuous_snd.prodMk ((slopes P H Y E T hT i).comp (by fun_prop))
include hw
lemma passports (p: FlavorTorus): MeasurePreserving (U' p) S₀.μ S₀.μ:=by
       have hc:Continuous (U' p):= (stroll P H Y E T hT S₀ hS U' hU).comp (continuous_const.prodMk continuous_id)
       haveI:= hS.normalized; refine ⟨hc.measurable,?_⟩; apply ext_of_forall_integral_eq_of_IsFiniteMeasure; intro f; rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
       let g(x:S₀.X):ℂ:= (f x:ℂ); obtain ⟨y,hg⟩:= hw g (Complex.continuous_ofReal.comp f.continuous)
       apply Complex.ofReal_injective; rw [← integral_complex_ofReal,←integral_complex_ofReal]
       change (∫ x:S₀.X,g (U' p x) ∂S₀.μ)=∫ x:S₀.X,g x ∂S₀.μ; rw[hg]; simp_rw [hU]; change (∫ x,Z x (Tw _ y) ∂S₀.μ)=∫ x,Z x y ∂S₀.μ; rw [hS.ground,hS.ground]; let J:=hartK T hT; let s:= V.omega0
       change inner ℂ s ((sky (J p⁻¹) y.val) s) = inner ℂ s (y.val s); rw [sick, chairP T hT]; nth_rw 1 [show s=J p⁻¹ s from (chairP T hT _).symm]; exact LinearIsometryEquiv.inner_map_map _ _ _
omit hw
lemma reacts (p:FlavorTorus)(b:S₀.X)(x: Pack F): S₀.character (U' p b) (M₀ P (bank p x)) = S₀.character b (M₀ P x):=by rw [hU,mound P H T hT]; change Z b (Tw _ (Tw _ _))=_; rw [←twine,inv_mul_cancel,town]
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.passports
#print axioms YM.Massive.Bridge.Kly.reacts
#print axioms YM.Massive.Bridge.Kly.elephant
