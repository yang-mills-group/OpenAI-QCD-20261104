import YM.Kauri.Ave
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace Matrix.Norms.Frobenius
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
variable (g u:Skew)(Δ:ℝ→EuPin)(h:EuPin.Path g Δ)(x:BoxD)
local notation "B"=> pulseB.toBasis
include h
lemma scored (a b:Axis): HasDerivAt (fun t:ℝ=>(Δ t).coord.val a b) (g.val a b) 0:=by
      have he:=Work.A13.hasDerivAt_coord g (basis b) a 0
      simp only[Ortho.move,M4.move_basis] at he; rw [oneParameter_zero,show (1:Ortho).val=(1:M4) from rfl, M4.move_one,M4.move_basis] at he; simp_rw[h.2.2]; exact he
lemma slipped : HasDerivAt (fun t:ℝ=> dues (Δ t) x) (stall g x) 0:=by
      have hg(a b:Axis): HasDerivAt (fun t:ℝ=> dues (Δ t) (B (a,b))) (stall g (B (a,b))) 0:=by
           simp_rw [show ∀ p:EuPin,dues p (B (a,b))= troopL p _ from fun i=> rfl,sol];
           let f (i j:Axis)(t:ℝ):ℂ:= ↑((Δ t).coord.val i a*(Δ t).coord.val j b)
           let v(i j:Axis):ℂ:= ↑(g.val i a*(1:M4) j b+ (1:M4) i a*g.val j b)
           have ht(i j:Axis): HasDerivAt (f i j) (v i j) 0:=by
                  have he:= ((scored g Δ h i a).fun_mul (scored g Δ h j b)); apply (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 he).congr_deriv; unfold v; rw[h.1]; rfl
           let Z:= (∑ i:Axis, ∑ j:Axis,v i j • B (i,j))
           have hp: HasDerivAt (fun t=>∑ i:Axis,∑ j:Axis, f i j t • B (i,j)) Z 0:= HasDerivAt.fun_sum fun i _=> HasDerivAt.fun_sum fun j _=> (ht i j).smul_const _
           refine hp.congr_deriv ?_; unfold Z v; rw [stave]; simp [Matrix.one_apply,mul_ite,ite_mul,ite_smul,add_smul,Finset.sum_add_distrib]
      rw [←pulseB.toBasis.sum_repr x]; simp only [map_sum,map_smul]; exact HasDerivAt.fun_sum fun i _=>(hg i.1 i.2).const_smul (pulseB.toBasis.repr x i)
lemma d_stall (r:ℝ) : HasDerivAt (fun t=> dues (Δ t) x) (stall g (dues (Δ r) x)) r:=by
      apply (sidle (slipped g Δ h (dues (Δ r) x)) r).congr_of_eventuallyEq; apply Eventually.of_forall; intro t; simp_rw[←LinearEquiv.mul_apply,←map_mul,← SpinParity.additive h,sub_add_cancel]
omit h
lemma stub(g:EuPin): stall (Mako.conjSkew g.coord u) (dues g x)= dues g (stall u x):=by
     let f:=fun t:ℝ=>g*oathU u t*g⁻¹; let K:=conjSkew g.coord u; let L:= (dues g).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; apply (slipped K f (Mako.conjug u _ (tour u) g) (dues g x)).unique; apply (L.hasFDerivAt.comp_hasDerivAt 0 (slipped u (oathU u) (tour u) x)).congr_of_eventuallyEq; apply Eventually.of_forall; intro i; change dues (f i) (dues g x)= dues g (dues (oathU u i) x); rw[←LinearEquiv.mul_apply,←LinearEquiv.mul_apply, ←map_mul,←map_mul]; simp [f,mul_assoc]
def braille : Skew→L[ℝ] (BoxD →L[ℝ] BoxD):= LinearMap.toContinuousLinearMap { toFun:=fun p:Skew=> (LinearMap.toContinuousLinearMap (stall p)).restrictScalars ℝ
                                                                              map_add':=fun p q=>by apply ContinuousLinearMap.ext; intro z; change stall (p+q) z=_; rw[dome]; rfl
                                                                              map_smul':=fun p q=>by apply ContinuousLinearMap.ext; intro z; change stall (p • q) z =_; rw[sal]; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) p (stall q z)).symm }
lemma stalk : clip (stall g) (stall u)= stall (Org.bracket g u):=by
      apply LinearMap.ext; intro z; exact Mako.comet braille dues (fun p x=>slipped p (oathU p) (tour p) x) stub g u z
end YM.Kauri
#print axioms YM.Kauri.d_stall
#print axioms YM.Kauri.stalk
