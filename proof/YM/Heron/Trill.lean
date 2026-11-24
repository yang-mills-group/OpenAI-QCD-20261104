import YM.Heron.Trust
import YM.Heron.Mage
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Arise.Range
open Maxwell.Free (fromCenter)
open Finset
variable {d:ℕ}(p:PClan)(B:EuPin)(u:su.El)(g h: EuPin × PClan)
noncomputable def carr (g:EuPin × PClan)(d:ℕ) : Module.End ℂ (Pol d):=TensorProduct.map (Labels.rotated g.1.coord).toLinearMap (spun g.2 d).toLinearMap
lemma carr_times(x:Pol d):carr (g*h) d x=carr g d (carr h d x):=by
     induction x using TensorProduct.induction_on with
     | zero=> simp
     | tmul p q=> simp_rw [carr,TensorProduct.map_tmul,AlgHom.toLinearMap_apply,across]; exact congr_arg₂ (TensorProduct.tmul ℂ) (Labels.rotation_law g.1.coord h.1.coord p) rfl
     | add x y hx hy=> simp only [map_add,hx,hy]
lemma carr_one(x: Pol d) : carr 1 d x=x:=by
     induction x using TensorProduct.induction_on with
     | zero=> simp
     | tmul x y=> unfold carr; rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (burns x) (self_spun y)
     | add x y hx hy=> simp only [map_add,hx,hy]
lemma colorS (x:SpinPol d): spun p d (adapter (colorTable u) (star (colorTable u)).transpose x)=adapter (colorTable u) (star (colorTable u)).transpose (spun p d x):=by unfold spun; rw [adapt_together, adapt_together, (neat p u).eq,(toast p u).eq]
lemma tColor (x:Pol d): colorAct u (carr g d x)=carr g d (colorAct u x):=by
     induction x using TensorProduct.induction_on with
     | zero=> simp
     | tmul x y=> simp_rw [carr,colorAct,TensorProduct.map_tmul, AlgHom.toLinearMap_apply]; exact congr_arg₂ (tmul ℂ) (by apply Labels.eval_ext; intro J; unfold Labels.rotated; simp_rw[Labels.eval_changed]; apply congr_arg (fun J=>Labels.read J x); funext i; exact (Labels.Taylor.turn_paint ..).symm) (colorS g.2 u y).symm
     | add x y hx hy=> simp only [map_add,hx,hy]
lemma murals (x:Label d): carr g d x.val∈labels d:=by
    have H:x.val∈ cap d ⊓ ⨅ t,LinearMap.ker (colorAct t-LinearMap.id):= x.property; change _∈cap d⊓_; apply Submodule.mem_inf.mpr; constructor
    · apply changeCap _ _ _ _ H.1; rintro (i|i) (j|j) hx
      · change tileT g.2 false d i j=0; rw [row_spin]; exact UV.trails _ _ _ _ hx
      · rfl
      · rfl
      change tileT g.2 true d i j=0; rw [row_spin]; exact UV.trails _ _ _ _ hx
    simp only[Submodule.mem_iInf]; intro i
    simp only [Submodule.mem_iInf,Submodule.mem_inf,LinearMap.mem_ker,LinearMap.sub_apply,sub_eq_zero, LinearMap.id_apply] at H; rw [LinearMap.mem_ker,LinearMap.sub_apply,tColor,H.2 i]; exact sub_self _
noncomputable def putH(g:EuPin × PClan)(d:ℕ): Label d≃ₗ[ℂ]Label d :=
  { toFun:=fun x=> ⟨_,murals g x⟩, invFun:=fun x=> ⟨_, murals (g⁻¹) x⟩,
    left_inv:=fun x=>Subtype.ext (Eq.trans (carr_times g⁻¹ g x.val).symm (by rw [inv_mul_cancel,carr_one])),
    right_inv:= fun x=> Subtype.ext (Eq.trans (carr_times g g⁻¹ x.val).symm (by rw [mul_inv_cancel,carr_one])), map_add':=fun x y=>Subtype.ext (map_add (carr g d) x.val y.val),map_smul':=fun a x=>Subtype.ext (map_smul (carr g d) a x.val) }
lemma spine_pin (B:EuPin)(x: Pol d): carr (B,plainPicture B) d x=pinAct B x:=by unfold carr pinAct; rw [pictures] -- pattern issue
noncomputable def maskH (u:Flavor 6)(g:EuPin): PClan:= fun v=> if u=v then g else 1
noncomputable def aPaneB (u: Flavor 6)(p:EuPin):= ((1:EuPin), maskH u p)
noncomputable def bPaneB(p:EuPin):= (p,(1:PClan))
lemma pulse_blue(x:GPol)(v:SpinPol d): carr (bPaneB B) d (x⊗ₜ[ℂ] v)= Labels.rotated B.coord x ⊗ₜ[ℂ]v:=by unfold carr; rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (show _=Labels.rotated B.coord x from rfl) (self_spun v)
lemma pulse_o(u:Flavor 6)(x:GPol)(v:SpinPol d):carr (aPaneB u B) d (x⊗ₜ[ℂ] v)= x⊗ₜ[ℂ]spun (maskH u B) d v:=by unfold carr; rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (burns x) (show _=spun _ _ v from rfl)
lemma mask_one (u:Flavor 6):maskH u 1=1:=by funext i; simp [maskH]
lemma comboMask (v:PClan)(A:EuPin)(d:ℕ):putH (A,v) d=(putH (A,1) d)*(putH (1,v) d):=by
    have h : (A,v)=((A,(1:PClan))*((1:EuPin),v)):=by simp
    ext1; rename_i x; apply Subtype.ext; simp only[LinearEquiv.mul_apply]; change carr (A,v) d x.val= _; conv_lhs=> rw[h,carr_times]
    rfl
end YM.Heron
#print axioms YM.Heron.putH
