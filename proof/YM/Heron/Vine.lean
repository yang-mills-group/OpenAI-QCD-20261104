import YM.Heron.Stash
import YM.Cardinal.Radome
import YM.MassiveBridge.Algebraic
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open LinearMap Finset
open Massive.Poised Massive.Poised.Plans
open scoped YM.Massive.Poised.Plans.Stamp
variable {d e:ℕ}(x:Label d)(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(h:EuPin.Path Δ Γ)
-- Split scalars using intrinsic Label.SC contexts
noncomputable local instance (d:ℕ) : NormedSpace ℝ (Label d) := NormedSpace.restrictScalars ℝ ℂ _
local notation "H"=>Label d
local notation "V"=>Pol d
open Massive.Bridge.Spinor
include h
private lemma wrop : DifferentiableAt ℝ (printS ∘ Γ) 0:=by
     have he:DifferentiableAt ℝ (fun x=> (printS (Γ x)).2) 0 := (moss Δ Γ h).prodMk (jenna Δ Γ h false |>.differentiableAt)
     have ht:DifferentiableAt ℝ (fun x=>(printS (Γ x)).1) 0:= differentiableAt_pi.mpr fun a:Axis=> differentiableAt_pi.mpr fun b:Axis=> modesP Δ Γ h b a -- order? modesP a i.
     exact ht.prodMk he
lemma gaugePin(L:Module.Dual ℂ (Pol d))(p:V): DifferentiableAt ℝ (fun t=>L (pinAct (Γ t) p)) 0:=by
     obtain ⟨f,hf,hQ⟩:= Vertex.figures p L
     refine DifferentiableAt.congr_of_eventuallyEq (((hf _).restrictScalars ℝ).comp (0:ℝ) (wrop Γ Δ h)) ?_; exact Eventually.of_forall fun t=> (hQ (Γ t)).symm
-- projector from any q tensor test to unit lamp. basis constant map. 
noncomputable def sil (v:SpinPol d): Pol d→ₗ[ℂ] Pol d:= TensorProduct.map (LinearMap.id) (LinearMap.smulRight (coef ∅) v)
omit h
lemma hil (u:GPol)(v:SpinPol d): sil v (u ⊗ₜ[ℂ] 1)=u⊗ₜ[ℂ] v:=by unfold sil; rw [TensorProduct.map_tmul,LinearMap.smulRight_apply,← show mono (∅:Finset (letters d))=(1:SpinPol d) from mono_empty,Grass.read,one_smul]; rfl
include h
lemma gaugeBack (L:Module.Dual ℂ (Pol d))(p:V): DifferentiableAt ℝ (fun t=> L (carr (bPaneB (Γ t)) d p)) 0:=by
     induction p using TensorProduct.induction_on with
     | zero=> simp
                      [map_zero]
     | tmul x y=>
         have hp(i:EuPin): pinAct i (x⊗ₜ[ℂ](1:SpinPol d))= Labels.rotated i.coord x⊗ₜ[ℂ] (1:SpinPol d):=by rw [← spine_pin,carr,TensorProduct.map_tmul]; exact congr_arg (tmul ℂ (Labels.rotated i.coord x)) (map_one (spun (plainPicture i) _))
         apply (gaugePin Γ Δ h (L ∘ₗ sil y) (x⊗ₜ[ℂ](1:SpinPol d))).congr_of_eventuallyEq; exact Eventually.of_forall fun i=>by dsimp only; rw [hp,LinearMap.comp_apply,pulse_blue,hil]
     | add x y H₁ H₂=> simp_rw [_root_.map_add]; exact H₁.add H₂
lemma flit (u:Flavor 6)(L:Module.Dual ℂ (Pol d))(p:Pol d):DifferentiableAt ℝ (fun t=>L (carr (aPaneB u (Γ t)) d p)) 0:=by
    induction p using TensorProduct.induction_on with
    | zero=>simp [map_zero]
    | tmul x y=> simp_rw [pulse_o]; let P:= L ∘ₗ TensorProduct.mk ℂ _ _ x; exact (P.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp (0:ℝ) (mistB Δ Γ h u y)
    | add x y h h' => simp_rw [_root_.map_add]; exact h.add h'
omit h
lemma batter (f:ℝ→EuPin×PClan)(p:Label d) (h:∀ L:Module.Dual ℂ (Pol d),DifferentiableAt ℝ (fun t=> L (carr (f t) d p.val)) 0): DifferentiableAt ℝ (fun t=> putH (f t) _ p) 0:=by
    letI Hi: Module.Free ℂ (Label d):= Module.Free.of_divisionRing ℂ _
    let B:= Module.finBasis ℂ (Label d)
    let M t:= putH (f t) _ p; change DifferentiableAt ℝ M 0
    rw [show M=(fun t=>∑ i,B.coord i (M t) • B i) from funext fun t=>(B.sum_repr _).symm]; apply DifferentiableAt.fun_sum; intro i _; let P:= (UV.labels d).subtype; choose S hS using LinearMap.exists_leftInverse_of_injective P (LinearMap.ker_eq_bot.mpr (UV.labels d).subtype_injective); let X:=B.coord i ∘ₗ S; have he(r:ℝ):B.coord i (M r)= X (carr (f r) d p.val):=by change _=B.coord i (S (P (M r))); exact congr_arg (B.coord i) (DFunLike.congr_fun hS (M r)).symm
    simp_rw [he]; exact (h X).smul (differentiableAt_const (B i))
end YM.Heron
#print axioms YM.Heron.batter
#print axioms YM.Heron.flit
#print axioms YM.Heron.gaugeBack
