import YM.Patria.Cosm
/-! Symmetry in reading. Only origin star/equivs except translations. Translations true all lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Canvas
open Filter Function Set MeasureTheory Lattice Source RG Wilson Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators Topology Matrix ContDiff Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type*} {d k:ℕ}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper
open Poised Beacon Display Finset
variable (s:Signed)(H:TaperHol){c:Side}(p:EuPin)
variable (u:FlavorTorus)(Y:Density c 6)(a:Axis)(hp:p.Lifts s)(hc:18≤ c.val) {P:Density c 6}{L:Label d}
variable (U:Label d)(B:Label d→Density c 6)(ht:Tally H 0 L P Y)
local notation "Δ"=> foil P Y
open Plans Exposure
variable (hB:∀ p:Label d, ActionTest H 0 (B p) p.val)
lemma pulseG (s:Signed): Tendsto (pull (K:=su.El) s (0:Site c)) (𝓝 1) (𝓝 1):=by
    have he := (Wilson.continuous_pull (G:=su) s (0:Site c)).tendsto 1
    rw [show pull (K:=su.El) s 0 (1:Grid c)=1 from funext (fun i=>by simp [pull,Step.read])] at he; exact he
include hp hc ht hB in
lemma hinge (hP:Action.pin p s P=P) (ha:Action.pin p s (B L)= B U): Tally H 0 U P (Action.pin p s Y):=by
    refine linearT H _ _ U B ht (pull s 0) (shipP _ s p) (pulseG s) (fun _ _=>rfl) hP (hB _) (hB _) ha fun j=>?_
    let Z:=adapter (UV.turned (d:=d) p (wave p.matrix⁻¹.val)) (UV.turned p (wave p.matrix.val.transpose)); exact ⟨JQ s j,Z.toLinearMap.toContinuousLinearMap.restrictScalars ℝ,fun _=> funext fun i=>spin_seen s H p i _ j hp hc⟩
include hc ht hB in
lemma swingC (hP:Action.charge P=P) (ha:Action.charge (B L)= B U): Tally H 0 U P (Action.charge Y):=by
    let V(U:Grid c):=conjugate ∘ U; have hv:V 1=1:=funext fun _=>Papyrus.recol_el
    refine linearT H _ _ U B ht V (eveN _) (by have h:= (show Continuous V from TorusPCAC.Geometry.Reflection.grid_cts).tendsto 1; rwa [hv] at h) (fun _ _=>rfl) hP (hB _) (hB _) ha fun j=>?_
    exact ⟨_,(changeVars (masq d)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ,fun _=>funext fun i=> charge_seen H i _ _ hc⟩
include ht hB
lemma arrows (hP:Action.flavor u P=P)(ha:Action.flavor u (B L)= B U): Tally H 0 U P (Action.flavor u Y):=by
    refine linearT H _ _ U B ht id (stroll _ u) tendsto_id (fun _ _=>rfl) hP (hB _) (hB _) ha fun j=>?_
    let T:= adapter (byFlavor u (fun i:SpinMode d=>i.2)) (byFlavor u⁻¹ (fun i:SpinMode d=>i.2)); exact ⟨j,T.toLinearMap.toContinuousLinearMap.restrictScalars ℝ,fun _=>funext fun i=> slash_pig ..⟩
lemma hingeP (hP:Action.parity P=P)(ha:Action.parity (B L)= B U): Tally H 0 U P (Action.parity Y):=by
    refine linearT H _ _ U B ht id grade tendsto_id (fun _ _=>rfl) hP (hB _) (hB _) ha fun j=>?_; exact ⟨j,(grade (A:=Pairs (SpinMode d))).toLinearMap.toContinuousLinearMap.restrictScalars ℝ,fun _=> funext fun i=>grade_seen ..⟩
include hc
-- multiply by unmarked even on right.Commutation verified.
lemma flux (he:Action.adj a P=P)(hf:Action.parity P=P)(h:Action.adj a (B L)= B U): Tally H 0 U P (Action.adj a Y):=by
    let C:= tilt (eyeP c a); let V:= pull (K:=su.El) (Signed.mirror a) (0:Site c)
    apply grouping H Y (Action.adj a) U B ht _ (hB _) (hB _) h _ _
    · filter_upwards [ht.unit,(pulseG _).eventually ht.unit] with x hx hh; refine (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hx).mpr ?_; let g:= foil P Y; let p:=g (V x); have hQ: Plus (P x):=congr_fun hf x; rw [(hQ.central _).eq.symm,eye_value,eye_value]; change C (Y (V x)) = C (g (V x))*P x; have hs:P x=C (P (V x)):= (congr_fun he x).symm.trans (eye_value ..); rw [hs,show C (g (V x))*C (P (V x))=C (P (V x)*p) from (tilt_mul ..).symm]; exact congr_arg C (Ring.mul_inverse_cancel_left _ _ hh).symm
    · intro i j; funext x; rw [Pi.sub_apply,eye_value,eye_value,eye_value, Pi.sub_apply,map_sub]
    intro J; let Z:SpinPol d →ₗ[ℝ] SpinPol d:= { toFun:= aSpin d a,map_add':=map_add _,map_smul':=fun c x=>by change aSpin d a ((c:ℂ) • x)=_; rw [map_smulₛₗ, Complex.conj_ofReal]; rfl}; exact ⟨JQ (Signed.mirror a) J,Z.toContinuousLinearMap,fun _=> funext fun i=>eye_seen H i _ J a hc⟩
end YM.Massive.Patria.Canvas
#print axioms YM.Massive.Patria.Canvas.hinge
#print axioms YM.Massive.Patria.Canvas.flux
