import YM.Kly.Cape
import YM.Work.B09.Shell
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
local notation "G"=> bloom P H X'
variable {s:E4}{d:ℝ≥0}{χ:E4→ℝ}
open Work.B09 MeasureTheory Lift
include H
lemma presume(h:Padded s d x) : Points.across s x∈region t₀ d n:= ⟨h.1,Points.across_in s h.2.1,h.2.2⟩
omit H
-- integrate pay meter closure via subtype codRestrict.
variable {y:Points (n+1)}(q:Fin (n+2) → F.W)
variable (hχ:∀ y∈tsupport χ, InsideTimes s d y)(k:Physics.Window y χ)
variable (hy:Padded s d y)(p:E4→ℂ)(hp:Continuous p)(i:Axis)
noncomputable def filled (i:Axis)(χ:E4→ℝ)(z:E4→ℂ)(s:E4)(d:ℝ≥0)(q:Fin (n+2)→F.W)(x:Points (n+1))(p:E4):V.H.Op:= Work.B09.weight χ i z p • mac P q s d (Points.cons p x)
include hχ k H Y E hp hy
lemma fillP : Continuous (filled P i χ p s d q y)∧HasCompactSupport (filled P i χ p s d q y) :=by
    let f:=filled P i χ p s d q y; change Continuous f∧HasCompactSupport f
    have hu : Table.Window y χ:=k; have ht(y:E4):Continuous (Work.B09.weight χ i p):= Continuous.mul (Complex.continuous_ofReal.comp (show Continuous (D (basis i) χ) from continuous_iff_continuousAt.mpr (fun t=>(dSmooth (hu.1.contDiffAt (x:=t)) (basis i) (m:=∞) (by simp)).continuousAt))) hp
    constructor
    · apply continuous_iff_continuousAt.mpr; intro x; by_cases he:x∈tsupport (Work.B09.weight χ i p)
      · let z:= Points.cons x y; have hy:= Work.B09.padded_shell hu hy hχ he; let T(t:E4):= Points.cons t y; have hh:Continuous T:=by
              have hT : Continuous (fun w : E4 => (Fin.cons (α := fun _ : Fin (n+2) => E4) w y.ofLp)) := continuous_pi fun k => Fin.cases (by simp; exact continuous_id) (fun j => by simp; exact continuous_const) k
              exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp hT
        have hz: ContinuousAt (mac P q s d) z:= (cont_place P Y E d q (presume H _ hy)).comp (f:=Points.across s) (x:=z) (acc z s).continuous.continuousAt; exact (ht x).continuousAt.smul (hz.comp (f:=T) (x:=x) (hh.continuousAt))
      exact continuousAt_const.congr (show (fun _ : E4=> (0:V.H.Op))=ᶠ[𝓝 x] f from by filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with i hi; change 0= _ • _; rw[show _= (0:ℂ) from hi,zero_smul])
    apply HasCompactSupport.intro hu.2.1; intro x hx; have ha:x∉ tsupport (Work.B09.weight χ i p):=fun h=> hx (Work.B09.weight_within h); change _ • _= 0; rw [image_eq_zero_of_notMem_tsupport ha,zero_smul]
omit hp E Y k hy hχ H
-- integrable.P returns plus agreement with compressed operator and evaluation
include H Y E k hp hy hχ
local notation "I"=> filled P i χ p s d q y
noncomputable abbrev subt (P:Spread V) : P.algebra→L[ℂ] V.VacuumOp:=
      {P.algebra.subtype.toAlgHom.toLinearMap with cont:= continuous_subtype_val } -- type instance CStar on norm
lemma inAlgebra : Cpr (V:=V) (∫ t, I t) ∈ P.algebra:=by
     have hc:IsClosed (P.algebra:Set V.VacuumOp):= isClosed_closure; haveI :IsClosed (P.algebra:Set V.VacuumOp):= hc
     letI:CStarAlgebra P.algebra:= StarSubalgebra.cstarAlgebra P.algebra; let L:=Cpr (V:=V); obtain ⟨hV,hJ⟩:= fillP P H Y E q hχ k hy p hp i
     have hb(t:E4) : L (filled P i χ p s d q y t)∈ P.algebra:=by
           by_cases ht:t∈ tsupport (weight χ i p)
           · have he:= padded_shell (show Table.Window _ _ from k) hy hχ ht; unfold L filled; rw [map_smul,←activeM P H _ q s d he.2.1 (presume H _ he)]; exact (P.algebra).smul_mem (Subtype.property _) _ -- order
           unfold filled; rw[image_eq_zero_of_notMem_tsupport ht,zero_smul,map_zero]; exact (P.algebra).zero_mem
     let W(t:E4):↥P.algebra:= ⟨_,hb t⟩; have hT:Continuous W:= (L.continuous.comp hV).subtype_mk _; have hm: HasCompactSupport W:= HasCompactSupport.intro hJ (fun t ht=> Subtype.ext (show L _= 0 from (congr_arg L (image_eq_zero_of_notMem_tsupport ht)).trans (map_zero L)))
     let f:P.algebra→L[ℂ] V.VacuumOp:= {P.algebra.subtype.toAlgHom.toLinearMap with cont:= continuous_subtype_val}; rw [show Cpr (V:=V)=L from rfl,show L (∫ t, I t)=(∫ t:E4,L (I t)) from (ContinuousLinearMap.integral_comp_comm (E:=V.H.Op) (Fₗ:=V.VacuumOp) (μ:=volume) (𝕜:=ℂ) L (hV.integrable_of_hasCompactSupport hJ)).symm]; rw[show (fun t=> _)= (fun t=> f (W t)) from (?_ : (fun t:E4=>L (filled P i χ p s d q y t)) = fun t:E4=> f (W t))]; have hp:(∫ t:E4,f (W t)) = f (∫ t:E4,W t):= ContinuousLinearMap.integral_comp_comm (E:=P.algebra) (Fₗ:=V.VacuumOp) (μ:=volume) (𝕜:=ℂ) f (hT.integrable_of_hasCompactSupport hm); rw [hp]; exact Subtype.property (∫ t,W t); rfl
lemma march_f (Z:V.H.Op→L[ℂ]ℂ)(u:E4→ℂ)(hv:∀ t, t∈tsupport (weight χ i p)→ Z (mac P q s d (Points.cons t y))=u t) : Integrable (fun t=> weight χ i p t*u t) ∧ Z (∫ t,I t)= ∫ t,weight χ i p t*u t:=by
      obtain ⟨h,hv'⟩:= fillP P H Y E q hχ k hy p hp i; have hf:(fun t=> Z (I t))=(fun t=>weight χ i p t*u t):=by
            funext t; unfold filled; rw [map_smul,smul_eq_mul]; by_cases ht :t∈tsupport (weight χ i p); · rw[hv t ht]
            rw [image_eq_zero_of_notMem_tsupport ht,zero_mul,zero_mul]
      rw[← hf]; exact ⟨(Z.continuous.comp h).integrable_of_hasCompactSupport (HasCompactSupport.intro hv' (fun t ht=>(congr_arg Z (image_eq_zero_of_notMem_tsupport ht)).trans (map_zero _))), (Z.integral_comp_comm (h.integrable_of_hasCompactSupport hv')).symm⟩
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.inAlgebra
#print axioms YM.Massive.Bridge.Kly.march_f
