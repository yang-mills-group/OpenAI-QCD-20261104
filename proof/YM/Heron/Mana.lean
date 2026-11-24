import YM.Heron.Till
import YM.Heron.Vine
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Finset LinearMap
open scoped YM.Massive.Poised.Plans.Stamp
noncomputable local instance (d:ℕ):NormedSpace ℝ (Label d):=NormedSpace.restrictScalars ℝ ℂ _
private lemma seed (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousSMul ℝ V:=inferInstance
noncomputable local instance (d:ℕ) : ContinuousSMul ℝ (Label d) := by exact seed (Label d)
variable {d:ℕ}(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)
abbrev IceT:=Option (Flavor 6)
noncomputable def sectorP (b:IceT)(A:EuPin):EuPin × PClan:=b.elim (bPaneB A) (fun b=> aPaneB b A)
local notation "H"=> Label d
variable (b:IceT)
include hΓ
lemma dvP (p:H):DifferentiableAt ℝ (fun x=>putH (sectorP b (Γ x)) d p) 0 :=by
    refine batter _ p fun L=>?_; cases b; exact gaugeBack Γ Δ hΓ L p.val; exact flit Γ Δ hΓ _ L p.val
noncomputable def Cane (d:ℕ): Label d→ₗ[ℂ] Label d where
 toFun p:= deriv (fun x=>putH (sectorP b (Γ x)) _ p) 0
 map_add' a c:=by simp only[_root_.map_add]; exact deriv_fun_add (dvP Γ Δ hΓ b a) (dvP Γ Δ hΓ b c)
 map_smul' s p:=by simp only[_root_.map_smul,RingHom.id_apply]; exact deriv_const_smul s (dvP Γ Δ hΓ b p)
lemma tCane (p:Label d): HasDerivAt (fun x:ℝ=>putH (sectorP b (Γ x)) _ p) (Cane Γ Δ hΓ b d p) 0 :=(dvP Γ Δ hΓ b p).hasDerivAt
open Massive.Tawny Massive.Tawny.Cast Carnal Perla
noncomputable def yarrow (b:IceT):RawTensor 1 8:= b.elim (-solid) (fun b=> -(1/4:ℂ) • sunS b)
variable (x:Points 2)(hx:x∈conf 2)(χ:E4→ℝ)(hχ: Physics.Window x χ)
include hχ hx
lemma plunge (p q:Label d): plumes x χ Δ (yarrow b).val p.val q.val = ear x (Cane Γ Δ hΓ b d p).val q.val:=by
    have hf :HasDerivAt (fun t:ℝ=> ear x (carr (sectorP b (Γ t)) d p.val) q.val) (plumes x χ Δ (yarrow b).val p.val q.val) 0:=by
        cases b with
        | none =>
           have ht:= carries x hx Δ χ hχ solid.val (fun t=>bPaneB (Γ t)) (-1) (fun p q u v=> (spaceDance x hx Γ Δ hΓ χ hχ p q u v).congr_deriv (by rw [neg_one_mul])) p.val q.val
           apply ht.congr_deriv; let s:=partyR x hx Δ χ hχ p.val q.val; change (-1:ℂ)*s solid.val=s (-solid.val); rw[map_neg,neg_one_mul]
        | some i=>
           let F:=fun t=>aPaneB i (Γ t)
           have ht:= carries x hx Δ χ hχ (sunS i).val F (-(1/4:ℂ)) (fun p q u v=> gust_b x hx Γ Δ hΓ χ hχ p q u v i) p.val q.val
           apply ht.congr_deriv; exact Eq.symm (_root_.map_smul (partyR x hx Δ χ hχ p.val q.val) _ _)
    let L:Label d→L[ℝ]ℂ:= ((tally x q.val ∘ₗ( UV.labels d).subtype).toContinuousLinearMap).restrictScalars ℝ; let G:=fun z:Label d=> ear x z.val q.val; have he : ∀ z, L z=G z:=fun z=> t_eye ..; rw [show ear x (Cane Γ Δ hΓ b d p).val q.val= _ from (he _).symm]; apply hf.unique; apply (L.hasFDerivAt.comp_hasDerivAt 0 (tCane Γ Δ hΓ b p)).congr_of_eventuallyEq; exact Eventually.of_forall fun a=> (he (putH (sectorP b (Γ a)) _ p)).symm
end YM.Heron
#print axioms YM.Heron.Cane
#print axioms YM.Heron.plunge
