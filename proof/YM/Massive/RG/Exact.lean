import YM.Massive.Target.Tower
import YM.QCD.Cedar.Canopy
import YM.Push.BETA_TRANSPORT.Block
import YM.Branch.Covariant

/-!
# Actual RG, any flight

Spacing indices may vary as specified in Tower; holds for the full finite
Wilson/Grass algebra even on insertion of odd fields (all the transfers here
also apply to odd densities). All continuity/measurability statements about
steps are on native, finite tori. Normalization statements are relative to
the *chosen* positive starting density mass, not obtained by assuming
positivity of the gauge marginal on the way.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Grass QCD.Lat Lattice Wilson MeasureTheory Function Filter RG
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace Transfer

variable {j k F : ℕ} {c f : Side}
variable (P : Flight j k) (K : KernelChoices) (h : f.val=c.val*P.L.val)
variable (β w : ℝ)
local notation "S" => coarse P K h
variable (hk : P.patch.Branches K su)

-- complex parameter-independent pointwise linear laws
lemma soften_add (x y : Density f F) : soften P h (x+y) = soften P h x + soften P h y := by
  funext U
  unfold soften Kit.sheath; simp only [Pi.add_apply,map_add,add_mul, smul_add]

lemma soften_smul (x : Density f F) (z : ℂ) : soften P h (z • x) = z • soften P h x := by
  funext U
  unfold soften Kit.sheath; simp [smul_comm]

-- analytic obligations in boolean mask/selector kernel: pinned *same* choices and hypotheses
include hk
lemma kernel : (coarse P K h).IsKernel β su := StepData.isKernel _ hk _

omit hk
lemma soften_continuous {x : Density f F} (hx : Continuous x) : Continuous (soften P h x) := by
  have hc : Continuous (fun U : Grid f => Kit.choir F (Flume.tied P h 0 U)) :=
    (Kit.choir_cont (A:=Row c) (B:=Row f) F).comp (Pine.tied_cont P h 0)
  change Continuous ((fun t : Matrix (Modes c F) (Modes f F) ℂ × Fields f F => Kit.sheath 1 t.1 t.2) ∘ fun U => (Kit.choir F (Flume.tied P h 0 U),x U))
  exact (Kit.sheath_cont (A:=Modes f F) (B:=Modes c F) (b:=1)).comp
    (hc.prodMk hx)

lemma soften_pay {x : Density f F} (hx : Continuous x) : Integrable (soften P h x) (prior su f) :=
  (soften_continuous P h hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hk
lemma push_continuous (x : Grid f → Fields c F) (hx : Integrable x (prior su f)) :
    Continuous ((coarse P K h).push β x) := by
    rw [continuous_iff_continuousAt]; intro i; rw [← continuousWithinAt_univ]
    exact (Push.BetaTransport.push_continuousWithinAt S hk (b:=fun _=>β) (y:=i) continuousWithinAt_const continuousWithinAt_id
      (V:=id) (F:=fun _=>x) hx (Eventually.of_forall fun _=> hx.1) (ae_of_all _ fun _=> continuousWithinAt_const)
        hx.norm (Eventually.of_forall fun _=> ae_of_all _ fun _=> le_rfl)).2

theorem continuous {x : Density f F} (hx : Continuous x) : Continuous (transfer P K h β w x) :=
  (rescale w (F:=F) (c:=c)).toLinearMap.continuous_of_finiteDimensional.comp
    (push_continuous P K h β hk _ (soften_pay P h hx))

def up (x : Insertion f F) : Insertion c F :=
  ⟨transfer P K h β w x,continuous P K h β w hk x.continuous⟩ -- R.w

lemma linear (x y : Insertion f F) : up P K h β w hk (x+y) = up P K h β w hk x + up P K h β w hk y := by
    ext1 i
    change rescale w ((S).push β (soften P h (⇑x+⇑y)) i)=_+_
    rw [soften_add,StepData.push_add (kernel P K h β hk) _ _ (soften_pay P h x.continuous) (soften_pay P h y.continuous),Pi.add_apply,map_add]; rfl

lemma complex_smul (x : Insertion f F) (z : ℂ) : up P K h β w hk (z • x) = z • up P K h β w hk x := by
    ext1 i; change rescale w ((S).push β (soften P h (z • ⇑x)) i)= _; rw [soften_smul];
    unfold StepData.push; simp only [Pi.smul_apply,ContinuousMap.smul_apply];
    -- rw under integral
    simp_rw [smul_comm _ z, integral_smul,map_smul]; rfl

/-- exact linear transport -/
def blockMap : Insertion f F →ₗ[ℂ] Insertion c F where
    toFun := up P K h β w hk
    map_add' := linear P K h β w hk
    map_smul' := fun z x => complex_smul P K h β w hk x z

omit hk

/-- w multiplier at the step, never used without an integrable kernel. -/
def growth (c : Side) (F : ℕ) (w : ℝ) : ℂ := (w:ℂ)^(Fintype.card (Pairs (Modes c F)))

lemma volumeScale (x : Fields c F) : ber (Modes c F) (rescale w x)= growth c F w * ber _ x := by
  classical
  unfold rescale; rw [ber_rows,Matrix.det_diagonal]; congr 1; simp [growth]

include hk

/-- Conservation of every unnormalized globally inserted expectation. -/
theorem conserves (x : Density f F) (ht : Integrable (soften P h x) (prior su f)) :
    joint (transfer P K h β w x) = growth c F w * joint x := by
    let y := soften P h x
    have he := (S).push_integrable (kernel P K h β hk) y ht
    let W : Fields c F →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (ber _)
    unfold joint transfer
    simp only [Function.comp_apply,volumeScale,integral_const_mul]
    congr 1; change (∫ V, W ((S).push β y V) ∂prior su c) = _
    rw [W.integral_comp_comm he,StepData.push_integral (kernel P K h β hk) y ht, ← W.integral_comp_comm ht]
    exact integral_congr_ae (ae_of_all _ fun i => Kit.insulate one_ne_zero _ _)

end Transfer
end YM.Massive
