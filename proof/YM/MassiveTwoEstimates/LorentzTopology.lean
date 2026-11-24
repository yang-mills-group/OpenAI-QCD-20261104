import YM.MassiveTwoEstimates.SpinTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Closedness of the proper, future-cone-preserving group and its concrete
spin presentation. These use the topology on the units and their inverses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.LorentzTopology
open Massive Mink QCD.Lat SpinTopology Set
open scoped BigOperators Matrix.Norms.Frobenius

private theorem closedConeMaps : IsClosed {g : General | ∀ x ∈ cone, g.walk x ∈ cone} := by
  have eq : {g : General | ∀ x ∈ cone, g.walk x ∈ cone} =
      {g : General | ∀ x : cone, g.walk x.val ∈ cone} := by
    ext g
    exact ⟨fun h x=>h x.val x.property,fun h x hx=>h ⟨x,hx⟩⟩
  rw [eq]
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  apply closed_cone.preimage
  change Continuous (fun g : General => g.val x.val)
  fun_prop

theorem closedLorentz : IsClosed (Proper : Set General) := by
  let C := {g : General | ∀ x ∈ cone, g.walk x ∈ cone}
  have target : (Proper : Set General) = {g : General | g.stretch=1} ∩
      {g : General | ∀ x, m (g.walk x)=m x} ∩ (C ∩ (fun g : General=>g⁻¹) ⁻¹' C) := by
    ext g
    change (g.stretch=1 ∧ (∀ x, m (g.walk x)=m x) ∧ (∀ x, g.walk x ∈ cone ↔ x ∈ cone)) ↔
      (g.stretch=1 ∧ ∀ x, m (g.walk x)=m x) ∧
        (∀ x ∈ cone, g.walk x ∈ cone) ∧ (∀ x ∈ cone, (g⁻¹).walk x ∈ cone)
    constructor
    · rintro ⟨hd,hm,hc⟩
      refine ⟨⟨hd,hm⟩,fun x hx=>(hc x).mpr hx,fun x hx=>?_⟩
      exact (hc ((g⁻¹).walk x)).mp (by simpa using hx)
    · rintro ⟨⟨hd,hm⟩,hp,hb⟩
      exact ⟨hd,hm,fun x=>⟨fun hx=>by simpa using hb (g.walk x) hx,hp x⟩⟩
  rw [target]
  refine (IsClosed.inter ?_ ?_).inter (closedConeMaps.inter (closedConeMaps.preimage continuous_inv))
  · exact isClosed_eq (ContinuousLinearMap.continuous_det.comp Units.continuous_val) continuous_const
  · rw [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_eq _ continuous_const
    change Continuous (fun g : General=>m (g.val x))
    fun_prop

private theorem continuousWick : Continuous wickSlash := by
  unfold wickSlash
  fun_prop

theorem closedSpin : IsClosed (minkSpinSubgroup : Set (Lorentz × Spikeˣ)) := by
  change IsClosed ({p : Lorentz × Spikeˣ | KeepsC p.2} ∩
    {p | ∀ x, p.2.val*wickSlash x=wickSlash (p.1.act x)*p.2.val})
  apply closedCharge.inter
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq
  · fun_prop
  · have h : Continuous (fun p : Lorentz × Spikeˣ=>p.1.act x) := by fun_prop
    exact (continuousWick.comp h).mul (Units.continuous_val.comp continuous_snd)

def projection : RealSpin →* Lorentz where
  toFun := RealSpin.coord
  map_one' := rfl
  map_mul' _ _ := rfl

theorem realOpenOfSurjective (onto : Function.Surjective RealSpin.coord) :
    IsOpenMap RealSpin.coord := by
  letI : LocallyCompactSpace Lorentz := closedLorentz.locallyCompactSpace
  letI : SigmaCompactSpace General := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  letI : SigmaCompactSpace Lorentz := closedLorentz.sigmaCompactSpace
  letI : SigmaCompactSpace Spike := inferInstanceAs (SigmaCompactSpace (Pinor → Pinor → ℂ))
  letI : SigmaCompactSpace Spikeᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  letI : SigmaCompactSpace Spikeˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  letI : SigmaCompactSpace RealSpin := closedSpin.sigmaCompactSpace
  exact projection.isOpenMap_of_sigmaCompact onto (continuous_fst.comp continuous_subtype_val)

end YM.MassiveTwoEstimates.LorentzTopology
#print axioms YM.MassiveTwoEstimates.LorentzTopology.closedLorentz
#print axioms YM.MassiveTwoEstimates.LorentzTopology.realOpenOfSurjective
