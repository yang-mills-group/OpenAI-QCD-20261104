import YM.MassiveBridge.SpinStar
import YM.Mako.Matte
import YM.Next.MAXWELL.Quarters
import YM.Kly.River
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Mako MassiveTwoEstimates Set Function Filter Analysis Mink Spinor Lift
open Fields (pointMoment distinct)
open OS (Cross)
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix Matrix.Norms.Frobenius ComplexOrder
local notation "D"=> daylight
local notation "d₀"=> timeAxis
abbrev thetaR:=Signed.reflect timeAxis
noncomputable def GenH :Subgroup Ortho:=Subgroup.closure {t:Ortho | ∃ (i:SpaceAxis)(r:ℝ), t=(daylight i r).coord}
variable (p:Ortho)
lemma memG (i:SpaceAxis)(r:ℝ):(daylight i r).coord∈GenH:=Subgroup.subset_closure (show _ from ⟨i,r,rfl⟩)
set_option quotPrecheck false
local notation "A" i:arg r:arg=> (daylight i r).coord
lemma mirM : thetaR*thetaR=1:= map_mul (Signed.inclusionO) (Signed.mirror timeAxis) (Signed.mirror timeAxis) |>.symm.trans (by rw [show Signed.mirror timeAxis*Signed.mirror timeAxis =1 from inv_mul_cancel _,map_one])
lemma mirI : thetaR⁻¹=thetaR:= (eq_inv_of_mul_eq_one_left mirM).symm
lemma pivot (i:SpaceAxis)(r:ℝ): thetaR*A i r*thetaR⁻¹ = (A i r)⁻¹:=by
      have he:=way i; let J:=Ortho.plane timeAxis i.castSucc
      have h:Mako.conjSkew thetaR J= -J:=by
            let s:=Signed.mirror timeAxis; change Org.orients s (Ortho.plane timeAxis i.castSucc)=_; rw[Maxwell.Free.Corners.bracket_orient]; simp [s,J,Signed.mirror,Ne.symm (Fin.castSucc_ne_last i)]; exact neg_one_smul ℝ (Ortho.plane d₀ i.castSucc)
      rw[he.2.2 r,← Mako.oneParameter_conj,h]; -- exp inverse
      apply Subtype.ext; change NormedSpace.exp (r • (-J).val)=_; have hu:A i (-r) = (A i r)⁻¹:= (congr_arg EuPin.coord (Mako.curve_i he r)) -- defeq
      rw [he.2.2 _,he.2.2 _] at hu; refine Eq.trans ?_ (congr_arg Subtype.val hu); change _=NormedSpace.exp ((-r) • J.val); apply congr_arg; exact (smul_neg r J.val).trans (neg_smul r J.val).symm
lemma normalR(h:p∈GenH): thetaR*p*thetaR ∈ GenH:=by
    induction h using Subgroup.closure_induction with
    | mem t h=>
        obtain ⟨i,r,rfl⟩:=h
        have h:= pivot i r; rw [mirI] at h; exact h ▸ GenH.inv_mem (memG i r)
    | one=>rw[mul_one,mirM]; exact GenH.one_mem
    | mul x y hx hy h1 h2=>
          have he:(thetaR*x*thetaR)*(thetaR*y*thetaR)=thetaR*(x*y)*thetaR:=by simp only [mul_assoc]; rw [← mul_assoc thetaR thetaR,mirM, one_mul]
          rw [← he]; exact GenH.mul_mem h1 h2
    | inv x hx h=>
          rw[show thetaR*x⁻¹*thetaR=(thetaR*x*thetaR)⁻¹ from (by simp [mul_assoc,mirI])]; exact GenH.inv_mem h
-- squash always pivot time: only time planes.
lemma squashT(v:E4)(s:Finset Axis)(h:d₀ ∉ s):∃ p∈GenH,∀ j∈ s, Ortho.move p v j=0:=by
    induction s using Finset.induction_on with
    | empty=> exact ⟨1,GenH.one_mem, by simp⟩
    | @insert j s hj ih=>
      obtain ⟨hij,his⟩:= (show d₀≠j ∧ d₀∉ s by simpa using h)
      obtain ⟨b,hb,ht⟩:= ih his; obtain ⟨t,hT⟩:= Work.A13.plane_eliminates hij (Ortho.move b v); let r:=Ortho.oneParameter (Ortho.plane d₀ j) t
      have hr:r∈GenH:=by
           rcases Fin.eq_castSucc_or_eq_last j with ⟨i,hx⟩|hx; · unfold r; rw [hx]; exact (Lift.way i).2.2 t ▸ memG i t
           exact False.elim (hij hx.symm)
      refine ⟨r*b,GenH.mul_mem hr hb, fun k hk=>?_⟩; rw[Ortho.move_mul]; rcases Finset.mem_insert.mp hk with H|hk; rw[H]; exact hT
      exact ((Work.A13.plane_givens hij (Ortho.move b v) t).2.2 k (fun he=> his (he ▸ hk)) (fun he=>hj (he ▸ hk))).trans (ht _ hk)
abbrev hyp(v:E4):= (ℝ ∙ v)ᗮ.reflection
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.normalR
#print axioms YM.Massive.Bridge.Kly.squashT
