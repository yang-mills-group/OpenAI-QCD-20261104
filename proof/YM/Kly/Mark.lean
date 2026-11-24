import YM.Kly.Tuna
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
open Work.A13
lemma tAlign (v : E4) :
    ∃ g ∈ GenH, ∃ c : ℝ, Ortho.move g v = c • basis timeAxis := by
  obtain ⟨g, hg, hall⟩ := squashT v (Finset.univ.erase timeAxis) (by simp)
  refine ⟨g, hg, Ortho.move g v timeAxis, PiLp.ext ?_⟩
  intro k
  by_cases h : k = timeAxis
  · subst k; simp
  simp [h, hall k (by simp [h])]

lemma mirror_plan {v : E4} (hv : v ≠ 0) :
    ∃ g ∈ GenH,
      motionHom (g⁻¹ * Signed.reflect timeAxis * g) = (ℝ ∙ v)ᗮ.reflection := by
  obtain ⟨g, hg, c, hc⟩ := tAlign v
  refine ⟨g, hg, ?_⟩
  let f := motionHom g
  have he : f v = c • basis timeAxis := hc
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv (f.injective (by simpa using he))
  have ht : (ℝ ∙ v)ᗮ.map (f.toLinearEquiv : E4 →ₗ[ℝ] E4) = (ℝ ∙ basis timeAxis)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    change (ℝ ∙ f v)ᗮ = _
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcn)]
  have hm : (ℝ ∙ basis timeAxis)ᗮ.reflection = f.symm.trans ((ℝ ∙ v)ᗮ.reflection.trans f) :=
    (congrArg (fun A : Submodule ℝ E4 => A.reflection) ht.symm).trans
      (Submodule.reflection_map f (ℝ ∙ v)ᗮ)
  rw [map_mul, map_mul, map_inv, motionHom_mirror]
  change f⁻¹ * (ℝ ∙ basis timeAxis)ᗮ.reflection * f = (ℝ ∙ v)ᗮ.reflection
  rw [hm]
  apply LinearIsometryEquiv.ext; intro x
  change f.symm (f ((ℝ ∙ v)ᗮ.reflection (f.symm (f x)))) = _
  simp

def older (p:Ortho): ℝ:= LinearMap.det (motionHom p).toLinearEquiv.toLinearMap
@[simp]lemma older_one:older 1=1:=by unfold older; rw [map_one,show (LinearEquiv.toLinearMap _ : Module.End ℝ E4)=1 from (by rfl), map_one]
lemma older_mul(p q: Ortho):older (p*q)=older p*older q:=by unfold older; rw[map_mul,show (LinearEquiv.toLinearMap _ : Module.End ℝ E4)= ((motionHom p).toLinearEquiv.toLinearMap*(motionHom q).toLinearEquiv.toLinearMap) from (by rfl),map_mul]
lemma theta_det : older thetaR= -1:=by rw [older,motionHom_mirror]; change LinearMap.det _=(-1:ℝ); rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton (by intro h; have hh:=basis_norm d₀; rw[h,norm_zero] at hh; norm_num at hh),pow_one]
lemma both (p: Ortho): p∈GenH ∨ (thetaR*p)∈GenH:=by
      let h(p:Ortho):Prop:= p∈GenH∨(thetaR*p)∈ GenH; have he(p q:Ortho): h p→h q→h (p*q):=by
             rintro (hp|hp)(hq|hq); exact Or.inl (GenH.mul_mem hp hq); · right; rw [show thetaR*(p*q)= (thetaR*p*thetaR)*(thetaR*q) from by simp only[mul_assoc]; rw [← mul_assoc thetaR thetaR q,mirM,one_mul]]; exact GenH.mul_mem (normalR p hp) hq
             · exact Or.inr (mul_assoc thetaR p q ▸ GenH.mul_mem hp hq)
             left; rw [show p*q=(thetaR*(thetaR*p)*thetaR)*(thetaR*q) from by rw [←mul_assoc thetaR thetaR,mirM,one_mul]; simp only[mul_assoc]; rw [← mul_assoc thetaR thetaR,mirM,one_mul]]; exact GenH.mul_mem (normalR _ hp) hq
      have ht(v:E4):∃ q:Ortho, h q∧ motionHom q=hyp v:=by
             by_cases hv:v=0; · subst v; refine ⟨1,Or.inl GenH.one_mem,?_⟩; rw [map_one]; symm; apply LinearIsometryEquiv.ext; intro x; apply Submodule.reflection_mem_subspace_eq_self; simp
             obtain ⟨x,hx,hP⟩:= mirror_plan hv; refine ⟨x⁻¹*thetaR*x,Or.inr ?_,hP⟩; rw [← mul_assoc,← mul_assoc]; exact GenH.mul_mem (normalR _ (GenH.inv_mem hx)) hx
      have hv (l : List E4):∃ t:Ortho,h t ∧ motionHom t=(l.map hyp).prod:=by
             induction l with
             | nil => exact ⟨1,Or.inl GenH.one_mem,map_one _⟩
             | cons i l ih=> obtain ⟨q,hq,h⟩:= ht i; obtain ⟨x,hx,k⟩:= ih; exact ⟨q*x,he q x hq hx,(map_mul motionHom ..).trans (congr_arg₂ _ h k)⟩
      obtain ⟨l,-,hl⟩:= (motionHom p).reflections_generate_dim; obtain ⟨t,hv,ht⟩:= hv l; rw [← motionHom_injective (ht.trans hl.symm)]; exact hv
lemma limen(p: Ortho): older p* older p=1:=by
      -- apply norm map gives |det|=1
      unfold older
      let b:= stdOrthonormalBasis ℝ E4; let S:=motionHom p; let t:=(motionHom p).toMatrix b.toBasis b.toBasis; rw[← LinearMap.det_toMatrix b.toBasis]; change t.det*t.det=1; have he:= S.toMatrix_mem_unitaryGroup b b; have hp:t.transpose*t=1:=he.1; nth_rw 1 [← Matrix.det_transpose]; rw [← Matrix.det_mul,hp,Matrix.det_one]
lemma ingens (p: Ortho)(hp: p ∈ GenH) : older p=1:=by
       have he(i:SpaceAxis)(r:ℝ): (D i r).coord=(D i (r/2)).coord*(D i (r/2)).coord:=by nth_rw 1[← add_halves r]; exact congr_arg EuPin.coord (SpinParity.additive (way i) ..)
       induction hp using Subgroup.closure_induction with
       | one => exact older_one
       | inv x hx h=> have he:= older_mul x x⁻¹; rw[h,mul_inv_cancel,older_one,one_mul] at he; exact he.symm
       | mul x y hx hy h k=> rw [older_mul,h,k,one_mul]
       | mem x h=> obtain ⟨i,r,rfl⟩:=h; rw [he,older_mul,limen]
lemma prop_inherit (G: Subgroup EuPin)(he:∀ i:SpaceAxis,∀ r:ℝ,D i r∈ G)(p:EuPin)(hp:p.IsRotation):p∈ G:=by
      have h: p.coord∈ GenH:=by
             rcases both p.coord with h|h; exact h; have h:= ingens _ h; rw [older_mul, theta_det, show older p.coord=1 from hp,mul_one] at h; norm_num at h
      have hQ: GenH ≤ G.map euca:= Subgroup.closure_le _|>.mpr (fun x ⟨i,r,h⟩=>⟨_,he i r,h.symm⟩)
      obtain ⟨x,hx,ht⟩:= hQ h; let z:= p*x⁻¹; have hz: z.coord=1:=by change euca z=1; unfold z; rw[map_mul,map_inv,ht]; exact mul_inv_cancel _
      have hi: z∈G:=by
             rcases SpinGeometry.geometry.euFiber z 1 hz with H|H; rw[H]; exact G.one_mem
             let w:=daylight 0 (2*Real.pi); have h:=SpinGeometry.geometry.parityDouble _ _ (Ne.symm (Fin.castSucc_ne_last (0:SpaceAxis))) _ (way 0); rw [show z=w from Subtype.ext (Prod.ext (hz.trans h.1.symm) (H.trans h.2.symm))]; exact he ..
      have hv:=G.mul_mem hi hx; exact (show z*x=p from by simp[z,mul_assoc]) ▸ hv
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.prop_inherit
