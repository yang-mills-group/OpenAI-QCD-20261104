import YM.Heron.Eagle
import YM.MassiveTwoEstimates.SpinParity
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
-- standard differentiation by integration of hom proof. No Lie.
theorem oak {V:Type} [NormedRing V] [NormedAlgebra ℝ V] [CompleteSpace V] [SecondCountableTopology V] (T:ℝ→V) (H:Continuous T) (ht:∀ x y,T (x+y)=T x*T y)(hp:T 0=1) : DifferentiableAt ℝ T 0:=by
   let F:= fun s:ℝ=> ∫ t in (0:ℝ)..s, T t; let J:= fun z:ℝ=> z⁻¹ • F z
   have he(s:ℝ):HasDerivAt F (T s) s:= intervalIntegral.integral_hasDerivAt_right (H.intervalIntegrable ..) (H.stronglyMeasurable.stronglyMeasurableAtFilter) H.continuousAt
   have hz:F 0=0:=intervalIntegral.integral_same; have hq:= hasDerivAt_iff_tendsto_slope_zero.mp (he 0); simp only [sub_zero,zero_add,hz,hp] at hq; have hJ:Tendsto J (𝓝[>] (0:ℝ)) (𝓝 (1:V)):= hq.mono_left (nhdsWithin_mono _ (show Ioi 0⊆ ({0}:Set ℝ)ᶜ from fun _ hr=>ne_of_gt hr))
   have hU:∀ᶠ x in 𝓝[>] (0:ℝ),IsUnit (J x):= hJ (Units.isOpen.mem_nhds (show IsUnit (1:V) from isUnit_one)); obtain ⟨r,hr,hb⟩:= (hU.and self_mem_nhdsWithin).exists; change 0<r at hb
   have hv(x:ℝ): T x*J r=r⁻¹ • (F (x+r)-F x):=by
       rw [show (F (x+r)-F x)= ∫ z in (0:ℝ)..r,T x*T z from ?_];
       · unfold J F; have hP : IntegrableOn T (Ioc 0 r) volume:= (H.intervalIntegrable 0 r).1; rw [intervalIntegral.integral_of_le hb.le,intervalIntegral.integral_of_le hb.le, integral_const_mul_of_integrable] -- API
         exact mul_smul_comm ..; exact hP
       simp_rw [← ht]; rw[intervalIntegral.integral_comp_add_left,add_zero]; unfold F; rw [eq_comm,eq_sub_iff_add_eq]; rw [add_comm]; exact intervalIntegral.integral_add_adjacent_intervals (H.intervalIntegrable ..) (H.intervalIntegrable ..)
   let Q:=J r; let B:=hr.unit
   let M:= fun x:ℝ=>r⁻¹ • (F (x+r)-F x); have Hm:M=(fun x=> T x*B.val):=funext fun x=>by rw[IsUnit.unit_spec,hv]
   rw[show T=(fun x=> M x*B⁻¹.val) from funext (fun x=>by rw [Hm]; change _=T x*B.val*B⁻¹.val; rw[mul_assoc,show B.val*B⁻¹.val=1 from B.val_inv,mul_one])];
   have hd : DifferentiableAt ℝ (fun x=> F (x+r)) 0:= (he (0+r)).differentiableAt.comp 0 (f:=fun x=>x+r) ((hasDerivAt_id' _).add_const _ |>.differentiableAt); have hy:DifferentiableAt ℝ (fun x=>F (x+r)- F x) 0:= hd.sub (he 0).differentiableAt; have hG:DifferentiableAt ℝ M 0:= DifferentiableAt.fun_const_smul hy _; exact hG.mul_const _
variable (s:Ortho.Skew)(Γ:ℝ→EuPin)(hΓ: EuPin.Path s Γ)
noncomputable def cΩ (Γ:ℝ→EuPin)(x:ℝ):Spike:=(Γ x).matrix.val
include hΓ
lemma monad(x y:ℝ): cΩ Γ (x+y)=cΩ Γ x*cΩ Γ y:=by unfold cΩ; rw[MassiveTwoEstimates.SpinParity.additive hΓ]; rfl
lemma moss :DifferentiableAt ℝ (cΩ Γ) 0:=by
    refine oak _ ?_ (monad _ _ hΓ) ?_
    · have h:=hΓ.2.1; unfold cΩ EuPin.matrix; fun_prop (disch:= assumption); -- ht Cont from hΓ
    unfold cΩ; rw[hΓ.1]; rfl
end YM.Heron
#print axioms YM.Heron.moss
