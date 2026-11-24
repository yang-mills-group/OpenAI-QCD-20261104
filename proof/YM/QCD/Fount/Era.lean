import YM.QCD.Fount.Boom
import YM.Push.STATIONARY_UNIFORM.Continue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Lapses
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open PhysicalNext.Repeat Lapis ConnectedActivityE6 Push Push.Uniform Blaze Brush Poll Coat
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR
variable {i b j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a A B w ν α s L y u' σ:ℝ} {M:ParcelR}{f c:Side}{S:StepData c f}
lemma strikes (F:Tree.Forest S.ratio)(ρ:Bid.Dir su c→AxisChart su F)(x:Positions (Uniform.Primary c su)): Octave.projection F (x,Lapis.orbit F ρ x)=(encamp F ρ (mergeC c x)).1:= by
   rw [← modelU (S:=S) _ _ _]; change Uniform.fine su F (combineH F (x,Lapis.orbit F ρ x))= _
   unfold buildU Function.comp; rw [ContinuousLinearEquiv.symm_apply_apply]; exact rfl
lemma beads {W:Cnr c→ℝ}(hj:1≤A)(hK:(Fintype.card (Primary c su):ℝ) ≤ A)(hp:0 ≤ B)(h: ContDiffAt ℝ ω W 0)(hv:∀ x:Cnr c, ‖iteratedFDeriv ℝ 2 W 0 ![x,x]‖≤B*‖x‖^2): normJ 2 (W ∘ mergeC c) 0 ≤ tollS A 2 (3*B):=by
   have ht (i:Primary c su): ‖mergeC c (Uniform.bolt i)‖=1:=by
      obtain ⟨⟨x,y⟩,z⟩:=i; have hu:=primedBolt (c:=c) (show Road c from (x,y,z)); erw [← hu]; rw [ContinuousLinearEquiv.apply_symm_apply]; exact norm_bolt _
   refine raises hj hK (by positivity) le_rfl (fun q=>?_)
   let L:= (mergeC c).toContinuousLinearMap; let x:=L (Uniform.bolt (q 0)); let y:= L (Uniform.bolt (q 1)); let S:= iteratedFDeriv ℝ 2 W 0
   have hp' : Uniform.entry (W ∘ mergeC c) 0 q=S ![x,y]:=by
      unfold entry; erw [linear_pull L (k:=2) (f:=W) (by rw [map_zero]; exact h.of_le le_top)]; rw [map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; exact congr_arg _ (funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩))
   have he:S ![x+y,x+y]=2*S ![x,y]+S ![x,x]+S ![y,y]:=by
      have hk:= Work.F03.hessian_symmetric (h.of_le le_top) x y; unfold S; simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,map_add,_root_.add_apply] at * -- risk
      change _=_; linarith only [hk]
   rw [hp',Real.norm_eq_abs]; obtain hx:= ht (q 0); change ‖x‖=1 at hx; have hy:‖y‖=1:=ht _; have hz:‖x+y‖ ≤ 2:=by simpa only [hx,hy,one_add_one_eq_two] using norm_add_le x y
   have hh : |S ![x+y,x+y]|≤ B*2^2:= (hv _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) hp)
   have hu :=hv x; have hB:=hv y; rw [hx,one_pow,mul_one, Real.norm_eq_abs] at hu; rw [hy,one_pow,mul_one,Real.norm_eq_abs] at hB
   obtain ⟨hu,hx'⟩:=abs_le.1 hu; obtain ⟨hi,hy'⟩:=abs_le.1 hB; rw [he] at hh; obtain ⟨hz,he⟩:=abs_le.1 hh
   unfold S at *; refine abs_le.2 ⟨?_,?_⟩<;> linarith
end YM.QCD.Fount
