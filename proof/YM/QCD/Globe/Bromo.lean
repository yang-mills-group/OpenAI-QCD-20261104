import YM.QCD.Globe.Rents
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Laurent Bloch QCD.Free Flume.Para Cost
variable {t r W d C a:ℝ}
lemma distant (K:Bundle)(u:ℝ)(hu:0 < u)(h:‖K⁻¹‖ * u ≤1)(hv:IsUnit K.det)(R:Bundle)(hr:2*‖R‖ ≤ u) : IsUnit (K+R).det ∧ ‖(K+R)⁻¹‖≤(u/2)⁻¹:=by
    have hc(x:Vec Lat.Fiber): u * ‖x‖ ≤ ‖op K x‖:=by
         have hx := (op K⁻¹).le_opNorm (op K x); rw [← mul_apply_eq_comp,← map_mul, Matrix.nonsing_inv_mul _ hv, map_one,one_apply_eq_self, ← Matrix.cstar_norm_def] at hx; apply le_trans (mul_le_mul_of_nonneg_left hx hu.le); rw [← mul_assoc,mul_comm u]; exact mul_le_of_le_one_left (norm_nonneg _) h
    let A:=K+R; have hy:0<u/2:=half_pos hu; have ht(x:Vec Lat.Fiber): u/2* ‖x‖ ≤ ‖op A x‖:=by
         have hx: ‖op R x‖ ≤ u/2* ‖x‖:=by apply ((op R).le_opNorm _).trans; rw [← Matrix.cstar_norm_def]; apply mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
         have h1:op K x=op A x-op R x:=by rw [show K=A-R from by unfold A; abel, map_sub]; rfl
         suffices he: u/2*‖x‖ +u/2*‖x‖ ≤ ‖op A x‖+u/2*‖x‖ by linarith
         apply le_trans (b:= ‖op K x‖) _ _; · linarith only [hc x]
         rw [h1]; exact (norm_sub_le ..).trans (add_le_add_right hx _)
    have h:IsUnit A.det:=isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((pow_pos hy _).trans_le (Cost.min_det _ hy.le ht)))
    refine ⟨h,?_⟩; change ‖A⁻¹‖≤ _; rw [Matrix.cstar_norm_def]; apply (op A⁻¹).opNorm_le_bound (by positivity); intro x; apply (le_inv_mul_iff₀ hy).2; have hq:= ht (op A⁻¹ x); rwa [←mul_apply_eq_comp,← map_mul, Matrix.mul_nonsing_inv _ h,map_one,one_apply_eq_self] at hq
-- uniform δ spectral bounds independent of sign/excursion
lemma area_sol (P:Plan j):∃ C r T:ℝ,0<C∧0<r∧0 < T∧∀ (v:Train j)(p:Momentum)(c: Side)(K:Sheet c)(m:ℝ),p∈baseCube→Beam K 6 r→Drier K→|m|≤ T→lengthSq p>0→
       let u:=Real.sqrt (C*lengthSq p+m^2); let H:= model (gleeM v p m) + pitchP K p; IsUnit H.det∧ ‖H⁻¹‖ ≤ (u/2)⁻¹:=by
    obtain ⟨C,t,hC,ht,H⟩:=bright P.good; obtain ⟨V,hV,G⟩:=area; let r:= Real.sqrt (C/V)/32; have hr:0<r:=by unfold r; positivity
    refine ⟨C,r,t,hC,hr,ht,fun v p c K m hp hB he hm hv'=>?_⟩; intro u F; let A:=gleeM v p m; have hh:= H v p m hp hm
    let X:=C*lengthSq p+m^2; have hx:0<X:=by unfold X; positivity
    have he' :0<(Para.quad A).re:=hx.trans_le hh; obtain ⟨hi,hS⟩:= living A (gleeOk v p hp m) he'
    have hu : 0 < u:= Real.sqrt_pos.mpr hx; apply distant _ _ hu ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (norm_nonneg _)).trans_eq hS) hi _;
    apply le_trans (mul_le_mul_of_nonneg_left (dry_wave he hB p hp) (show 0 ≤(2:ℝ) by norm_num));
    have hk: (32*r)^2 * V=C:=by unfold r; rw [show (32*(Real.sqrt (C/V)/32))=Real.sqrt (C/V) by ring, Real.sq_sqrt (by positivity :0 ≤ C/V),div_mul_cancel₀ _ hV.ne']
    have hz : (2*(16*lengthSq p*r))^2 ≤ X:=le_trans ?_ (le_add_of_nonneg_right (sq_nonneg _)) -- syntax
    · nlinarith only [mul_nonneg hv'.le (show 0≤ r from hr.le),hz,hu,(show u^2=X from Real.sq_sqrt hx.le)]
    rw [←hk]; nlinarith only [mul_le_mul_of_nonneg_left (G p hp) (show 0 ≤ (32*r)^2 *lengthSq p from by positivity)]
-- extension.Nest block analysis
end YM.QCD.Globe
