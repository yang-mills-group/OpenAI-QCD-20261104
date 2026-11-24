import YM.QCD.Globe.Ken
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
open Laurent Bloch QCD.Free Flume.Para
variable {t r W d C a:ℝ}
lemma rent_ray (hj:2 ≤ j): ∃ C:ℝ,0<C ∧∀ (v:Train j)(p:Momentum),p∈baseCube→‖(Flume.Dir v p).1‖≤ C*lengthSq p:=by
     obtain ⟨η,B,hη,hB,H⟩:= sensitivity hj (fun p:Train j×Axis=>p.1) (fun i=>i.2)
     refine ⟨B,hB,fun v p hp=>?_⟩
     have he(i):‖YM.Next.Free.chip (p i)‖≤ ‖p i‖:=by
          rw [← cast_real hp.1 i]; change ‖Complex.exp (Complex.I*_)-1‖ ≤ _; rw [Complex.norm_real]; apply Real.norm_exp_I_mul_ofReal_sub_one_le
     have hx(i): ‖steps v i p‖≤ B:= by simpa using (H (v,i)).bound _ (mem_cube_real (base_subset_realCube hη hp) hη)
     change ‖hemi v p‖ ≤ _; rw [← chosen_steps hj v p hp]; apply (norm_sum_le ..).trans; unfold lengthSq; rw [Finset.mul_sum]; apply sum_le_sum; intro i hi; rw [powerD _ _ hp.1,norm_mul, Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),mul_comm]; exact mul_le_mul (hx i) (pow_le_pow_left₀ (norm_nonneg _) (he i) _) (sq_nonneg _) hB.le
noncomputable def gleeM (v: Train j)(p:Momentum)(a:ℝ):Para:= Flume.Dir v p + solo (a:ℂ)
lemma gleeOk (v:Train j)(p:Momentum)(ha:p∈baseCube)(a:ℝ):Native (gleeM v p a):=(native_dir _ _ ha.1).ad (Native.scalar _)
lemma bright (hj: 2 ≤ j):∃ C δ:ℝ,0<C ∧ 0 < δ ∧∀ (v:Train j)(p:Momentum)(a:ℝ),p∈baseCube→|a|≤δ→ C*lengthSq p+a^2 ≤ (quad (gleeM v p a)).re:=by
    obtain ⟨η,C,hη,hn,hC,H⟩:= size_q hj; obtain ⟨t,ht,h⟩:= rent_ray hj; let δ:= (C/2)/(2*t); refine ⟨C/2,δ,half_pos hC,div_pos (half_pos hC) (by linarith),fun v p a hp hx=> ?_⟩
    obtain ⟨hu,hv⟩:= H v p (base_subset_realCube hη hp); have hQ : (quad (gleeM v p a)).re = (quad (Flume.Dir v p)).re + a^2 + 2*a*(Flume.Dir v p).1.re:=by unfold gleeM; rw [quad_add]; simp only [Para.solo,Para.quad,Flume.Para.beam,Complex.add_re]; norm_num [← Complex.ofReal_pow]; ring -- may issue
    have hD: 0 ≤ lengthSq p:= sum_nonneg fun _ _=> sq_nonneg _; have hh := (Complex.abs_re_le_norm _).trans (h v p hp)
    have he: a * (Flume.Dir v p).1.re ≥ -(δ*(t*lengthSq p)):= by apply abs_le.mp _ |>.1; rw [abs_mul]; exact mul_le_mul hx hh (abs_nonneg _) (by unfold δ; positivity) -- order
    rw [hQ]; have hx:δ*(2*t)= C/2:= div_mul_cancel₀ _ (by positivity : (2:ℝ)*t≠0); nlinarith only [mul_le_mul_of_nonneg_right hx.le hD,hu,he]
lemma area : ∃ C:ℝ,0<C∧∀ p: Momentum,p∈baseCube→lengthSq p ≤ C:=by
     refine ⟨4*Real.pi^2,by positivity,fun p hp=>?_⟩; unfold lengthSq; apply (sum_le_sum (g:=fun i:Axis=> Real.pi^2) fun i _=> ?_).trans_eq; · simp [Axis] -- sugar
     apply pow_le_pow_left₀ (norm_nonneg _); nth_rw 1 [← cast_real hp.1 i]; rw [Complex.norm_real]; exact hp.2 i
-- shifted model unitary bound
lemma living (A:Para)(hp:Native A)(h:0<(quad A).re): IsUnit (model A).det ∧ ‖(model A)⁻¹‖ * Real.sqrt (quad A).re=1:=by
    have hx : quad A≠0:= fun hv=> not_lt_of_ge (by rw [hv]; simp) h
    refine ⟨Flume.Para.funds hx,?_⟩; have hv : ‖model (turn A)‖^2=(quad A).re:=by
         rw [pow_two,← CStarRing.norm_star_mul_self, hp.rotated.conjugate, turn_turn, model_forth,norm_smul, hp.magnitude,norm_one,mul_one]
    rw [← Para.live_inv hx, Para.reciprocalP, model_smul, norm_smul,norm_inv,hp.magnitude]; have he:=Real.sqrt_sq (norm_nonneg (model (turn A))); rw [hv] at he; rw [← he,mul_assoc, ← pow_two,Real.sq_sqrt h.le,inv_mul_cancel₀ h.ne']; -- norm_nonneg (model (turn A)), inv_pos.mpr h,mul_inv_cancel₀ h.ne',Real.sqrt_pos.mpr h,Real.sq_sqrt h.le]
end YM.QCD.Globe
