import YM.QCD.Pearl.Acres

/-! # margin receipts -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff ENNReal
variable {n: Side} {μ κ : ℝ}
def tuneBill (κ t:ℝ):ℝ:=300*(2*Real.pi^2)*(Real.log (κ+1)+Real.log 4)
lemma missing (ht:beamH n<1/4)(h:3≤κ)(hp : (κ+1)*beamH n ≤ 1/4):
    |4*(2*Real.pi^2*Real.log (beamH n)⁻¹)-∫ x in fans (midst n κ), windward x| ≤ tuneBill κ (beamH n):=by
  let t:= beamH n; let z:=(κ+1)*t; let A:=orbShell t; let M:=fans (midst n κ)
  have hZ : 0<z:=mul_pos (by linarith) (beamP n)
  have he:=inn ht.le h
  change |_-(∫ x in M,windward x)|≤_
  rw [← full_pole (beamP n) (by linarith), ← setIntegral_diff (fans_m _) (south (beamP n)) he];
  let B:=orbShell z; let X:=orbShell (1/4)
  have hb : B ⊆ A:=by
    intro i hi; exact ⟨lt_of_le_of_lt (le_mul_of_one_le_left (beamP n).le (by linarith)) hi.1,hi.2⟩
  have hx : X ⊆ B:= fun i hi=> ⟨lt_of_le_of_lt hp hi.1,hi.2⟩
  have hh : B \ X ⊆ M:= by
    rintro i ⟨hi,hi'⟩; refine between ht h ⟨hi, mem_closedBall.mpr ?_⟩; rw [dist_zero_right]; by_contra! heh; exact hi' ⟨heh,hi.2⟩
  refine (show |∫ x in A \ M, windward x| ≤ ∫ x in A \ M,(300*radial 4 x) from norm_integral_le_of_norm_le ((sorb 4 (beamP n)).mono_set Set.sdiff_subset|>.const_mul _) (Eventually.of_forall gale)).trans ?_
  rw [integral_const_mul,setIntegral_diff (fans_m _) (sorb 4 (beamP n)) he]
  have hj: ∫ x in B \ X, radial 4 x ≤ ∫ x in M, radial 4 x := setIntegral_mono_set ((sorb 4 (beamP n)).mono_set he) (Eventually.of_forall fun _=> sinuous ..) (Eventually.of_forall hh)
  rw [setIntegral_diff shell_meas (sorb 4 hZ) hx] at hj
  have hu : ∫ i in M, radial 4 i ≥ 2*Real.pi^2*(Real.log z⁻¹-Real.log 4):=by
    unfold B X radial at * -- maybe problematic
    rw [polar_m z hZ (by linarith [show z≤1/4 from hp]),polar_m (1/4) (by norm_num) (by norm_num)] at hj; field_simp at hj; simpa only [one_div] using hj
  have heq: Real.log z⁻¹= Real.log t⁻¹-Real.log (κ+1):=by rw [Real.log_inv,Real.log_inv,Real.log_mul (show κ+1≠0 by linarith) (show t≠0 from (beamP n).ne')]; ring -- fix
  rw [show (∫ x in fans (midst n κ), radial 4 x)=(∫ x in M, radial 4 x) from rfl] -- inspect
  apply (mul_le_mul_of_nonneg_left (sub_le_sub_left hu (∫ x in A,radial 4 x)) (by norm_num : (0:ℝ)≤300)).trans_eq
  rw [show (∫ x in A,radial 4 x)=_ from polar_m t (beamP n) (by linarith only [show t<1/4 from ht]),heq]; unfold tuneBill; ring
lemma icebox (ht:beamH n≤1/4)(h:3≤κ): (∑ p∈ midst n κ, (beamH n)^4*radial 5 (centerZ p))* beamH n ≤ 32*(2*Real.pi^2):=by
  have hp:=beamP n; apply (mul_le_mul_of_nonneg_right (compareCost 5 ht h) hp.le).trans
  rw [ripe hp (by linarith)]; norm_num; field_simp; nlinarith [Real.pi_pos]
lemma sweeping (h:3 ≤ κ): ∃ C:ℝ, ∀ n: Side,beamH n≤1/4 →
    |(∑ i ∈ midst n κ,(beamH n)^4 *windward (centerZ i)) - (∫ x in fans (midst n κ), windward x)| ≤ C:=by -- parenthesize
  obtain ⟨C,hc,H⟩:= sway2; refine ⟨C*(32*(2*Real.pi^2)),fun n ht=>?_⟩
  let t:= beamH n; have hp:0<t:=beamP _
  have he: ∀ i∈midst n κ, IntegrableOn windward (seat i) volume:=fun i hi=>(south hp).mono_set (seat₃ ht h hi)
  unfold fans; rw [integral_biUnion_finset _ (fun i _=> chair i) (fans_dis _) he,← sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (g:=fun i => t^4*(C*radial 5 (centerZ i)*t)) ?_).trans
  · have he : (∑ p∈ midst n κ,t^4*radial 5 (centerZ p))*t ≤ _:= icebox ht h
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left he hc); rw [sum_mul,Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  intro i hi; let Y:=seat i; have ht' : κ*t<‖centerZ i‖:= (medium.mp hi).1; have h2 : 0< ‖centerZ i‖:=by nlinarith
  have hw : volume Y ≠ ⊤:=by unfold Y; rw [seating]; exact ENNReal.ofReal_ne_top
  change |t^4*_-_|≤_
  rw [show t^4= volume.real (seat i) from (seatVolume i).symm,← smul_eq_mul, ← setIntegral_const,← integral_sub (show IntegrableOn (fun _ => windward (centerZ i)) (seat i) volume from integrableOn_const hw) (he i hi),← smul_eq_mul, ← setIntegral_const] -- check
  refine norm_integral_le_of_norm_le (f:=fun x=> windward (centerZ i)-windward x) (show IntegrableOn (fun _ => C*radial 5 (centerZ i)*t) (seat i) volume from integrableOn_const hw) ?_
  filter_upwards [ae_restrict_mem (μ:=volume) (chair i)] with x hx
  have hz:=seat_far hx; rw [dist_eq_norm] at hz
  rw [norm_sub_rev]; exact (H (centerZ i) x h2 (by nlinarith only [hp, h,mul_le_mul_of_nonneg_right h hp.le,ht',show ‖x-centerZ i‖≤t from hz])).trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hc (sinuous ..)))
end YM.QCD.Pearl
