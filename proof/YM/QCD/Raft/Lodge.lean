import YM.QCD.Raft.Scale

/-! # Frobenius receipt for full massless propagator, not just blocked high -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Cost Run Lattice Wilson Function Finset Kit Flume Laurent Bloch Metric Push.Uniform YM.Next.Free RG Rudder Free Para Pearl Pinch MeasureTheory Stationary Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {I:Type}{n:Side}{j:ℕ}{κ r C B ε:ℝ}
lemma subtotal (A:Site n→Bundle): hs2 (Flume.install A)=∑ i, hs2 (A i):=by
  unfold Flume.install; rw [HunitR _ _ (Unitary.star_mem (leaf_u _)), Hunit _ _ (leaf_u _),hs2,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [Fintype.sum_prod_type,sum_eq_single i]; · simp [lined,rides]
  · intro b _ he; simp [lined,rides,he,Ne.symm]
  simp
lemma purchaseB (A: Bundle): hs2 A ≤ (Fintype.card Fiber:ℝ)^2 *‖A‖^2:=by
  unfold hs2; apply (sum_le_sum (s:=univ) (fun i _=> sum_le_sum (s:=univ) fun j _=> pow_le_pow_left₀ (norm_nonneg (A i j)) (Cost.north A i j) 2)).trans_eq; simp only [sum_const,card_univ,nsmul_eq_mul]; ring
lemma hslow (n:Side):0<Pearl.beamH n:=Pearl.beamP _
lemma t_min : (∑ p:Site n, ((beamH n)^4)*(‖tuning p‖^2)⁻¹)= (∑ p:Site n,(‖tuning p‖^2)⁻¹)* (beamH n)^4:=by rw [← mul_sum,mul_comm]
lemma invmoments (n:Side)(ht: beamH n≤1/4): (∑ p:Site n, (beamH n)^4*(‖tuning p‖^2)⁻¹) ≤ 4*(8*(2*Real.pi^2))+4*(4^4*(Real.pi^2/2))+16*(2*Real.pi)^4:=by
  let t:=beamH n; let S:=midst n 3; let K := smallH n 3; let X(p:Site n):=t^4*(‖tuning p‖^2)⁻¹
  have hP : 0<t:=beamP _; have ht':t ≤ 1/4:=ht
  have hu p : 0 ≤ X p:=by unfold X; positivity
  have he (p:Site n):0<‖tuning p‖ := norm_pos_iff.mpr (tune_nonzero p)
  have hr(p:Site n): 0 < atomR p:=by unfold atomR; rw [whirl]; exact lt_of_lt_of_le (he p) (fry_lower _)
  have hm (p:Site n):(‖tuning p‖^2)⁻¹ ≤ 4*radial 2 (centerZ p):=by
    let b:=atomR p; have hb := hr p; have hx : b≤2*‖tuning p‖:=by unfold b atomR; rw [whirl]; exact fry_upper (menu p)
    rw [← one_div,radial,← div_eq_mul_inv]; exact (div_le_div_iff₀ (pow_pos (he p) _) (pow_pos (hr p) _)).2 (by
      rw [one_mul]; exact (pow_le_pow_left₀ hb.le hx 2).trans_eq (by ring))
  have hs : ∑ p∈S,X p ≤ 4*(8*(2*Real.pi^2)):=by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left (pocket (κ:=3) le_rfl ht) (show (0:ℝ)≤4 by norm_num))
    rw [Finset.mul_sum]; refine sum_le_sum fun i hi=>?_ ; have hx : radial 2 (centerZ i)≤radial 3 (centerZ i):=by
      have he :=(medium.mp (show i ∈midst n 3 from hi)).2; have hf:=hr i
      unfold radial; apply inv_le_inv₀ (pow_pos hf _) (pow_pos hf _) |>.2; exact pow_le_pow_of_le_one hf.le (by linarith) (by decide)
    unfold X; exact (mul_le_mul_of_nonneg_left ((hm i).trans (mul_le_mul_of_nonneg_left hx (by norm_num))) (pow_nonneg hP.le 4)).trans_eq (by unfold t; ring)
  have hK : ∑ p∈K,X p≤4*(4^4*(Real.pi^2/2)):=by
    have hx p (_h:p∈K) : X p ≤4 :=by
      have hF:t/2 ≤ ‖tuning p‖:=minSize p
      apply (mul_le_mul_of_nonneg_left (inv_le_inv₀ (pow_pos (he p) 2) (pow_pos (by positivity : 0<t/2) 2)|>.2 (pow_le_pow_left₀ (by positivity) hF 2)) (pow_nonneg hP.le 4)).trans
      field_simp; nlinarith [show t^2≤1 by nlinarith]
    apply (sum_le_sum (fun i p=>hx i p)).trans; rw [sum_const,nsmul_eq_mul,mul_comm]; gcongr; rw [show (4:ℝ)=3+1 from by norm_num]; exact row_count (by norm_num : (3:ℝ) ≤ 3)
  let Q:=univ \ (S∪K)
  have hh : ∑ p∈Q,X p ≤ 16*(2*Real.pi)^4:=by
    apply le_trans (le_abs_self _) (oceanPay (C:=16) (X:=X) (by norm_num) fun i hi=>?_); rw [abs_of_nonneg (hu _)]
    have hx:i∉S ∧ i∉K:= (notMem_union ..).mp ((mem_sdiff.mp hi).2)
    have hp : 1/2 ≤ atomR i:=le_of_not_gt fun he=>hx.1 (medium.mpr ⟨lt_of_not_ge (mt small_h.mpr hx.2),he⟩)
    rw [mul_comm (16:ℝ)]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hP.le _); exact (hm _).trans ((mul_le_mul_of_nonneg_left (radial_hi 2 hp) (by norm_num)).trans (by norm_num))
  change ∑ i,X i ≤ _; rw [splits 3 X]; exact add_le_add (add_le_add hs hK) hh
lemma HSprice (hj: 2≤ j): ∃ C:ℝ, 0≤C ∧ ∀ᶠ n: Side in atTop,∀ v: Train j,hs2 ((unbarred v n)⁻¹)≤ C*cap n:=by
  obtain ⟨r,c,B,h⟩ := Pearl.boot hj -- inspect
  let T:= (Fintype.card Fiber:ℝ)^2*purse r c B^2
  let D:ℝ:=4*(8*(2*Real.pi^2))+4*(4^4*(Real.pi^2/2))+16*(2*Real.pi)^4; let K:= (2*Real.pi)^4
  have hp : 0 < K:= by unfold K; positivity
  have ht : 0≤ T:=by unfold T; positivity
  refine ⟨T*D/K, by unfold D; positivity,?_⟩
  filter_upwards [beam0.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4))] with n hn v
  obtain ⟨ε,e,_⟩:= (h v).source 1 zero_lt_one
  let t:=beamH n; have he : 0<t:=beamP _
  rw [← stage_eq,Flume.stage,subtotal]; apply le_of_mul_le_mul_left _ (pow_pos he 4)
  rw [Finset.mul_sum]; apply le_trans _ (le_of_eq (show T*D=t^4*(T*D/K*cap n) from ?_))
  · apply le_trans _ (mul_le_mul_of_nonneg_left (invmoments n hn) ht); rw [Finset.mul_sum]; refine sum_le_sum fun i _=>?_
    have hg:= keyboard i; have hx:=tune_nonzero i
    rw [show T*_ =t^4*(T*(‖tuning i‖^2)⁻¹) by unfold t; ring]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg he.le _); rw [plac]; have h := h v; have hu:= (h.protectedV e hg hx (h.friend e hg hx)).2; change hs2 (vase (Dir v) _) ≤ _; apply (purchaseB _).trans; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) (sq_nonneg _)).trans_eq (by unfold T; ring)
  rw [show K=cap n*t^4 from (oceanCount n).symm]; field_simp [(cap_pos _).ne']
end YM.QCD.Raft
