import YM.QCD.Raft.Sung

/-! # charge two cochain gradients at probe. use on any given graft P -> P'. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Bid Eyrie Stationary Quarry Work.F03 Exterior Matrix YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n:Side}{η C:ℝ}{P: Cnr n→ℝ}
lemma staff (a:su.Color)(i:su.ColorIndex):|a i|≤‖a‖:=by
    rw [← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
lemma pole_diff (x:Site n)(p:PlaqAxes)(s : Signed)(a:Axis):
    ∃ i:Axis, (Face.send s 0 (x,p)).1+step i=(Face.send s 0 (x+step a,p)).1∨(Face.send s 0 (x+step a,p)).1+step i=(Face.send s 0 (x,p)).1:=by
  refine ⟨s.perm a,?_⟩
  have he:s.act (step a:Site n) =(if s.flip a then -(step (s.perm a)) else step (s.perm a)):=by rw [← Step.vec_pos,← Step.vec_rotate]; simp [Step.rotate,posDir,Step.vec]
  rw [add_comm x,heading,he]; split <;> simp [add_comm]
lemma mood (a:su.Color)(x:Cnr n)(hx:x=(poke a n).1 ∨ x=(poke a n).2) (p:PlaqAxes)(j:su.ColorIndex)(b:Site n)(i:Axis)(s:Signed):
    ‖grad i (Iteration.flux (pulled (arm su n 1 x) s) p j) b‖ ≤ ‖a‖* ‖speedL n‖^2:=by
  let u:= (Face.send s (0:Site n) (b,p)).1; let v:= (Face.send s (0:Site n) (b+step i,p)).1; let F:=Iteration.flux (arm su n 1 x)
  have he: grad i (flux (pulled (arm su n 1 x) s) p j) b= YM.Next.Free.turned s p*(F (p.rotate s) j v-F (p.rotate s) j u):=by rw [grad,windsG,windsG,mul_sub]
  rw [he,norm_mul,Real.norm_eq_abs (YM.Next.Free.turned s p),stamp_abs, one_mul]
  let H:= vw (step 0:Site n) (melody (Pearl.beamH n)); let S:=plaquette (p.rotate s)
  have hp: ‖H (v,S)-H (u,S)‖≤ _:=volition _ _ (pole_diff b p s i) S
  have ht := cornS a S b j
  obtain hh|hh:=hx
  · have hs(a':Site n): F (p.rotate s) j a'=a j*(H (a',S)).re:=by unfold F; rw [hh]; exact congr_fun ht.1 (a',S)
    rw [hs,hs,← mul_sub,norm_mul, ← Complex.sub_re]; exact mul_le_mul (staff ..) ((Complex.abs_re_le_norm _).trans hp) (by positivity) (norm_nonneg _)
  have hs(a':Site n): F (p.rotate s) j a'=a j*(H (a',S)).im:=by unfold F; rw [hh]; exact congr_fun ht.2 (a',S)
  rw [hs,hs,← mul_sub,norm_mul, ← Complex.sub_im]; exact mul_le_mul (staff ..) ((Complex.abs_im_le_norm _).trans hp) (by positivity) (norm_nonneg _)
lemma litPay (O: Ornament η C)(hp:0<η) (a:su.Color)(x: Cnr n)(hx:x=(poke a n).1∨x=(poke a n).2):
    ‖Jacobi.mixed x x (barG O.page n) 0‖ ≤2*(cap n*(C*(‖a‖*‖speedL n‖^2)^2)):=by
  rw [(crust O hp x).2,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]; apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let B:=‖a‖*‖speedL n‖^2
  let v(s:Signed):=flux (pulled (arm su n 1 x) s)
  have hz(i:O.mark)(b:Site n)(s : Signed): ‖(O.P i).sample (v s) b‖≤ (O.P i).atom.budget η * B^2:=by
    let A:= O.P i
    apply le_trans _ (mul_le_mul_of_nonneg_right (A.atom.lower_budget _ hp) (sq_nonneg _))
    unfold Pattern.sample Atom.magnitude; rw [Finset.sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro q _; rw [norm_mul,norm_prod]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ∏ _ : Fin 2, B :=by
        apply prod_le_prod (fun i _=>norm_nonneg _); intro j _; obtain ⟨k,H⟩:= Option.isSome_iff_exists.mp (O.paid.1 i j); rw [H]; exact mood a x hx _ _ _ k s
      _ = _:=by simp only [prod_const,card_univ,Fintype.card_fin]
  have hu b s : ∑' i, ‖(O.P i).sample (v s) b‖≤ C*B^2:= (Cost.mono (Cost.scale' O.paid.2.2 (B^2) (sq_nonneg _)) (fun i=> norm_nonneg _) (fun i=> hz i b s)).2.2
  have he s: ‖total (Iteration.plain∘ O.page) (v s)‖ ≤cap n*(C*B^2):=by
    have hs x:=sample_summable O.P (v s) hp.le O.paid.2.2 x; rw [O.trace_payment (v s) hp,total,Summable.tsum_finsetSum (fun b _=> hs b)]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun b (_:b∈univ)=> (norm_tsum_le_tsum_norm (hs b).norm).trans (hu b s))).trans; rw [sum_const,card_univ,nsmul_eq_mul]; exact le_rfl
  unfold Patch.average; rw [norm_mul,Real.norm_of_nonneg (show 0≤((↑(Fintype.card Signed):ℝ)⁻¹) from toll_on.le)]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (s:=univ) (fun i _=> he i))) toll_on.le).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ,← mul_assoc,toll,inv_mul_cancel₀ (by positivity),one_mul]
lemma windPrice (O:Ornament η C)(hp:0<η)(a:su.Color): Tendsto (fun n:Side=> scoreM (barG O.page n) a (pointT n 1)/densityP n) atTop (𝓝 0):= by
  have he:= speeds; have ht:= track_limit
  let X n:= ‖((Pearl.beamH n:ℝ))⁻¹ • speedL n‖; let Q n:= ‖speedL n‖
  have hs:Tendsto Q atTop (𝓝 0):=by simpa using! he.norm
  have hX:Tendsto X atTop (𝓝 1):=by simpa [X] using! ht.norm
  apply squeeze_zero_norm' (a:=fun n=>4*C*‖a‖^2*(X n*Q n)^2) _ (by simpa using! (((hX.mul hs).pow 2).const_mul (4*C*‖a‖^2)))
  apply Eventually.of_forall; intro n
  rw [norm_div,Real.norm_of_nonneg (density_pos n).le, ratedP _ (zen (O.cost hp) hp _)]
  apply (div_le_div_of_nonneg_right ((norm_add_le ..).trans (add_le_add (litPay O hp a (poke a n).1 (Or.inl rfl)) (litPay O hp a (poke a n).2 (Or.inr rfl)))) (density_pos n).le).trans_eq
  unfold Q X densityP; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Pearl.beamP _))]; field_simp [(cap_pos n).ne',(Pearl.beamP _).ne']; ring
end YM.QCD.Raft
