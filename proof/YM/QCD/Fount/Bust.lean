import YM.QCD.Fount.Price
/-! # Mass: fixed masks; exact pocket and stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM Run
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR Cost
variable {j k m B:ℕ}{P:Plan j}{w D v r b C p a t A s T d R :ℝ}{f c:Side}
abbrev houseK (m:ℝ)(X:St f): St f:= fun U=> X U+(m:ℂ) • 1
-- scalar term log pack weighted by |m|.
variable {X:St f} {F:Flight j k}{e:f.val=c.val*F.L.val}
abbrev debt (p:ℝ)(X:St f):St f:= -(p:ℂ) • Tee.inverser X
lemma chirHi (J A:Sheet f)(h:J*J=1)(_hJ:star J=J)(ha:Cost.Chiral J A):Cost.Chiral J A⁻¹:=by
   unfold Cost.Chiral; rw [show star A⁻¹=(star A)⁻¹ from (Matrix.conjTranspose_nonsing_inv _),ha, Matrix.mul_inv_rev,Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h, Matrix.mul_assoc]
-- exact in terms of P.det
lemma cinder (m:ℝ)(X:St f) (hg:Species F e D R r b C B X)(ht:Species F e D R r b C B (houseK m X))(q:Grid f)(hx:‖debt m X q‖ < 1) : Real.log (houseK m X q).det.re-Real.log (X q).det.re= ∑ i:Site f,((Run.cell (Run.lap (debt m X q)) i i).trace).re:=by
   let A:Sheet f:= 1-debt m X q; have he:A*X q=houseK m X q:=by
       unfold A debt houseK inverser; rw [Pi.smul_apply,sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.nonsing_inv_mul (X _) (hg.sole _),neg_smul,sub_neg_eq_add]
   have hf: Cost.Chiral (chirality f) A:=by
       have hp:= chirHi (chirality f) (X q) chi_sq chi_star (hg.crease q)
       unfold Cost.Chiral; unfold A; simp only [star_sub,star_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,chi_sq,debt,Pi.smul_apply,star_smul,inverser,Matrix.mul_smul,Matrix.smul_mul,star_neg,Complex.star_def,Complex.conj_ofReal]; rw [hp]
   have hv: A.det=(A.det.re:ℂ) := (determinant_real chi_sq hf).symm
   have hh: (houseK m X q).det.re=A.det.re*(X q).det.re := by
       rw [← he,Matrix.det_mul,Complex.mul_re,show A.det.im=0 by rw [hv,Complex.ofReal_im]]; simp
   have hc:0<A.det.re:= pos_of_mul_pos_left (hh ▸ ht.full _) (hg.full _).le
   have hm:A= 1-debt m X q:=rfl
   have hxQ : notch 1 A=debt m X q:= by unfold notch; rw [hm]; simp
   have h:=stamped A hf hc zero_lt_one (hxQ.symm ▸ hx)
   rw [hh,Real.log_mul hc.ne' (hg.full _).ne',add_sub_cancel_right,h,hxQ,Real.log_one,mul_zero,sub_zero]
lemma heft (m:ℝ)(P:Plan j)(S:Offer 1 t C)(J:Offer 2 b A)(p:ℝ):park F e P S J p m=houseK m (park F e P S J p 0):=by
   funext i; simp only [park,pesto,Tee.trunkM,houseK,Pi.add_apply, Pi.smul_apply,Pi.one_apply,Complex.ofReal_zero, zero_smul,Pi.zero_apply]; abel
variable {u:ℝ}{x:St f}
lemma volts (he:0≤u)(hx:u ≤ 1/2)(hg:Own f t 0 B x u)(ht:0<t): Own f t 0 B (fun U=>lap (x U)) (2*u):=by
   have hP : (1/2:ℝ)<1:=by norm_num
   let F i:= u*(1/2:ℝ)^i; have hf:HasSum F (2*u):= by
       have he:= (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤1/2) hP).mul_left u; norm_num at he; rw [mul_comm (2:ℝ)]; exact he
   have hk i : Own f t 0 B (x^(i+1)) (F i):=by
       induction i with
       | zero=> simpa only [zero_add,pow_one, F,pow_zero,mul_one] using hg
       | succ j ih=>
          have hv :0≤ F j:=by unfold F; positivity
          have h: F (j+1)= F j*(1/2):=by unfold F; ring
          rw [pow_succ,h]; exact (ih.meet (hg.mono hx) ht le_rfl hv (by norm_num))
   have hy U : ‖x U‖<1:= (hg.value ht le_rfl he U).trans_lt (hx.trans_lt hP)
   rw [← hf.tsum_eq]
   refine Heritage.congregation (T:=fun i U=>Run.logchip (x U) i) ht le_rfl (fun i=>?_) hf.summable (fun U=> (Run.log_series (hy U)).hasSum)
   have hP:=((hk i).scalar ((i+1:ℂ)⁻¹)).minus
   refine (show Own f t 0 B (fun U=>Run.logchip (x U) i) (‖(i+1:ℂ)⁻¹‖*F i) from ?_).mono (mul_le_of_le_one_left (by unfold F; positivity) ?_)
   · simpa only [Run.logchip,funext_iff,Own] using! hP
   rw [norm_inv, show ‖(i+1:ℂ)‖= (i+1:ℝ) by norm_cast]; exact inv_le_one_of_one_le₀ (by simp)
end YM.QCD.Fount
