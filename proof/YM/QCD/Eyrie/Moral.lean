import YM.QCD.Eyrie.Dim

/-!
# Direct input unmasked Bloom jet Cauchy system
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Rudder
open Revolve Work.F02 Metric Quarry
open scoped Topology Matrix ContDiff BigOperators Classical
variable {n : Side} {I : Type} {k m : ℕ}
section
open scoped Matrix.Norms.L2Operator

def cap (P:Bundle):= ‖P‖
lemma costing (W:Bloom k): W.price=∑ i, cap (W.coeff i):=rfl
lemma limits (P:Bundle)(i j):‖P i j‖≤ cap P:= Cost.north ..
lemma cap_nn (P:Bundle): 0≤cap P:=norm_nonneg _
end
open scoped Matrix.Norms.Frobenius

def fibreCost : ℝ:=(Fintype.card Fiber:ℝ)^2
lemma fibreGe : 0≤ fibreCost:=sq_nonneg _
lemma turning (P : Bundle) : ‖P‖ ≤ fibreCost*cap P:=by
  -- Frobenius via Basis.single; or formula
  have hx:= cap_nn P
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]; push_cast
  rw [Real.sqrt_le_iff]; constructor; exact mul_nonneg fibreGe hx
  norm_cast; apply (sum_le_sum (s:=univ) (fun (i:Fiber) _=> sum_le_sum (s:=univ) fun (j:Fiber) _=> pow_le_pow_left₀ (norm_nonneg (P i j)) (limits P i j) 2)).trans
  norm_num [fibreCost,Fiber,Pinor,Hue]; nlinarith
lemma prefers {X Y: Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℂ X] [NormedSpace ℂ Y] (L:X→L[ℂ] Y): ∃ C:ℝ,0 ≤ C ∧ ∀ x, ‖L x‖≤C*‖x‖:= ⟨_,norm_nonneg _,fun i=> L.le_opNorm _⟩
lemma form_eval : ∃ C:ℝ,0 ≤ C ∧ ∀ (B: Bundle) i j, ‖B i j‖≤C*‖B‖:=by
  let L (i j:Fiber) : Bundle→ₗ[ℂ] ℂ:= { toFun:=fun P=>P i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  choose T hT H using fun z:Fiber×Fiber=> prefers (X:=Bundle) (Y:=ℂ) ((L z.1 z.2).toContinuousLinearMap)
  exact ⟨∑ z,T z, sum_nonneg fun i _=>hT i,fun B i j=> (H (i,j) B).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=T) (fun k _=> hT k) (mem_univ (i,j))) (norm_nonneg B))⟩

def sticker (B:Bloom k) (i : Site n)(p:Ambient su n):= ∑ a, (∏ j, slotExt (B.petals j) i p (a j)) • B.coeff a
lemma money (B:Bloom k)(i : Site n) (U:Grid n): sticker B i (physical U)=B.taste U i:=by
  unfold sticker Bloom.taste Bloom.hues; simp_rw [slotExt_physical,colorUp_apply,Complex.ofReal_prod]
lemma rate_sticker (B:Bloom k)(i : Site n): ContDiff ℂ ω (sticker B i):=by
  unfold sticker; refine ContDiff.sum (fun a _=> (ContDiff.smul (𝕜:=ℂ) (f:=(fun p:Ambient su n=>∏ j, slotExt (B.petals j) i p (a j))) (g:=fun _=>B.coeff a) ?_ contDiff_const))
  exact contDiff_prod fun j _=> (contDiff_apply ℂ _ (a j)).comp (slotExt_contDiff (B.petals j) i)
lemma price_sticker (B:Bloom k)(i: Site n) {u:ℝ} (h:0<u) (x:Ambient su n) {U:Grid n} (hx:x∈closedBall (physical U) (radius u)) :
    ‖sticker B i x‖≤ |slotConst su|^k*Real.exp (u*∑ j,(B.petals j).length)*(fibreCost* B.price) :=by
  rw [costing, mul_sum, mul_sum]; unfold sticker
  apply (norm_sum_le ..).trans; refine sum_le_sum (fun a _=>?_)
  rw [norm_smul]; apply mul_le_mul ?_ (turning _) (norm_nonneg _) (by positivity); rw [norm_prod]
  have he j : ‖slotExt (B.petals j) i x (a j)‖≤ |slotConst su| * Real.exp (u*(B.petals j).length):= (norm_le_pi_norm _ (a j)).trans ((slotExt_bound U h x hx (B.petals j) i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
  apply (prod_le_prod (s:=univ) (fun j _=> norm_nonneg (slotExt (B.petals j) i x (a j))) (fun i _=> he i)).trans_eq; rw [prod_mul_distrib,← Real.exp_sum]; congr <;> simp [mul_sum] -- try

def carryF : su.Mat→L[ℂ] Bundle:=LinearMap.toContinuousLinearMap (𝕜:=ℂ) {
    toFun:=touch,map_add':=fun i j=> (touch_add ..).symm,map_smul':=fun i j=> Matrix.kronecker_smul .. }

def aval (B:Bloom k)(i j: Row n)(p:Ambient su n):= if stop i.1 B.tail=j.1 then (sticker B i.1 p*(shimmer 0 i.1 B.tail • carryF (stringMat p B.tail i.1))) i.2 j.2 else 0
lemma signed_sticker (B:Bloom k) (U:Grid n)(i j:Row n): aval B i j (physical U)=B.tonic 0 U i j:=by rw [aval, money,stringMat_physical,at_books]; rfl
lemma sticker_out (B:Bloom k)(i j : Row n): ContDiff ℂ ω (aval B i j):=by
  unfold aval; split; swap; exact contDiff_const
  let L : Bundle →ₗ[ℂ] ℂ:= { toFun:=fun G=> G i.2 j.2,map_add':=fun _ _=>rfl,map_smul':=fun _ _=> rfl }
  apply L.toContinuousLinearMap.contDiff.comp (f:=fun p : Ambient su n=> sticker B i.1 p*(shimmer 0 i.1 B.tail • carryF (stringMat p B.tail i.1)))
  exact (rate_sticker B i.1).mul (((carryF.contDiff).comp (stringMat_contDiff (G:=su) B.tail i.1)).const_smul _)

lemma paid_solo (k:ℕ){u:ℝ}(h:0<u): ∃ C:ℝ,0≤C∧∀ n (B: Bloom k) (i j:Row n) (U:Grid n) (x:Ambient su n), x∈closedBall (physical U) (radius u)→ ‖aval B i j x‖ ≤ C* B.paid u:=by
  obtain ⟨W,hW,H⟩:= form_eval
  obtain ⟨C,hC,Cp⟩:= prefers (X:=su.Mat) (Y:=Bundle) carryF
  let Q:= |slotConst su|^k*fibreCost*(C*‖(1:su.Mat)‖)
  have he : 0≤Q:=by unfold Q; have := fibreGe; positivity
  refine ⟨W*Q,mul_nonneg hW he,fun n B i j U x hp=>?_⟩
  have hb:= B.price_nn; let D:= Real.exp (u* B.tail.length);
  have hf : ‖sticker B i.1 x*(shimmer 0 i.1 B.tail • carryF (stringMat x B.tail i.1))‖≤ Q*B.paid u:=by
    apply le_trans (norm_mul_le ..); rw [norm_smul, show ‖shimmer 0 i.1 B.tail‖=1 from ?_,one_mul]
    · have hv:= price_sticker B i.1 h x hp
      have hx := stringMat_bound U (radius_pos h).le x hp B.tail i.1
      have ht := Cp (stringMat x B.tail i.1)
      have hh : (1+radius u)^B.tail.length ≤ Real.exp (u*B.tail.length):=by
        rw [radius,add_sub_cancel,← Real.exp_nat_mul]; apply Real.exp_monotone; nlinarith [show (0:ℝ) ≤ B.tail.length from by positivity]
      apply (mul_le_mul hv (ht.trans (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))) hC)) (norm_nonneg _) ((norm_nonneg _).trans hv)).trans_eq; unfold Q Bloom.paid Bloom.span; push_cast; rw [mul_add,Real.exp_add]; ring
    rw [occ_rays, Flume.pathLength]
  unfold aval; split
  · exact (H _ _ _).trans ((mul_le_mul_of_nonneg_left hf hW).trans_eq (mul_assoc W Q _).symm)
  rw [norm_zero]; exact mul_nonneg (mul_nonneg hW he) (hb.trans (B.paidUp h.le))
end YM.QCD.Eyrie
