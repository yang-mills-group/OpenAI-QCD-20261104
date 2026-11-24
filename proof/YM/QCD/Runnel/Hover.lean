import YM.QCD.Runnel.Foot

/-! # op norm in tube follows from absolute heritage -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Metric
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {f : Side} {D E : Type*} [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
variable {x : D→Site f} {y : E→Site f} {δ b R : ℝ} {B m : ℕ} {M : Grid f→ArrayL D E} {X : Land f D E} {Y : Pays f D E}
lemma chute_sum (M : ArrayL D E) (u : Vec (E×Fiber)) (i:D): fiber (lead M u) i=∑ j, op (cell M i j) (fiber u j):=by
  ext1 a; change _=WithLp.ofLp (∑ j,op (cell M i j) (fiber u j)) a; rw [WithLp.ofLp_sum,Finset.sum_apply]
  change ∑ _,_= _; rw [Fintype.sum_prod_type]; rfl
lemma wind_op (hR : 0≤R) (M : ArrayL D E) (d : D → E → ℝ) (hw : ∀ i j, ‖cell M i j‖≤ d i j)
    (h : ∀ i,∑ j,d i j≤R) (e : ∀ j,∑ i,d i j≤R): ‖M‖≤R:=by
  have ht i j : 0≤d i j:=(norm_nonneg _).trans (hw i j)
  rw [lead_norm]; refine (lead M).opNorm_le_bound hR (fun u =>?_)
  let v (j:E):= fiber u j
  have hm i : ‖fiber (lead M u) i‖^2 ≤ R*∑ j,d i j *‖v j‖^2:=by
    rw [chute_sum]
    have hh : ‖∑ j:E,op (cell M i j) (v j)‖≤ ∑ j,d i j*‖v j‖:= (norm_sum_le ..).trans (sum_le_sum (fun j _ => (leanBound (cell M i j) (v j)).trans (mul_le_mul_of_nonneg_right (hw i j) (norm_nonneg _))))
    refine (pow_le_pow_left₀ (norm_nonneg _) hh _).trans ((Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ (f:=fun j=>d i j) (g:=fun j => d i j*‖v j‖^2) (fun j _=> ht i j) (fun j _=> mul_nonneg (ht i j) (by positivity)) ?_).trans (mul_le_mul_of_nonneg_right (h i) (Finset.sum_nonneg (fun j _=>mul_nonneg (ht i j) (by positivity)))))
    intro j _; exact le_of_eq (by ring)
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),norms,mul_pow,pow_two R, norms]
  apply (sum_le_sum (fun i _=> hm i)).trans; rw [← mul_sum, sum_comm,mul_assoc R]; refine mul_le_mul_of_nonneg_left ?_ hR; rw [mul_sum]; refine sum_le_sum fun j _=>?_ ; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (e j) (sq_nonneg _)

def bearer (X : D→E→Bundle): ArrayL D E:= Matrix.of fun p q=> X p.1 q.1 p.2 q.2
def bear : (D→E→Bundle)→L[ℂ] ArrayL D E:= LinearMap.toContinuousLinearMap { toFun:= bearer,map_smul':=fun _ _=>rfl,map_add':=fun _ _=>rfl }
def winch (X : Land f D E) (U : Pulse f) := bearer (fun i j=>∑ P,X i j P U)
section
variable {C G : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup G] [NormedSpace ℂ G]
lemma lastwig {U V:C} (F : C → G) (hd : 0<δ) (h : ∀ i∈ ball U δ,DifferentiableAt ℂ F i)
    (hv : ∀ i∈ball U δ, ‖F i‖≤R) (hu : V∈ball U (δ/2)): ‖F V-F U‖ ≤ R/(δ/2)*‖V-U‖:=by
  letI : NormedSpace ℝ C := NormedSpace.restrictScalars ℝ ℂ C
  have hm : ball U (δ/2)⊆ball U δ:=ball_subset_ball (half_le_self hd.le)
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun i hi=> (h i (hm hi)).hasFDerivAt.hasFDerivWithinAt) (fun i hi=> wind hd h hv hi) (convex_ball U (δ/2)) (mem_ball_self (by positivity)) hu
end
namespace Pack
variable (h : Pack x y δ b B M R X Y)
include h
lemma winched (U : Grid f): winch X (settled U)=M U:=by ext ⟨i,a⟩ ⟨j,r⟩; simp only [winch,bearer,Matrix.of_apply,h.sells]; rfl
lemma won (U : Pulse f) (hu : U∈Kingdom f δ): DifferentiableAt ℂ (winch X) U:=by
  refine (bear (D:=D) (E:=E)).differentiableAt.comp (f:=fun Z=>fun i j=>∑ P,X i j P Z) _ ?_
  exact differentiableAt_pi.mpr fun i=>differentiableAt_pi.mpr fun j=>DifferentiableAt.fun_sum (fun P _=> (h.crop i j P).2.2.1 U hu)
lemma empire (hb : 0≤b) (hr : 0≤R) (U : Pulse f) (hu : U∈Kingdom f δ) : ‖winch X U‖≤ R:=by
  apply wind_op hr (winch X U) _ _ h.spends h.dues; intro i j
  change ‖∑ P,X i j P U‖ ≤ _
  apply (norm_sum_le ..).trans; exact sum_le_sum fun P _=> ((h.crop i j P).2.2.2.1 U hu).trans (le_mul_of_one_le_left ((h.crop i j P).1) (market hb B P))
lemma wiggle (hb : 0≤b) (hr : 0≤R) (hd : 0<δ) (Z : Grid f) (U : Pulse f) (hu : U∈ball (settled Z) (δ/2)): ‖winch X U-M Z‖ ≤ R/(δ/2)*‖U-settled Z‖:=by
  rw [← h.winched]
  have hH : ball (settled Z) δ⊆Kingdom f δ:=fun _ h=>Set.mem_iUnion.mpr ⟨Z,h⟩
  exact lastwig _ hd (fun i hi=> h.won i (hH hi)) (fun i hi=> h.empire hb hr i (hH hi)) hu
lemma sold_g (U : Grid f) (k : Frame f): M (gauge k U)=circulant x k*M U*star (circulant y k):=by
  ext ⟨i,a⟩ ⟨j,r⟩; change cell (M (gauge k U)) i j a r=cell (circulant x k*M U*star (circulant y k)) i j a r
  rw [gyro,← h.sells,← h.sells]; simp_rw [fun P=> ((h.crop i j P).2.2.2.2.2 U k),mul_sum,sum_mul]
end Pack
lemma Heritage.value (h : Heritage x y δ b B M R) (hd : 0<δ) (hb : 0≤b) (hr : 0≤R) (U : Grid f): ‖M U‖ ≤ R:= by obtain ⟨X,Y,h⟩:=h; rw [← h.winched]; exact h.empire hb hr _ (citizenship _ hd U)
end YM.QCD.Run
