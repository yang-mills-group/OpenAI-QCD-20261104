import YM.QCD.Rudder.Soil

/-! # all family locally analytic along complex Cart rays with support summability -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Revolve
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace ContDiff
variable {n : Side} {I J : Type} {m j : ℕ} {σ θ : ℝ} (C : su.Color)
lemma am_append (t: Site n) (Z : Weather n) (a : Step) (w : Walk):
    amass C t (a::w) Z=amass C t [a] Z*amass C t w Z:=by
  have hx : routeM t 1 [a]=leg t 1 a:=by simp[routeM]
  unfold amass; rw [hx,show routeM t 1 (a::w)=leg t 1 a*routeM t 1 w from rfl]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc]; congr 1; rw [leg_day,ride_mul,ride_mul,ride_mul]; congr 1; funext i
  have he : colour (a.read (1:Grid n) i)=1:=by cases h : a.neg <;> simp only [Step.read,h,Bool.false_eq_true,↓reduceIte,Pi.one_apply,inv_one] <;> rfl
  change touch (lunar _ _)*touch (_• colour _)= touch (lunar _ _)*touch (_• colour (a.read (1:Grid n) i))* touch _; simp_rw [touch_mul]; apply congr_arg touch; simp only [Equiv.refl_apply]
  rw [he,bill,bill,bill, add_zero,← spend]; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one]; rfl

def gate (n:Side): (Site n→Bundle) →L[ℂ] Sheet n:= LinearMap.toContinuousLinearMap { toFun:= rides (Equiv.refl _),map_add':=fun F X=>(ride_add ..).symm,map_smul':=fun c X=> (ride_smul ..).symm }
lemma hooked (t : Site n) (w):Differentiable ℂ (amass C t w):=by
  unfold amass; refine ((gate n).differentiable.comp (f:=fun Z i=> TouchL (lunar C (bill Z i w))) ?_).mul (differentiable_const _)
  apply differentiable_pi.mpr; intro i; fun_prop
lemma petals_open (W : Bloom m) (x : Site n): Differentiable ℂ (fun Z=> blossom C W Z x):=by
  unfold blossom; apply Differentiable.fun_sum; intro i _; refine Differentiable.smul_const ?_ _
  generalize (univ:Finset (Fin m))=S
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty]; exact differentiable_const _
  | insert a s ha ih=> simp_rw [prod_insert ha]; exact ((bore_diff C _).comp (billD (wrap n (W.petals a).offset+x) (Lattice.square _ _))).mul ih
lemma siltD (W:Bloom m)(t:Site n):Differentiable ℂ (silt C t W):=by unfold silt; exact ((gate n).differentiable.comp (differentiable_pi.mpr fun i=> petals_open C W i)).mul (hooked C t W.tail)
lemma siloD (G:Gleam)(t:Site n):Differentiable ℂ (silo C t G):=(hooked C t G.w).mul (differentiable_const _)
structure Weathered (σ θ:ℝ) : Prop where
 degree : 0<σ
 dry : 0<θ
 controls : ∀ z : ℂ, ‖z‖ ≤ θ → ‖TouchL (lunar C z)‖ ≤ Real.exp σ
lemma appoint (h:0<σ) : ∃ θ, Weathered C σ θ:=by
  have hp : ‖TouchL (lunar C 0)‖ < Real.exp σ:=by rw [lunar_nil,show TouchL 1=1 from touch_one,oneNorm]; exact Real.one_lt_exp_iff.mpr h
  have he:= TouchL.continuous.comp (liveD C).continuous |>.norm.continuousAt (x:=0)
  obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (he.eventually (gt_mem_nhds hp))
  exact ⟨r/2, h, half_pos hr, fun z hz=> le_of_lt (show _ < Real.exp σ from H (mem_ball_zero_iff.mpr (hz.trans_lt (half_lt_self hr))))⟩
variable {C}
lemma hailing (h: Weathered C σ θ) (t: Site n) (Z: Weather n) (hZ:‖Z‖ ≤ θ) (w : Walk): ‖amass C t w Z‖≤ Real.exp (σ*w.length):=by
  induction w with
  | nil=> unfold amass; simp only [bill,lunar_nil]; change ‖rides (Equiv.refl _) (fun _ : Site n=>touch 1)*1‖ ≤ _; simp_rw [touch_one,ridden,mul_one,oneNorm,List.length_nil,Nat.cast_zero,mul_zero,Real.exp_zero]; rfl
  | cons a w ih=>
    rw [am_append,List.length_cons]; push_cast; rw [mul_add,mul_one,add_comm,Real.exp_add]; apply (norm_mul_le ..).trans; refine mul_le_mul ?_ ih (norm_nonneg _) (Real.exp_pos _).le; unfold amass; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (rotation_price (circle ..))).trans
    apply rides_size _ (Real.exp_pos _).le; intro i; exact h.controls _ ((bill_bound Z i [a]).trans (by simpa using hZ))
lemma silo_swell (hW: Weathered C σ θ)(t:Site n): ∃ f:Gleam→ℝ, (∃ w : ℝ,∀ G,f G=w*G.rate σ)∧∀ (G:Gleam) Z,‖Z‖≤θ → ‖silo C t G Z‖≤ f G:=by
  obtain ⟨w,h,H⟩:= Wages.spinSize n; refine ⟨fun G=> w*G.rate σ,⟨w,fun _=>rfl⟩,fun G Z hu=>?_⟩
  exact (norm_mul_le ..).trans ((mul_le_mul (hailing hW t Z hu _) (H _) (norm_nonneg _) (Real.exp_pos _).le).trans (le_of_eq (mul_left_comm ..))) -- unfold
lemma silt_swell (hW : Weathered C σ θ)(m : ℕ)(t: Site n):∃ w : ℝ,∀ (W : Bloom m) Z,‖Z‖≤θ → ‖silt C t W Z‖ ≤ w*W.paid σ:=by
  have hc i: Continuous (fun z : ℂ=> ‖bore C i z‖):=(bore_diff C i).continuous.norm
  choose c H using fun i=> ((isCompact_closedBall (0:ℂ) (4*θ)).image (hc i)).bddAbove
  let B:=∑ i:su.ColorIndex,|c i|
  refine ⟨B^m,fun W Z h=>?_⟩
  have ht x : ‖blossom C W Z x‖ ≤ B^m*W.price:=by
    unfold blossom; apply (norm_sum_le ..).trans; unfold Bloom.price; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [norm_smul,norm_prod]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hh j : ‖bore C (i j) (tick (W.petals j) x Z)‖≤B:=by
      refine ((H _ ⟨_,mem_closedBall_zero_iff.mpr ?_,rfl⟩).trans (le_abs_self _)).trans (single_le_sum (fun j _=> abs_nonneg (c j)) (mem_univ _)); unfold tick
      apply (bill_bound Z ..).trans; simpa [Lattice.square] using mul_le_mul_of_nonneg_left h (by norm_num : 0≤(4:ℝ))
    simpa using Finset.prod_le_prod (s:= Finset.univ) (fun _ _=> norm_nonneg _) fun j _=> hh j
  refine (norm_mul_le ..).trans ((mul_le_mul (rides_size _ (mul_nonneg (pow_nonneg (show 0≤B by unfold B; positivity) _) W.price_nn) _ _ ht) (hailing hW t Z h _) (norm_nonneg _) ?_).trans ?_)
  · exact mul_nonneg (pow_nonneg (show 0≤B by unfold B; positivity) _) W.price_nn
  unfold Bloom.paid; rw [mul_assoc]; rw [mul_comm W.price]; gcongr
  · exact W.price_nn
  · exact hW.degree.le
  exact Nat.le_add_right .. 
  -- wrong order
end YM.QCD.Rudder
