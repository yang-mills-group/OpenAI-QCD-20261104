import YM.QCD.Runnel.Token

/-! # rowcol convolution -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Run
open Lat Lattice Gauge Wilson Cost Function Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {f : Side} {D E F : Type*} [Fintype D] [Fintype E] [Fintype F] [DecidableEq D] [DecidableEq E] [DecidableEq F]
variable {x : D→Site f} {y : E→Site f} {z : F→Site f}
variable {δ b R R' S S' : ℝ} {B : ℕ}
variable {M N : Grid f → ArrayL D E} {K : Grid f → ArrayL E F} {X : Land f D E} {Y : Pays f D E}
lemma duel_nn (h : Pack x y δ b B M R X Y) (i j) : 0≤ duel Y i j b B:= sum_nonneg fun a _=>mul_nonneg (fair ..).le (h.crop ..).1
lemma payme (h : Pack x y δ b B M R X Y) (i j P) : rent b B P * Y i j P ≤ R:= (single_le_sum (fun a _=>mul_nonneg (fair b B a).le (h.crop i j a).1) (mem_univ P)).trans ((single_le_sum (fun a _=>duel_nn h i a) (mem_univ j)).trans (h.spends i))
namespace Heritage
lemma vacant : Heritage x y δ b B 0 0:= by refine ⟨0,0,(fun _ _ _ => Crop.zero),fun i j U=> ?_,?_,?_⟩; · simp [cell]; rfl
                                           all_goals simp [duel]
lemma plus (h : Heritage x y δ b B M R) (e : Heritage x y δ b B N S): Heritage x y δ b B (M+N) (R+S):=by
  obtain ⟨X,Y,h⟩:=h; obtain ⟨Z,W,e⟩:=e; refine ⟨X+Z,Y+W,fun i j p=> (h.crop ..).plus (e.crop i j p),fun i j U=> ?_,fun i=> ?_,fun j=>?_⟩
  · simp only [Pi.add_apply,sum_add_distrib,cell_add,h.sells,e.sells]
  · simpa only [duel, Pi.add_apply,mul_add,sum_add_distrib] using add_le_add (h.spends i) (e.spends i)
  simpa only [duel,Pi.add_apply,mul_add,sum_add_distrib] using add_le_add (h.dues j) (e.dues j)
lemma scalar (w : ℂ) (h : Heritage x y δ b B M R): Heritage x y δ b B (w • M) (‖w‖*R) :=by
  obtain ⟨X,Y,h⟩:=h; let W:= fun i j p=> ‖w‖*Y i j p
  have he i j : duel W i j b B=‖w‖ * duel Y i j b B:=by unfold duel W; rw [mul_sum]; simp_rw [mul_left_comm _ ‖w‖]
  refine ⟨w • X,W,fun i j p=> (h.crop ..).alloy w,fun i j U=> ?_,fun i=> ?_,fun j=>?_⟩
  · simp only [Pi.smul_apply,← smul_sum,h.sells,cell_scale]
  · simp_rw [he, ← mul_sum]; exact mul_le_mul_of_nonneg_left (h.spends i) (by positivity)
  simp_rw [he, ← mul_sum]; exact mul_le_mul_of_nonneg_left (h.dues j) (by positivity)
lemma minus (h : Heritage x y δ b B M R): Heritage x y δ b B (-M) R:=by simpa using h.scalar (-1)
lemma sub (h : Heritage x y δ b B M R) (e : Heritage x y δ b B N S): Heritage x y δ b B (M-N) (R+S):=by rw [sub_eq_add_neg]; exact h.plus e.minus
lemma mono (h : Heritage x y δ b B M R) (hs : R≤S): Heritage x y δ b B M S:= by
  obtain ⟨X,Y,h⟩:=h; exact ⟨X,Y,h.crop,h.sells,fun i=> (h.spends i).trans hs,fun j=> (h.dues j).trans hs⟩
lemma clip (h : Heritage x y δ b B M R) {δ'} (ht : δ'≤δ) : Heritage x y δ' b B M R:=by
  obtain ⟨X,Y,h⟩:=h
  have hh : Kingdom f δ'⊆Kingdom f δ:=Set.iUnion_mono fun _=>Metric.ball_subset_ball ht
  refine ⟨X,Y,fun i j p=> ?_,h.sells,h.spends,h.dues⟩; obtain ⟨hp,hq,hK,hH,hL,hG⟩:=h.crop i j p; exact ⟨hp,hq,fun Z ht=>hK Z (hh ht),fun Z ht=>hH Z (hh ht),hL,hG⟩
lemma meet (h : Heritage x y δ b B M R) (e : Heritage y z δ b B K S) (hd : 0<δ) (hp : 0≤b) (hr : 0≤R) (hs : 0≤S) : Heritage x z δ b B (fun U=> M U * K U) (R*S):=by
  obtain ⟨X,Y,h⟩:=h; obtain ⟨Z,W,e⟩:=e
  let I:=Support f×Support f
  let O (i:D) (a:E) (j:F) (p : Support f) (l : I) : Pulse f→Bundle:= if l.1∪l.2=p then X i a l.1*Z a j l.2 else 0
  let P (i:D) (a:E) (j:F) (p : Support f) (l : I) := if l.1∪l.2=p then Y i a l.1*W a j l.2 else 0
  let Q i j p:=∑ a:E,∑ v:I,P i a j p v
  have hk i j : duel Q i j b B≤∑ a:E, duel Y i a b B * duel W a j b B:=by
    unfold duel Q; simp_rw [mul_sum]; rw [sum_comm]
    refine sum_le_sum fun a _=> ?_; rw [← mul_sum,sum_mul,sum_comm, Fintype.sum_prod_type]; refine sum_le_sum fun u _=>?_ ; rw [mul_sum]; refine sum_le_sum fun v _=>?_
    unfold P; dsimp only; simp only [mul_ite,mul_zero,sum_ite_eq,mem_univ,if_true] -- check
    by_cases hl:Y i a u=0; · simp [hl]
    by_cases hg:W a j v=0; · simp [hg]
    have hh:=(pooled hp B ((h.crop ..).2.1 hl).2 ((e.crop ..).2.1 hg).1)
    exact (mul_le_mul_of_nonneg_right hh (mul_nonneg (h.crop ..).1 (e.crop ..).1)).trans (le_of_eq (by ring))
  refine ⟨fun i j p=>∑ a:E,∑ v:I,O i a j p v, Q,fun i j p=>?_ ,fun i j U=>?_,fun i=> ?_,fun j=>?_⟩
  · refine Crop.cluster _ (fun a _=> Crop.cluster _ (fun v _=> ?_)); unfold O P; split_ifs with hx
    · rw [← hx]; exact (h.crop ..).joined (e.crop ..) hd
    exact Crop.zero
  · -- regroup
    simp_rw [Finset.sum_apply] -- check fn
    rw [cell_mul,sum_comm]; refine sum_congr rfl fun a _=>?_
    rw [sum_comm, ← h.sells i a,← e.sells a j,Fintype.sum_prod_type,sum_mul]; apply sum_congr rfl; intro u _; rw [mul_sum]; refine sum_congr rfl fun v _=>?_ ; simp [O,ite_apply]
  · apply (sum_le_sum (fun j _=>hk i j)).trans; rw [sum_comm]
    simp_rw [← mul_sum]
    exact (sum_le_sum (fun a _=> mul_le_mul_of_nonneg_left (e.spends a) (duel_nn h i a))).trans (by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (h.spends i) hs)
  apply (sum_le_sum (fun i _=>hk i j)).trans; rw [sum_comm]
  simp_rw [← sum_mul]; exact (sum_le_sum (fun a _=> mul_le_mul_of_nonneg_right (h.dues a) (duel_nn e a j))).trans (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (e.dues j) hr)
end Heritage
end YM.QCD.Run
