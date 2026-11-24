import YM.QCD.Pearl.Culp

/-! # the kinetic remainder before tracing -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para Pinch
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {η c b B r q ρ ε : ℝ} {p k: Momentum}{F : Momentum → Para}
def spanX (F : Momentum→Para)(A B:Shine→Bundle)(p k:Momentum):= (vase F k * A (-p,k+p)*vase F (k+p)* A (p,k)).trace-(vase F k* B (p,k)).trace
def crown (X:Bundle)(p k:Momentum):= (vase shaft k * X * vase shaft (k+p) * X).trace

def twinball (η : ℝ):= ball (0:Shine) η
lemma vigor (h:0<η):twinball η ⊆ twin η:=by
  have he (k:Momentum)(hk:‖k‖<η): k∈strip η:=fun i=> (Complex.abs_im_le_norm _).trans_lt ((norm_le_pi_norm k i).trans_lt hk)
  intro p hp; change _∧ _; rw [twinball,mem_ball_zero_iff,Prod.norm_def,max_lt_iff] at hp; exact ⟨he _ hp.1,he _ hp.2⟩
namespace Wall
variable {A:Shine→ Bundle} (h: Wall η b A) (he:0<η)
def freshB (η b:ℝ):=4*b/η
include h he
lemma posX : 0≤ b:= (norm_nonneg _).trans (h.s _ (vigor he (mem_ball_self he)))
lemma edgeX (v:Shine) (hv:v∈ twin η): ‖A v-A 0‖ ≤ freshB η b *‖v‖:=by
  have ht:= h.s 0 (vigor he (mem_ball_self he)); have hr:= h.posX he
  by_cases hh: ‖v‖<η/2
  · have hk:=Run.lastwig A he (fun i hi=> h.d i (vigor he hi)) (fun i hi=> h.s i (vigor he hi)) (mem_ball_zero_iff.mpr hh); rw [sub_zero] at hk; apply hk.trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold freshB; apply (div_le_div_iff₀ (half_pos he) he).mpr; nlinarith
  push Not at hh; exact (norm_sub_le ..).trans ((add_le_add (h.s v hv) ht).trans (by unfold freshB; rw [div_mul_eq_mul_div,le_div_iff₀ he]; nlinarith))
end Wall

lemma members (hk:k∈baseCube)(he:ε*Real.pi ≤ η/2)(hx:0<η)(hε:0≤ε) (hz:‖p‖ < ε*‖k‖): (-p,k+p)∈ twin η ∧ (p,k)∈twin η:= by
  have hp : ‖p‖<η/2:= hz.trans_le ((mul_le_mul_of_nonneg_left (cap_base hk) hε).trans he)
  have ht : p∈strip η:= fun i=> lt_trans ((Complex.abs_im_le_norm _).trans_lt ((norm_le_pi_norm p i).trans_lt hp)) (half_lt_self hx)
  have hK := mem_cube_real (base_subset_realCube (half_pos hx) hk) (half_pos hx)
  refine ⟨⟨strip_negX ht,(ball_inside_cube (η:=η) hK ?_).1⟩, ht,(cube_mono (half_le_self hx.le) hK).1⟩
  simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left, sub_half] using hp
lemma skyline {A B X Y :Bundle} {b c d e :ℝ}(h : ‖A-X‖≤b)(he: ‖B-Y‖ ≤ c) (hA : ‖X‖≤d)(hB:‖B‖≤ e):‖A*B-X*Y‖≤ b*e +d*c:=by
  rw [show A*B-X*Y=(A-X)*B+ X*(B-Y) by rw [sub_mul,mul_sub]; abel]
  refine (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul h hB (norm_nonneg _) ((norm_nonneg _).trans h))) ((norm_mul_le ..).trans (mul_le_mul hA he (norm_nonneg _) ((norm_nonneg _).trans hA))))
lemma step_norm (a:Axis): ‖(step a:Momentum)‖=1 :=by
  apply le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_) ?_
  · intro i; rw [step_apply]; split <;> simp
  simpa using norm_le_pi_norm (step a:Momentum) a
lemma streak (u : ℂ)(a:Axis): ‖(u • step a:Momentum)‖=‖u‖:=by rw [norm_smul,step_norm,mul_one]

variable (h:Pinch F r c B)(hS: Pinch shaft r c B) (e : Bright r c B ε) (hη: ε* Real.pi≤η/2) (he:0<η) (hk:k∈baseCube)(h₀:k≠0)
def wobble (r c B η b:ℝ):= proofD r c B*b + purse r c B*(2*Wall.freshB η b)
def wobble2 (r c B η b q:ℝ):= (Fintype.card Fiber:ℝ)*(2*wobble r c B η b *purse r c B * b + purse r c B * q)
include h hS e hη he hk h₀
lemma ambient {A S: Shine→Bundle} (hA:Wall η b A)(hQ: Wall η q S)(hp:‖p‖< ε*‖k‖): ‖spanX F A S p k - crown (A 0) p k‖ ≤ wobble2 r c B η b q /‖k‖:=by
  let J := k+p; let X:=(-p,J); let U:=(p,k); let K:=A 0; let f:=Wall.freshB η b
  have hJ : J∈ball k (ε*‖k‖):= by unfold J; simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hp
  have heJ:= h.friend e hk h₀; let P:=purse r c B; let D:=proofD r c B; let t:= ‖k‖; have ht: 0<t:=norm_pos_iff.mpr h₀; have hb:=hA.posX he; have hh:0≤f:= by unfold f Wall.freshB; positivity
  have hf:‖K‖ ≤ b := hA.s 0 (vigor he (mem_ball_self he))
  obtain ⟨hL,hR⟩:= members hk hη he e.seed.le hp
  have hT: ‖p‖ ≤ t:= hp.le.trans (mul_le_of_le_one_left ht.le e.span)
  have hX:‖A X-K‖ ≤ f*(2*t):=by
    apply (hA.edgeX he _ hL).trans; refine mul_le_mul_of_nonneg_left (max_le ?_ (h.near hJ e.span)) hh; change ‖-p‖≤ _; rw [norm_neg]; linarith
  have hU:‖A U-K‖ ≤ f*(2*t):= (hA.edgeX he _ hR).trans (mul_le_mul_of_nonneg_left (max_le (hT.trans (by linarith)) (show t≤2*t by linarith)) hh)
  have hP : 0≤P:= h.cost_q
  let L:=wobble r c B η b
  have ha y x (hy:y∈ ball k (ε*t)) (hx:x∈ twin η) (hv:‖A x-K‖≤ f*(2*t)): ‖vase F y*A x-vase shaft y*K‖≤L:= by
    refine (skyline (h.adjacent e hk h₀ hS hy) hv (hS.protectedV e hk h₀ hy).2 (hA.s _ hx)).trans_eq ?_; change D*b+P/t*_ = D*b+P*(2*f); field_simp
  have hI: ‖vase shaft k*K‖ ≤ P/t*b:= (norm_mul_le ..).trans (mul_le_mul (hS.protectedV e hk h₀ heJ).2 hf (norm_nonneg _) (by positivity))
  have hY: ‖vase F J*A U‖ ≤ P/t*b:= (norm_mul_le ..).trans (mul_le_mul (h.protectedV e hk h₀ hJ).2 (hA.s _ hR) (norm_nonneg _) (by positivity))
  have hy:= skyline (ha k X heJ hL hX) (ha J U hJ hR hU) hI hY
  have hM:= (norm_mul_le (vase F k) (S U)).trans (mul_le_mul (h.protectedV e hk h₀ heJ).2 (hQ.s _ hR) (norm_nonneg _) (by positivity))
  rw [spanX,crown,mul_assoc (vase F _*_),mul_assoc (vase shaft _*_),sub_right_comm,← Matrix.trace_sub];
  refine (norm_sub_le ..).trans ((add_le_add ((trace_cost ..).trans (mul_le_mul_of_nonneg_left hy (by positivity))) ((trace_cost ..).trans (mul_le_mul_of_nonneg_left hM (by positivity)))).trans_eq ?_); unfold wobble2; dsimp only [P,L,t] at *; ring
lemma airlift {A S:Shine→Bundle}(hA:Wall η b A)(hQ: Wall η q S)(a:Axis) (x:ℂ) (hx:x∈ball 0 (ε*‖k‖)):
    DifferentiableAt ℂ (fun t:ℂ=>spanX F A S (t • step a) k - crown (A 0) (t • step a) k) x:=by
  let L (z:ℂ):Momentum:= z • step a
  let G (z:ℂ): Shine:=(-(L z), k+L z)
  have hu : ‖L x‖ < ε*‖k‖:= by unfold L; rw [streak]; exact mem_ball_zero_iff.mp hx
  obtain ⟨hL,hR⟩:= members hk hη he e.seed.le hu
  have hh: k+ L x ∈ ball k (ε*‖k‖):= by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hu
  let Z:Bundle→L[ℂ] ℂ := (Matrix.traceLinearMap Fiber ℂ ℂ).toContinuousLinearMap
  have hv: Differentiable ℂ L := by unfold L; fun_prop
  have hp : Differentiable ℂ G := by unfold G; fun_prop
  have hi : DifferentiableAt ℂ (fun t=> k+L t) x:= by fun_prop
  have hV : DifferentiableAt ℂ (fun t=> vase F (k+L t)) x:= (h.protectedV e hk h₀ hh).1.comp (f:=fun t=>k+L t) x hi
  have hG : DifferentiableAt ℂ (fun t=> vase shaft (k+L t)) x:=(hS.protectedV e hk h₀ hh).1.comp (f:=fun t=>k+L t) x hi
  have hU:= hv.differentiableAt (x:=x) |>.prodMk (differentiableAt_const k)
  have h1:= ((((differentiableAt_const (vase F k)).mul ((hA.d _ hL).comp (f:=G) x (hp x))).mul hV).mul ((hA.d _ hR).comp x hU));
  unfold spanX crown; exact ((Z.differentiableAt.comp x h1).sub (Z.differentiableAt.comp x ((differentiableAt_const _).mul ((hQ.d _ hR).comp x hU)))).sub (Z.differentiableAt.comp x (((differentiableAt_const (vase shaft k*A 0)).mul hG).mul (differentiableAt_const _)))
end YM.QCD.Pearl
