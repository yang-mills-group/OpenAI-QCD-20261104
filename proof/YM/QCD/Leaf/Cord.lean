import YM.QCD.Rudder.Spout
import YM.QCD.Runnel.Crest
import YM.Next.SCHEDULE.Circuit

/-! # saturation of bosonic leg slots using physical chord not harmonic extrapolation -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf
open Run Kit Lat Function Finset Lattice RG Rudder Filter Matrix Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator InnerProductSpace Classical
variable {n : Side}
-- lollip
namespace Paths
def ringW (W:Slot): Walk:= Lattice.square W.plaq.1.1 W.plaq.1.2
def torch (W:Slot): Walk:= W.walk++ringW W++ Lattice.reverse W.walk
def valueM (W:Slot)(x : Site n) (U : Grid n):su.El:=travel U x (torch W)
def trueF (W:Slot)(x:Site n) (U:Grid n):su.El:=faceValue U (wrap n W.offset+x,W.plaq)
lemma torch_value (W:Slot)(x:Site n)(U:Grid n) : valueM W x U= let g:= travel U x W.walk; g * trueF W x U*g⁻¹:=by
  unfold valueM trueF torch faceValue ringW
  -- travel_at
  have hx : stop x W.walk=wrap n W.offset+x:=by unfold Slot.offset; rw [wrap_stop, add_comm]
  dsimp only; rw [travel_append,travel_append,stop_append, hx, square_stop,← hx,travel_reverse]
lemma recognized (W:Slot)(x:Site n)(U:Grid n): W.atSite U x=su.curvature (valueM W x U):=by
  unfold Slot.atSite Slot.eval faceValue; simp only [travel_at,map_zero,zero_add,torch_value,Gauge.curvature_conjugate]; rfl
lemma torch_pay (W:Slot)(x:Site n)(U:Grid n): su.chord (valueM W x U)=su.chord (trueF W x U):=by simp [torch_value]
lemma length_max (W:Slot) : (torch W).length ≤ 2*W.length:=by simp [torch,Lattice.reverse,Slot.length,ringW,Lattice.square]; omega

def strand (P:Pulse n)(a : Step)(x: Site n): Mat:= if a.neg then P.2 (a.used x) else P.1 (a.used x)
lemma string (U:Grid n) (a)(x): strand (settled U) a x=colour (a.read U x):=by unfold strand Step.read; split <;> rfl
lemma reachC (x:Site n)(a:Step): Differentiable ℂ (fun P:Pulse n=> strand P a x):=by unfold strand; split_ifs <;> fun_prop
lemma strand_p (P Q:Pulse n) (x:Site n)(a:Step): ‖strand P a x-strand Q a x‖ ≤ ‖P-Q‖:=by have hi:= load P (a.used x) Q; unfold strand; split <;> first| exact hi.2| exact hi.1

def pursueP (P: Pulse n)(x:Site n): Walk→Mat
 | []=>1
 | a::w=>strand P a x * pursueP P (x+a.vec) w
lemma pursuit (U: Grid n)(x:Site n)(W:Walk): pursueP (settled U) x W=colour (travel U x W):=by
  induction W generalizing x with
  | nil=>rfl
  | cons a w ih=> rw [pursueP,Lattice.travel,string,ih]; rfl
lemma reachP (x:Site n)(W:Walk): Differentiable ℂ (fun P:Pulse n=> pursueP P x W):=by
  induction W generalizing x with
  | nil=> exact differentiable_const _
  | cons a w ih=> exact (reachC x a).mul (ih (x+a.vec))

lemma orb (U:su.El) : ‖(colour U)‖≤1:= by apply rotation_price; exact ⟨su.mat_star_mul _,su.mat_mul_star _⟩
lemma strand_use {p:ℝ} (Z:Pulse n)(U:Grid n)(a)(x)(h:‖Z-settled U‖≤p): ‖strand Z a x‖≤1+p:=by
  have hi := (norm_sub_norm_le (strand Z a x) _).trans ((strand_p Z (settled U) x a).trans h); rw [string] at hi; linarith [orb (a.read U x)]
lemma pose {p:ℝ} (Z:Pulse n)(U:Grid n)(W)(x)(h:‖Z-settled U‖≤p): ‖pursueP Z x W‖ ≤ (1+p)^W.length:=by
  have hh: 0≤p:= (norm_nonneg _).trans h
  induction W generalizing x with
  | nil=>simp [pursueP]
  | cons a w ih=>rw [pursueP,List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (strand_use _ _ _ _ h) (ih _) (norm_nonneg _) (by positivity))
lemma pose_gap {p:ℝ}(Z:Pulse n)(U:Grid n)(W)(x)(h:‖Z-settled U‖ ≤ p): ‖pursueP Z x W-pursueP (settled U) x W‖ ≤ (W.length:ℝ)*(1+p)^W.length*p :=by
  have hh:0 ≤ p:= (norm_nonneg _).trans h
  induction W generalizing x with
  | nil=>simp [pursueP]
  | cons a w ih=>
    set V:=x+a.vec (R:=Per n); specialize ih V
    let f:= fun Y:Pulse n=> strand Y a x; let g:=fun Y:Pulse n=> pursueP Y V w; let X:=settled U
    change ‖f Z*g Z-f X*g X‖ ≤ _; rw [show f Z*g Z-_= f Z*(g Z-g X) + (f Z-f X)*g X by noncomm_ring]
    have ht:‖g X‖ ≤ 1:= by unfold g X; rw [pursuit]; exact orb _
    refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul (strand_use _ _ _ _ h) ih (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul ((strand_p Z (settled U) x a).trans h) ht (norm_nonneg _) hh))).trans ?_)
    rw [List.length_cons]; push_cast
    calc
      _ ≤ (1+p)*(w.length*(1+p)^w.length*p)+p*(1+p)^(w.length+1):=by gcongr; exact one_le_pow₀ (le_add_of_nonneg_right hh)
      _ = _:=by rw [pow_succ]; ring

lemma char_tr (V : su.El) : 2 - ((colour V).trace + (colour V⁻¹).trace)/3=((su.chord V^2:ℝ):ℂ):=by
  have ht: (colour V⁻¹).trace=star (colour V).trace := Matrix.trace_conjTranspose _
  have hv: (colour V).trace+star (colour V).trace=2*((colour V).trace.re:ℂ):=by apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hh : (su.repDim:ℝ)=3:=by norm_num [su]
  rw [ht,hv,su.chord_price]; push_cast; unfold Gauge.price; rw [hh]; push_cast; change (2:ℂ)-2*↑(trace (colour V)).re/3= 2*(1-↑(trace (colour V)).re/3); ring
lemma price_c (V : su.El)(i): stringC i ((1/2:ℂ) • (colour V-colour V⁻¹))=((su.curvature V i:ℝ):ℂ):=by
  let H : su.Mat := (1/2:ℝ) • (su.mat V-su.mat V⁻¹); have he : H=(show Mat from (1/2:ℂ) • (colour V-colour V⁻¹)):=by
    apply Matrix.ext; intro i j; change (1/2:ℝ) • (_:ℂ)=(1/2:ℂ) • (_:ℂ); simp [colour,Matrix.sub_apply]; rfl
  refine Eq.trans (show _ = metricC su i H from ?_) (league su i H ?_); · rw [he, chartC]
  unfold H; rw [star_smul,Gauge.mat_inv,star_sub,star_star]; simp only [star_trivial,smul_sub]; abel
end Paths
end YM.QCD.Leaf
