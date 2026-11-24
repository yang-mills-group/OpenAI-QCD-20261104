import YM.QCD.Smoke.Roof
import YM.Next.FREE_KERNELS.Signed

/-! # Account in the presence of orientations. Curvature-anchor separation flips with a pair-dependent shift; cannot ignore it for the marginal license. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical
variable {c n:Side}{I:Type}
lemma stamp_abs (s:Signed)(p:PlaqAxes):|turned s p|=1:=by unfold turned; dsimp only; split_ifs <;> norm_num
lemma card_side (s t: Signed)(p : PlaqAxes): PlaqAxes.rotate s (PlaqAxes.rotate t p)=PlaqAxes.rotate (s*t) p:=by
  let a:=p.val.1; let b:=p.val.2; let A:= t.perm a; let B:=t.perm b
  have hp : A ≠ B:= t.perm.injective.ne p.property.ne
  ext -- inspect
  all_goals unfold PlaqAxes.rotate PlaqAxes.ordered; dsimp only; simp only [Signed.mul_perm_apply]
  all_goals rcases lt_or_gt_of_ne (t.perm.injective.ne p.property.ne) with h|h
  all_goals simp only [min_eq_left ‹_ < _›.le,max_eq_right ‹_ < _›.le,min_eq_right ‹_ < _›.le,max_eq_left ‹_ < _›.le] -- try
  all_goals first| rw [min_comm] | rw [max_comm]
-- one-sided sign product orientation
lemma xor_cost (a b:Bool): (if a.xor b then (-1:ℝ) else 1)=(if a then -1 else 1)*(if b then -1 else 1):=by cases a <;> cases b <;> norm_num
lemma face_fee (s t :Signed)(p:PlaqAxes): turned (s*t) p=turned t p*turned s (p.rotate t):=by
  rcases lt_or_gt_of_ne (t.perm.injective.ne p.property.ne) with h|h
  · simp only [turned,Signed.mul_perm_apply,Signed.mul_flip,PlaqAxes.rotate,PlaqAxes.ordered,h,min_eq_left h.le,max_eq_right h.le, ↓reduceIte]
    simp only [xor_cost]; ring
  rcases lt_or_gt_of_ne ((s*t).perm.injective.ne p.property.ne) with H|H <;> simp only [Signed.mul_perm_apply] at H <;> simp only [turned,Signed.mul_perm_apply,Signed.mul_flip,PlaqAxes.rotate,PlaqAxes.ordered,H,H.not_gt,h.not_gt,min_eq_right h.le,max_eq_left h.le, ↓reduceIte]
  all_goals simp only [xor_cost]; ring

def debitG (p:PlaqAxes):Cover:=step p.val.1+step p.val.2
def reverseG : Signed:= ⟨Equiv.refl _,fun _=>true⟩
lemma negX (x:Cover): reverseG.act x= -x:=by funext i; simp [reverseG,Signed.act]
lemma offsetX (s:Signed)(p:PlaqAxes)(x:Cover): (Face.send (reverseG*s) 0 (x,p)).1= -(Face.send s 0 (x,p)).1-debitG (PlaqAxes.rotate s p):=by
  have hx (y:Axis) : ((posDir y).rotate (reverseG*s))=((posDir y).rotate s).rev:=by cases h:s.flip y <;> simp [Step.rotate,posDir,Signed.mul_perm,reverseG,h,Step.rev]
  unfold Face.send Face.lower; simp only [Signed.act_mul,debitG,affine,negX, add_zero, atFace,PlaqAxes.rotate,PlaqAxes.ordered, Step.rotate,posDir]
  rcases lt_or_gt_of_ne (s.perm.injective.ne p.property.ne) with g|g <;> cases h:s.flip p.val.1 <;> cases hh:s.flip p.val.2 <;>
    simp [Step.vec,reverseG,h,hh, g.le] <;> abel
lemma size_signedG (s:Signed)(x:Cover): Laurent.size (s.act x)=Laurent.size x:=by unfold Laurent.size; rw [← Equiv.sum_comp s.perm (fun i=> (s.act x i).natAbs)]; apply sum_congr rfl; intro i _; rw [Signed.act_at]; split <;> simp
lemma size_posG (s:Signed)(x:Cover)(p:PlaqAxes) : size (Face.send s 0 (x,p)).1 ≤size x+2:=by
  have ht (x:Cover)(a: Step): size (x+if a.neg then a.vec else 0)≤size x+1:=by split; apply (size_add ..).trans; rw [Iteration.step_size]; simp
  have hx:= ht (s.act x) ((posDir p.val.1).rotate s); unfold Face.send Face.lower; dsimp only [affine,atFace]; rw [add_zero]; apply (ht _ _).trans; rw [size_signedG] at hx; omega
lemma send_wrap (s:Signed)(x:Cover)(p:PlaqAxes): Face.send (R:=Per n) s 0 (wrap n x,p)=Prod.map (wrap n) id (Face.send s 0 (x,p)) := by
  refine Prod.ext ?_ rfl; unfold Face.send Face.lower atFace; simp only [Prod.map_apply,affine,add_zero,map_add]; rw [← wrap_signed]; split <;> split <;> simp [Step.vec, apply_ite (wrap n)]
-- reflected axis selection and difference stamp
lemma mirror_axes (a:Axis)(p:PlaqAxes): PlaqAxes.rotate (Signed.mirror a) p=p:=by rcases p with ⟨⟨i,j⟩,h⟩; apply Subtype.ext; change (min i j,max i j)=(i,j); exact Prod.ext (min_eq_left h.le) (max_eq_right h.le)
lemma reverse_axes (p:PlaqAxes): PlaqAxes.rotate reverseG p=p:=mirror_axes 0 p
lemma mirror_stamp (p:PlaqAxes)(a:Axis): turned (Signed.mirror a) p=if a∈(plaquette p).val then -1 else 1:=by
  unfold plaquette turned; dsimp only [Signed.mirror]; simp only [Equiv.refl_apply,p.property,if_true, mul_one,decide_eq_true_eq,mem_insert,mem_singleton]
  split_ifs <;> simp_all [p.property.ne,p.property.ne.symm]
lemma reversed (p:PlaqAxes): turned reverseG p=1:=by unfold reverseG turned; simp [p.property]
lemma spots (p q:PlaqAxes):∃ s:Signed,p.rotate s=q:=by
  let f(p:PlaqAxes):Fin 2→Axis:= ![p.val.1,p.val.2]; have hp(p:PlaqAxes):Injective (f p):=by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [f,p.property.ne,p.property.ne.symm]
  obtain ⟨σ,H⟩:= Equiv.Perm.exists_extending_pair (f p) (f q) (hp p) (hp q); refine ⟨⟨σ,fun _=>false⟩,Subtype.ext ?_⟩
  change (min (σ _) (σ _),max _ _) = _; rw [show σ p.val.1=q.val.1 from H 0, show σ p.val.2=q.val.2 from H 1,min_eq_left q.property.le,max_eq_right q.property.le]
end YM.QCD.Fog
