import YM.QCD.Grove.Sphere
import YM.QCD.Grove.Cry
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Frost
open Function Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}
private def movedDirs (s : Signed) (b : Site n) (A : Directions G n) : LR G n :=
  ((fun e => if s.flip e.2 then 0 else A (affine s b e.1, s.perm e.2)),
    fun e => if s.flip e.2 then -A (affine s b e.1-step (s.perm e.2), s.perm e.2) else 0)

private theorem pull_increment (s : Signed) (b : Site n) (U : Config G n) (A : Directions G n) (t : ℝ) :
    pull s b (increment U (t • A)) = mix (pull s b U) (t • movedDirs s b A) := by
  ext i
  simp only [pull,Lattice.Step.rotate, Lattice.Step.read,Lattice.Step.used,posDir,Bool.false_xor, mix, increment, movedDirs]
  split <;> simp [*,Work.F03.exp_neg_color]

private theorem pull_jets {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Signed) (b : Site n) (U : Config G n) (f : Config G n → Y) (l : List (Directions G n)) :
    leftDerivs (f ∘ pull s b) l U = mixJets f (l.map (movedDirs s b)) (pull s b U) := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp [mixJets,leftDerivs,ih,pull_increment]
private theorem sum_price {ι Y : Type*} [NormedAddCommGroup Y] (l : List ι) (f : ι → Y) {c : ℝ} (hf : ∀ i∈l, ‖f i‖ ≤ c) :
    ‖(l.map f).sum‖ ≤ (l.length : ℝ)*c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (_ * c) c]
    exact (norm_add_le ..).trans (add_le_add (hf i (by simp)) (ih fun j hj => hf j (by simp [hj])))
-- ext variant Freight
lemma stall {B:BudgetPoint} {f:Config G n→ℝ}{d:ℝ}(U: Config G n)(s: Signed)(b: Site n) (h:Chart B.order f (pull s b U))(hk:∀ l : List (Directions G n), l.length ≤ B.order → (∀ p∈ l, ‖p‖≤ B.threshold)→‖leftDerivs f l (pull s b U)‖ ≤ d)
 (l:List (Directions G n))(hp:l.length ≤ B.order)(hv: ∀ i∈l, ‖i‖ ≤ B.threshold) : ‖leftDerivs (f ∘ pull s b) l U‖ ≤ 2^B.order*d:=by
   let T:= l.map (movedDirs s b); let X:=pull s b U
   have he i (hi:i∈T): ‖i.1‖≤ B.threshold ∧ ‖rotateRight X i.2‖≤ B.threshold:=by
       obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hi; have hh:=hv p hp; constructor
       · apply (pi_norm_le_iff_of_nonneg B.threshold_pos.le).2; intro i; dsimp only [movedDirs]; split; exact norm_zero.le.trans B.threshold_pos.le; exact (norm_le_pi_norm p _).trans hh
       apply (pi_norm_le_iff_of_nonneg B.threshold_pos.le).2; intro i; rw [rotateRight,G.norm_adjoint]; dsimp only [movedDirs]; split; next h=> rw [norm_neg]; exact (norm_le_pi_norm p _).trans hh
       exact norm_zero.le.trans B.threshold_pos.le
   have hz: T.length ≤ B.order:=by simpa only [T,List.length_map]
   have hH i (hi:i∈ convertOrder X T): ‖leftDerivs f i X‖ ≤ d:=by
      obtain ⟨he,h⟩:= (convert_mem X (fun p=>‖p‖≤B.threshold) T he) i hi; exact hk i (he.trans_le hz) h
   have hd : 0≤d:= le_trans (norm_nonneg _) (hk [] (by simp) (by simp))
   rw [pull_jets,mix_convert X T f ?_ h hz]
   · refine (sum_price (convertOrder X T) _ hH).trans ?_; rw [convert_length,Nat.cast_pow,Nat.cast_ofNat]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hz) hd
   intro i hi j hj k; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hi; obtain ⟨j,_,rfl⟩:= List.mem_map.mp hj; dsimp only [movedDirs]; split<;>simp [*]
open Pressure Precision Uniform PhysicalNext.Repeat Trio.Sharp Bid Boulevard
variable (s:Signed)(b:Site n)
-- ext regardless : ∃ fixed.V'
lemma parkL (v:Positions (Primary n G)) : ∃ w:Positions (Primary n G), ‖w‖≤ ‖v‖∧ pull s b (actual v)=actual w:=by
   let A:=shifting b v; let V:=tint G _ A
   let X:=Bid.pulled V s; let W:=(tint G _).symm X
   refine ⟨W,?_,?_⟩
   · apply le_trans _ (low b v); apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; rintro ⟨i,j⟩; change ‖X i j‖≤ _; unfold X Bid.pulled; dsimp only
     split; next h=> change ‖-A (_,j)‖≤_; rw [norm_neg]; exact norm_le_pi_norm A _
     next h=> exact norm_le_pi_norm A _
   rw [actual, show actual W=Precision.represent X from congr_arg Precision.represent ((tint G _).apply_symm_apply _)] -- already unfold actual all?
   have hh:pull s b (actual v)=pull s 0 (actual A):=by unfold A; rw [moved,← pull_one,pull_pull]; simp [Lattice.affine]
   exact hh.trans (by simpa only [V,X,one_smul] using Work.F03.represent_pulled s V (1:ℝ)) -- order
end YM.Push.Local.Frost
