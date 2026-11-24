import YM.QCD.Cedar.Worth

/-!
# The reference determinant; pointwise book for a true background
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ} (P : Plan j) (F : Flight j k) (h : f.val=c.val*F.L.val) (t : Site f) (U : Grid f)
lemma tiedSpin (a : Spike): tied F h t U*onSpin f a=onSpin c a*tied F h t U:= by
  let r:=sliceL F h
  have hh (w): scoop r*routeM t U w*onSpin f a=onSpin c a*(scoop r*routeM t U w):=by rw [Matrix.mul_assoc,(spinM ..).eq,← Matrix.mul_assoc,show scoop r*onSpin f a=onSpin c a*scoop r from roots ..,Matrix.mul_assoc]
  unfold tied lineF; simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.sum_mul,Matrix.mul_sum]; dsimp only [r] at hh; simp_rw [hh]
lemma ticketStar : Chiral (chirality f) (vaultF P F h t U):=by
  let J:=chirality f; let Q:=tied F h t U
  have hχ : Q*J=chirality c*Q:= tiedSpin ..
  have hx := congr_arg (·ᴴ) hχ; simp only [Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose J,← Matrix.star_eq_conjTranspose (chirality _), show star J=J from chi_star,chi_star] at hx
  have he : J*(Qᴴ*Q)*J=Qᴴ*Q:=by
    rw [← Matrix.mul_assoc J Qᴴ,hx,Matrix.mul_assoc _ Q J,hχ,Matrix.mul_assoc,← Matrix.mul_assoc (chirality c),chi_sq,Matrix.one_mul]
  unfold Chiral vaultF; rw [star_add, mul_add,add_mul, show star (wood P t F.wing U)=_ from spinO .., he]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]; rfl
lemma ticket_pos : 0<(vaultF P F h t U).det.re:=det_pos chi_sq (ticketStar ..) (sealPos ..) (lease P F h t U)
lemma ticket_inv : IsUnit (vaultF P F h t U).det:=(lease P F h t U).unit (sealPos ..)
lemma ticket_B : ‖(vaultF P F h t U)⁻¹‖ ≤ stamp P F.L:=(lease P F h t U).reciprocal (sealPos ..)|>.trans_eq (inv_inv _)
lemma prize (L : Side) : ∃ w q : ℝ,0<w∧0≤q∧q<1 ∧ ∀ F : Flight j k,F.L=L→ ∀ (c f : Side) (h : f.val=c.val*F.L.val) t U,
    ‖Cost.notch w (vaultF P F h t U)‖≤q:=by
  obtain ⟨C,hc,H⟩:= overall (k:=k) P
  obtain ⟨w,q,hp,hq,ha,hB⟩:= choose_rate _ (C+massL L^2) (sealPos P L) (by positivity)
  refine ⟨w,q,hp,hq,ha,fun F h c f h' t U=>?_⟩
  subst L; exact contracts _ (lease P F h' t U) (H F c f h' t U) hp hq hB
lemma tree_zero :vaultF P F h 0 1=father F h:=by unfold vaultF; rw [bare_this]; rfl
@[fun_prop] lemma tied_cont : Continuous (tied F h t):=by unfold tied lineF; fun_prop
@[fun_prop] lemma canopy : Continuous (vaultF P F h t):=by unfold vaultF; fun_prop
end YM.QCD.Pine
