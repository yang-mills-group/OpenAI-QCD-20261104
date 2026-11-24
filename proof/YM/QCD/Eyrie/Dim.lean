import YM.QCD.Eyrie.Harm

/-! # grade zero Bloom. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Pine Flume
open Revolve Rudder Cost
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {n : Side} {I : Type} {k : ℕ}
def cargo:Spike→L[ℂ] Bundle:=
  let B : Spike→ₗ[ℂ] Bundle:={toFun:=wave,map_add':=fun i j=> (wave_add ..).symm,map_smul':=fun i j=> Matrix.smul_kronecker ..}
  B.toContinuousLinearMap
def duty:= ‖cargo‖+1
lemma duty_pos : 0<duty:=by unfold duty; positivity
lemma tributary (X : Spike):‖wave X‖≤duty*‖X‖:= by
  exact (cargo.le_opNorm X).trans (mul_le_mul_of_nonneg_right (by unfold duty; linarith) (norm_nonneg X))

def queen (B : Gleam): Bloom 0:= ⟨B.w,isEmptyElim, fun _=>wave B.B⟩
lemma queen_price (B:Gleam) (δ:ℝ):(queen B).paid δ≤ duty* B.rate δ:=by
  unfold queen Bloom.paid Bloom.span Bloom.price Gleam.rate; simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero, Finset.sum_const,card_univ,Fintype.card_pi,Finset.prod_empty,one_smul]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (tributary B.B) (by positivity)
lemma queen_score (B:Gleam)(v): (queen B).hues v=wave B.B:=by
  unfold queen Bloom.hues; simp
lemma queen_rides (B:Gleam)(t:Site n)(U:Grid n):(queen B).tonic t U=B.dept t U:=by unfold Bloom.tonic Gleam.dept Bloom.taste; simp_rw [queen_score]; exact (spinM t U B.B B.w).eq.symm
lemma queen_fit (B:Gleam): (queen B).Spins:=by
  intro u v; rw [queen_score,queen_score, (interlace ..).eq, Matrix.mul_assoc,(show touch (colour u)*star (touch (colour u))=1 from (touch_u (x:=colour u) ⟨su.mat_star_mul _,su.mat_mul_star _⟩).2),mul_one]
lemma trek {Q:I→Gleam}{δ C:ℝ}(h: Wages δ C Q): Fractal (queen∘Q) δ (duty*C):=by
  let B (i:I):= (queen (Q i)).paid δ
  have hn i : 0≤ B i:=le_trans (Bloom.price_nn ..) ((queen (Q i)).paidUp h.po)
  have hu:= h.val.mul_left duty; have hs : Summable B:=hu.of_nonneg_of_le hn (fun i=> queen_price ..)
  refine ⟨h.po, fun i=>queen_fit _,hs,(hs.tsum_le_tsum (fun i=> (queen_price (Q i) δ)) hu).trans ?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.cap duty_pos.le

def winding (x : Site n) (w : Walk)(t : Site n)(U : Grid n) := shimmer t x w • touch (colour (travel U x w))
def entryR {t : Site n} (U : Grid n)(w : Walk) (P: Site n→Bundle) (i j : Row n):=
    if stop i.1 w=j.1 then (P i.1*winding i.1 w t U) i.2 j.2 else 0
lemma pinned (U : Grid n)(t : Site n)(w : Walk):
    routeM t U w=rides (Equiv.addRight (wrap n (stop 0 w))) (fun i=>winding i w t U):=by
  induction w with
  | nil => unfold winding; change (1: Sheet n)= rides _ (fun _=> (1:ℂ) • touch (colour 1)); simp only [stop, map_zero, one_smul,show colour (1:su.El)=1 from rfl,touch_one]
           rw [show Equiv.addRight (0:Site n)=Equiv.refl (Site n) from ?_, ridden]; ext1 i; change i+0=i; simp
  | cons a w ih=>
    change leg _ _ _*routeM t U w=_; rw [ih,leg_day,ride_mul]; congr 1
    · ext1 i
      rw [show Equiv.addRight _ i=stop i (a::w) from (wrap_stop ..).symm]; rw [stop]; exact (wrap_stop ..).symm
    funext i; unfold winding hitch; rw [shimmer, travel]; simp only [colour_mul, show ∀ u (X: Mat), touch (u • X)= u • touch X from (fun (u:ℂ) X=> Matrix.kronecker_smul ..),Matrix.mul_smul, Matrix.smul_mul, touch_mul, smul_smul]; rw [mul_comm]; rfl
lemma at_books (U: Grid n)(t:Site n)(B:Bloom k) (i j: Row n): B.tonic t U i j=entryR (t:=t) U B.tail (B.taste U) i j:=by
  unfold entryR Bloom.tonic; rw [pinned,ride_mul]; change (if _=_ then _ else _)= _; rw [wrap_stop]; rfl
lemma number_g (U : Grid n)(t:Site n)(i j: Row n)(w : Walk) : routeM t U w i j=entryR (t:=t) U w (fun _=>1) i j:=by rw [pinned]; unfold entryR; rw [wrap_stop, Matrix.one_mul]; rfl
end YM.QCD.Eyrie
