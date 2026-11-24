import YM.QCD.Garden.Tray

/-!
# pre-ratio scaling interaction step at a given pair of analytic widths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f L:Side}{j k m:ℕ}{I:Type}{η σ B C A:ℝ}
lemma frc (W: Bloom m) (t:ℝ) : 0≤ W.paid t:=mul_nonneg (Real.exp_pos _).le W.price_nn

def bouquet (B C η:ℝ)(m:ℕ):= Real.exp ((4+8*(m:ℝ))*η)*(B*(B*((Fintype.card (Fin m→ PlaqAxes):ℝ)*C^m)))
variable {P:Flight j k} {R:Columns P.L} (W: Bloom m) (r: Site P.L)
lemma tray_price (he:0≤η)(hfit:η≤σ*P.L.val)(h:B≥0)(h':0≤C) (hQ:∀ (u:Site P.L), Width η B (fork P u)) (ht:Width (η*(1+m)) B (unFork P r)) (hp : (R none).strip η C) :
    SumBudget (fun i:Note m=> (jar P R W r i).paid η) (bouquet B C η m * W.paid σ) :=by
  let E:= (4+8*(m:ℝ))*η; let t:=η*(1+m)
  let V:=arrives r (stop 0 W.tail)
  let L u := Real.exp (t*size u)*‖unFork P r u‖; let J u:= Real.exp (η*size u)*‖fork P V u‖
  let M (z:Address m):= Real.exp (∑ i,η*size (z.2 i))*|brew R W r z|
  have hM : SumBudget M ((Fintype.card (Fin m→ PlaqAxes):ℝ)*C^m):= by
    refine Iteration.Cost.product (Iteration.Cost.finite (α:=Fin m→PlaqAxes) (C^m) (by positivity)) (fun i=>?_)
    have he k : Width η C (mer R W r (i k) k) := hp _ _
    have hu:= Iteration.Cost.pi he
    simp only [prod_const,card_univ,Fintype.card_fin] at hu
    simpa only [M, brew,Real.exp_sum, Finset.abs_prod, Real.norm_eq_abs,prod_mul_distrib] using! hu
  let g:= Iteration.Cost.prod (show SumBudget J B from hQ _) (fun _=> hM) (Iteration.Cost.nonneg hM)
  have hx:= Iteration.Cost.prod (show SumBudget L B from ht) (fun _=>g) (Iteration.Cost.nonneg g)
  have HH:= Iteration.Cost.scale hx (Real.exp E*W.paid σ) (mul_nonneg (Real.exp_pos _).le (frc ..))
  refine Iteration.Cost.enlarge (Iteration.Cost.mono HH (fun n=>frc ..) ?_) (le_of_eq (by unfold E bouquet; ring))
  rintro ⟨u,v,z⟩; unfold Bloom.paid; -- inspect
  refine (mul_le_mul (Real.exp_monotone (tms P R W r u v z he hfit)) (jar_price ..) (Bloom.price_nn _) (Real.exp_pos _).le).trans_eq ?_
  simp only [E,L,J,t,M,Real.exp_add,V]; ring

abbrev Tin (P:Flight j k) (m:ℕ) (I:Type):= I × Site P.L × Note m
def tray (P:Flight j k)(R:Columns P.L)(F:I→Bloom m) : Tin P m I →Bloom m:= fun i=>jar P R (F i.1) i.2.1 i.2.2

lemma tray_funds {F:I→Bloom m}(hP:Fractal F σ A)(he:0≤η)(hfit:η≤σ*P.L.val)(h:0≤B)(hp:0≤C)(hu:0<m)
    (hQ:∀ (u:Site P.L), Width η (B*slope P.L/(P.L.val:ℝ)) (fork P u) ∧ Width (η*(1+m)) (B*slope P.L/(P.L.val:ℝ)) (unFork P u)) (ht : (R none).strip η (C/(P.L.val:ℝ)^2)) :
    Fractal (tray P R F) η (bouquet B C η m/(P.L.val:ℝ)^(2*m-1) * A) := by
  let L:ℝ:= P.L.val; let M:= bouquet (B*slope P.L/L) (C/L^2) η m
  have hy : 0<L:= side_pos _; have hM: 0≤M:=by unfold M bouquet; have hh:=slope_pos P.L; positivity
  have H : (Fintype.card (Site P.L):ℝ)*M=bouquet B C η m/L^(2*m-1):=by
    have hz : L^(2*m)= L^(2*m-1)*L:= by rw [← pow_succ]; congr; omega
    have hs : slope P.L^2=L⁻¹:=by rw [Kit.slope, inv_pow,Real.sq_sqrt hy.le]
    unfold M bouquet; rw [site_card,Nat.cast_pow,div_pow,← pow_mul,hz]
    change L^4 * _=_; set x:=slope P.L
    field_simp
    field_simp at hs; linear_combination B^2*C^m*hs
  have he' : SumBudget (fun i=> (tray P R F i).paid η) (bouquet B C η m/L^(2*m-1)*A):=by
    rw [← H]; refine Iteration.Cost.product (Iteration.Cost.scale (show SumBudget _ A from ⟨fun i=>frc (F i) _,hP.bills,hP.bill⟩) ((Fintype.card (Site P.L):ℝ)*M) (by positivity)) (fun i=>?_)
    erw [mul_assoc]; exact Iteration.Cost.product (Iteration.Cost.finite (α:=Site P.L) (M*(F i).paid σ) (mul_nonneg hM (frc ..))) (fun j=>tray_price (F i) j he hfit (Iteration.Cost.nonneg (hQ j).2) (div_nonneg hp (by positivity)) (fun r=>(hQ r).1) (hQ j).2 ht)
  exact ⟨he, fun i=> jar_spin _ _ _ _ (hP.sect i.1) _, he'.2.1,he'.2.2⟩
end YM.QCD.Garden
