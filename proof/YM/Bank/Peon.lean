import YM.Bank.Nine
import YM.Bank.Sour
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bank
open Function Lattice Laurent Bloch Metric RG Precision Filter Finset YM.Next.Free
open YM.Bank Wale Osc Pilot Glyph
open Matrix Exterior Lat Flume Pearl Pinch
open scoped Topology Matrix Matrix.Norms.L2Operator ComplexConjugate BigOperators
variable {j:ℕ}{p q:Momentum}
lemma shaft_v : vase shaft 0 = 0:=by change Para.model ((_) • _)=0; have he:shaft 0=0:=rfl; simp [vase,he,Para.turn,Para.reciprocalP] -- edit
lemma spineW (hp:2≤j):∃ s C:ℝ,0<s ∧0≤C∧∀ (c:Side)(D:Train j)(i j:Fiber), Genie 0 true c (fun p=> vase (Dir D) p i j) (fun p=>vase shaft p i j) s C :=by
   obtain ⟨r,c,C,W⟩:= Pearl.boot hp; have hg:= W (Train.top j)
   obtain ⟨C',V⟩:=Pearl.adder hg.hr; let x:=min 1 c; let b:=max C C'; have hx:0<x:=lt_min one_pos hg.hc
   have hQ v:= (W v).reduce hg.hr le_rfl hx (min_le_right ..) (le_max_left C C')
   have hP:=V.reduce hg.hr le_rfl hx (min_le_left ..) (le_max_right C C')
   obtain ⟨a,ha,hh,H⟩:= cup_z r hg.hr; obtain ⟨s,hS,hR⟩:=hP.source a ha; let K:=max (Pearl.Pinch.purse r x b) (proofD r x b); have ht:0≤K:= hP.cost_q.trans (le_max_left ..)
   refine ⟨s,K,hS.seed,ht,fun c D i j=> ?_⟩
   have hd(q:Site c){p} (h:p∈collar (grid true q) s) : p∈collar (tuning q) a:= ball_subset_ball (mul_le_mul_of_nonneg_right hR (norm_nonneg _)) h
   refine ⟨hS.seed,hS.span,ht,Or.inr rfl, by rw [shaft_v]; rfl,fun p y hp he=>?_,fun p y hp hh=> (H _ (keyboard p) _ (hd p hh)).2.1,fun z p hp h hx=> ?_,fun p hh he=>?_⟩
   · obtain ⟨h',hv⟩:= (hQ D).protectedV hS (keyboard p) (tune_nonzero p) he
     exact ⟨(listenD i j).differentiableAt.comp y h', (Cost.north _ _ _).trans (hv.trans (div_le_div_of_nonneg_right (le_max_left ..) (norm_nonneg _)))⟩
   · have he := period_dir D z (base_subset_realCube zone_pos hp) ⟨h,hx.2⟩; unfold vase; rw [he]
   let q:= tuning p; have ht:= tune_nonzero p; have hu:=keyboard p; have hm:= hP.friend hS hu ht
   have hy: 0< ‖q‖:= norm_pos_iff.mpr ht
   rw [pow_zero]; apply Twin.peek
   change Twin (vase (Dir D) q) (vase shaft q) K (1 /‖q‖) ‖q‖
   have hx : Pearl.Pinch.purse r x b /‖q‖ ≤ K*(1/‖q‖) :=by rw [one_div,← div_eq_mul_inv]; exact div_le_div_of_nonneg_right (le_max_left ..) hy.le
   refine ⟨((hQ D).protectedV hS hu ht hm).2.trans hx,(hP.protectedV hS hu ht hm).2.trans hx,?_⟩
   apply ((hQ D).adjacent hS hu ht hP hm).trans; rw [show K*(1/‖q‖)*‖q‖=K by field_simp]; exact le_max_right ..
end YM.QCD.Bank
#print axioms YM.QCD.Bank.spineW
