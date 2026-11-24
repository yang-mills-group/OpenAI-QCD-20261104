import YM.Poised.Caps
/-! # spin jets through all moments, including bar entries without imposing oriented support on output -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Steed
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
variable (P:Flight j k) (h:l.val=c.val*P.L.val)
variable (hk:4≤k)
include hk
-- Coupling-independent reserve
lemma shareY (L:Side) (hP:4≤j) : ∃ W Z:ℝ,0<W ∧ 0≤Z∧∀ (P:Flight j k), P.L=L→∀ x:Cover, Width W Z (gears P x):=by
   obtain ⟨σ,C,hσ,hC,H⟩:=reserves_font hP hk
   obtain ⟨b,hb,K⟩:= Sparks.float_norm
   let I:=Lat.Fiber× Lat.Fiber; let U:ℝ := Fintype.card I * C; let A:=Kit.slope L; have hA:0<A:=QCD.Kit.slope_pos _; let p:ℝ:=L.val; have hp:0<p:=by unfold p; positivity
   refine ⟨σ,b*(U*A/p),hσ,?_ ,fun P hG x=>?_⟩
   · unfold U I; positivity
   let r:= wrap P.L x; let F (i:I) (u:Cover):= ‖fonts P [] r i.1 i.2 u‖
   have he (x:I): RG.SumBudget (fun u=> Real.exp (σ * size u)*F x u) (C*A/p):= by unfold A p; rw [← hG]; simpa only [List.length_nil,add_zero,pow_one] using! H P r [] (by simp) x.1 x.2
   have hs : SumBudget (fun u=> ∑ i:I,Real.exp (σ * size u)* F i u) (U*A/p):=by
     have hc : Summable (fun u=> ∑ i:I, Real.exp (σ * size u) * F i u):= summable_sum fun i _=> (he i).2.1
     refine ⟨fun i=>sum_nonneg (fun j _=> (he j).1 _),hc,?_⟩; rw [Summable.tsum_finsetSum (f:=fun i u=> Real.exp (σ*size u)*F i u) fun i _=>(he i).2.1]; apply (sum_le_sum fun i _=> (he i).2.2).trans; unfold U; simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
   have hx (x:Cover) : ‖Garden.sheath P r x‖≤ b*∑ i:I,F i x:=by
     have ha (i:I): 0≤ F i x:=norm_nonneg _; apply K _ _ (sum_nonneg fun i _=>ha i)
     intro i j; change F (i,j) x≤_; exact single_le_sum (s:=Finset.univ) (f:=fun i=>F i x) (fun i _=>ha i) (mem_univ (α:=I) (i,j))
   refine Work.F08.budget_minor (g:=fun u=> b * ∑ i:I,Real.exp (σ*size u)*F i u) ?_ (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) fun i=>?_
   · refine ⟨fun i=>mul_nonneg hb (hs.1 _),hs.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hs.2.2 hb
   exact le_trans (mul_le_mul_of_nonneg_left (hx i) (Real.exp_pos _).le) (le_of_eq (by rw [←Finset.mul_sum,mul_left_comm]))
set_option maxRecDepth 2100 in
lemma archY (L:Side)(hJ:4≤j) : ∃ W Z:ℝ,0<W∧0≤Z∧∀ (P:Flight j k),P.L=L→∀ (u v:Pipes.Shell)(x:Cover),Width W Z (arch P u v x):=by
    choose Lc hL using fun (i:Pipes.Shell ×Pipes.Shell)=> spin_patch i.1 i.2
    let M:= ∑ i,‖Lc i‖; have hM:0≤M:= sum_nonneg fun i _=> ContinuousLinearMap.opNorm_nonneg (Lc i)
    obtain ⟨A,C,hA,hC,H⟩:= shareY hk L hJ; refine ⟨A,M*C,hA,mul_nonneg hM hC,fun P hG u v x=>?_⟩; let f(i:Cover):= Real.exp (A*size i)*‖gears P x i‖; have h:= H P hG x
    refine Work.F08.budget_minor (g:=fun i=>M*f i) ⟨fun i=>mul_nonneg hM (h.1 _),h.2.1.mul_left _,?_⟩ (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_
    · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hM
    intro i; have hE:‖arch P u v x i‖ ≤ M*‖gears P x i‖:=by rw [show arch P u v x i=Lc (u,v) (gears P x i) from (hL (u,v) _).symm]; exact ((Lc _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i=> ‖Lc i‖) (fun i _=> ContinuousLinearMap.opNorm_nonneg (Lc i)) (mem_univ _)) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans_eq (mul_left_comm ..)
end Steed
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Steed.archY
