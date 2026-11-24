import YM.Gall.Peer
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised Display Beacon Pipes Further.LogJets
variable {u v a:ℝ}{c:Side}{n m:ℕ} {P:BudgetPoint}{o:Site c}{X G:Density c 6}
lemma wealthS (h:Tutor o P (Canvas.foil G X) v n m a)(t:ℝ) : Tutor o P (Canvas.foil G ((↑t:ℂ) • X)) v n m (‖t‖ *a) :=by
     let L:Lat.Fields c 6→L[ℝ] Lat.Fields c 6:= t • ContinuousLinearMap.id ℝ _; let W:= Canvas.foil G X; have he: Canvas.foil G ((t:ℂ) • X)=L ∘ W:=by funext y; exact mul_smul_comm (t:ℂ) _ _
     rw [he]; refine ⟨L.contDiff.contDiffAt.comp _ h.smooth,fun l hl hd=>?_,fun l hl hd i hi=>?_⟩ -- comp norm implicit
     · rw [left_linear _ _ h.smooth hl]; change ‖t • (_: Lat.Fields c 6)‖≤_; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h.large _ hl hd) (norm_nonneg _)
     rw [left_linear _ _ h.smooth hl]; change ‖framesF (purseX o n v) (mantel i (t • (_:Lat.Fields c 6)))‖ ≤ _; rw [map_smul,map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (h.fortune _ hl hd _ hi) (norm_nonneg _)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.wealthS
