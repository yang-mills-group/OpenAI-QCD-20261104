import YM.Parishes.Tucking
import YM.Parishes.Braid
import YM.Parishes.Lifts
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open MassiveQCD.Plate QCD.Acre QCD.Acre.Rails MassiveQCD.Plate.Card MassiveQCD.Plate.Card.Iris MassiveQCD.Ribbon MassiveQCD.Apron MassiveQCD.Cupola QCD.Loom.Fleet Ursell
open QCD.Patron QCD.Kites QCD.Ruby QCD.Loom QCD.Jets.Touch Bank.Hike QCD.Creek NormedSpace
variable {I J:Type}
local notation "T"=> Spine Unit
local notation "K"=> Keys c 6
set_option quotPrecheck false
variable (b₀:Cover)(p:Bool) (X:QCD.Patron.Rail c 6 I)(Pt:BudgetPoint)
local notation "r†"=>fun (_:Unit)=>p
local notation "o†"=>fun (_:Unit)=>wrap c b₀
local notation "o₁"=> wrap c b₀
local notation "V★"=>bears X
local notation "R!"=> rootR T K
local notation "d!"=> withdraw 6 (fun (_:Unit)=>wrap c b₀) v
local notation "b!"=> banknote 6 (fun (_:Unit)=>wrap c b₀) v
local notation "αT"=> (3/16+1:ℝ)
variable {Q:TaperHol}{U:Hol su} (A:Exhibit U) (x:Label d) (L:Side)(y:ℝ)
variable (hm: moored x.val p)
variable (hx:Pill X Pt.threshold (fan L θ y) Pt.B (3/16) (taxK L y 4))(hV:1 ≤fan L θ y)
local notation "W!"=> fan L θ y
local notation "uRK"=> goldM p
variable (hp:Pilot Q A d m k n j r α β)(hP: Pt.order=m)(ht:Pt.power=k)(hB:Pt.B=highR L y)(hR: Marginal L θ y)(hq:30*(r+1) ≤ c.val)
open Stair
lemma weightedL (S:Finset Cover)(u : Dirac (Nearest S 6))(hk:1 ≤ v) : Creek.load (fun _=>v) (Carte.perigee c b₀ S u) ≤ v^Fintype.card (Pairs (Nearest S 6))*‖u‖:=by
    let T':= Carte.Hem.tongue (c:=c) S b₀; let F:= Pairs (Nearest S 6); let w :F→ℝ:=fun _=>v
    have h : Creek.load (fun _=>v) (Carte.perigee c b₀ S u) = ‖T' (wscale (A:=Pairs (Nearest S 6)) w u)‖:=by
       unfold Creek.load; unfold Carte.perigee; -- `engine` lemma. prove map equality linear
       apply congr_arg; let L : Matrix (Nearest S 6) (Modes c 6) ℂ := belt c S b₀; let P:=Matrix.fromBlocks L 0 0 L; change changeVars _ (changeVars P _)= changeVars P (changeVars _ _); rw [← AlgHom.comp_apply,← AlgHom.comp_apply,←change_mul,←change_mul]; congr 2; ext i j; simp [Matrix.diagonal_mul,Matrix.mul_diagonal,w]; ring
    rw [h]; apply (Carte.Hem.tongue_pay S b₀ _).trans; change Creek.load (A:=Pairs (Nearest S 6)) w u ≤ _; rw [Creek.dry w (fun _=>zero_lt_one.trans_le hk),Grass.norm_def,Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; simpa [w,F] using mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk i.card_le_univ) (norm_nonneg (coef i u)) -- actual [A]
-- From fixed charts.My.AX. all-or-none unit.
noncomputable def sheds (d:ℕ): Label d→L[ℂ] ContinuousMap (CoverConfig su) (Dirac (Nearest (A.t d) 6)):= by
    let P: Label d→ₗ[ℂ] ContinuousMap (CoverConfig su) (Dirac (Nearest (A.t d) 6)):= {
         toFun:=fun x=>⟨fun u=> porch (A.t d) u (A.lead d x), porch_c ..⟩
         map_add':=fun x y=>ContinuousMap.ext (fun u=>map_add ((porch (A.t d) u).comp (A.lead d)) ..)
         map_smul':=fun z x=>ContinuousMap.ext (fun u=>map_smul ((porch (A.t d) u).comp (A.lead d)) ..) }
    exact P.toContinuousLinearMap
abbrev nJ (A:Exhibit U)(d:ℕ):= Fintype.card (Pairs (Nearest (A.t d) 6))
lemma metricS (V:Grid c)(ht:1 ≤ v): Creek.load (fun _=>v) (graphs (c:=c) d A b₀ x V) ≤ v^nJ A d*‖sheds A d‖*‖x‖:=by
    let R:= expandAt (wrap c b₀) V; let S:=(sheds A d) x; change Creek.load (fun _=>v) (Carte.perigee c b₀ (A.t d) (S R)) ≤ _; apply (weightedL b₀ _ _ ht).trans
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm ..).trans ((sheds A d).le_opNorm _)) (pow_nonneg (zero_le_one.trans ht) _)
lemma breathM (d:ℕ): ∃ C:ℝ,1 ≤ C ∧∀ x:Label d, ‖x‖ ≤ C*wealth x.val 1 1:=by
   let F:=Module.finBasis ℂ (Label d); obtain ⟨C,hC,H⟩:= payFrame (d:=d) F; refine ⟨C,hC,fun x=>?_⟩; have hx:=H x 1 1; apply le_trans _ hx; have hf:dimming (1:ℝ) 1 d x=x:=by
      apply Subtype.ext; apply (zBasis d).repr.injective; ext i; change Stative.fare _ x.val 1 1 = coord i x.val -- elaborate explicit
      simp [Stative.fare, rank_fee]
   unfold Sieve.watch; rw [hf]; exact le_rfl -- basis defeq hatch.L.
local notation "c!"=>Stair.feeS d Pt.threshold⁻¹
lemma scopeW (hv:1 ≤v): wealth x.val 1 1 ≤ c!*wealth x.val Pt.threshold v:=by
   let Y :BudgetPoint:={Pt with threshold:=1, threshold_pos:=zero_lt_one, threshold_le:=le_rfl}; have hT : 1≤Pt.threshold⁻¹:= (one_le_inv₀ Pt.threshold_pos).2 Pt.threshold_le
   unfold wealth; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_; let A (i:Rings d):= Pt.threshold⁻¹^life i.val.1*Pt.threshold⁻¹^i.val.2.card; have h:i∈(Finset.univ:Finset (Rings d)):= mem_univ i; have ht: A i≤ feeS d Pt.threshold⁻¹:= (Finset.single_le_sum (f:=A) (fun j _=>by unfold A; positivity) h).trans (le_add_of_nonneg_left zero_le_one)
   change ‖chartL Y 1 i x‖ ≤ _; exact (gain (P:=Y) (Q:=Pt) x (zero_lt_one.trans_le hT) zero_le_one (zero_le_one.trans hv) ((inv_mul_cancel₀ Pt.threshold_pos.ne').symm.le) (one_le_mul_of_one_le_of_one_le hT hv) i).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.metricS
