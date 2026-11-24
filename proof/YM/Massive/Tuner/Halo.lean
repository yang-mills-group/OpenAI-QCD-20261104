import YM.QCD.Reef.Balm
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {D E:Type*} [Fintype D][Fintype E][DecidableEq D][DecidableEq E]{A B:ℝ}
open Raft
variable {η : ℝ}
lemma uniformVeil (P:Plan j)(Ω:ParcelR)(he:Ω.Rates η)(q:ℝ) : ∃ Z:ℝ,∀ v:Train j,∀ c:Side,∀ V:Raft.ParcelR.SunR Ω,∀ (u:ℝ),|u|≤q→∀ σ:ℝ, 0<σ → σ≤1 →∀ X:Grid c, Beam ((Fount.FieldB Ω V c σ P v + u • 1) X) 0 Z:=by -- rename
   obtain ⟨K,r,R,hR,hk,hP⟩:= Loom.banner P 1 zero_le_one;
   obtain ⟨δ,T,n,hx,ht,hH⟩:= vaultP he.hr he.hs (show (0:ℝ) ≤1 from zero_le_one) Ω.d Ω.c; obtain ⟨x0,h0,H0⟩:=meal_cost K 0; obtain ⟨x1,h1,H1⟩:=meal_cost n 0
   refine ⟨x0*R+x1*(T*(1+q)),fun v c V u hu σ hh hv X=>?_⟩; have he:= hH V.X V.Y c n le_rfl σ u hh hv
   have hw:(Fount.FieldB Ω V c σ P v + u • 1) X= wood P 0 v X+trunkM V.X V.Y σ u c X:=by unfold Fount.FieldB trunkM; simp only [Pi.add_apply,Pi.smul_apply]; abel
   rw [hw]; exact (skirtR X _ id id (hP c v) hR x0 h0 (H0 c)).add ((skirtR X _ id id he (mul_pos hx (pow_pos hh _)) x1 h1 (H1 c)).up (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hv hu) ht.le) h1))
end YM.QCD.Globe
