import YM.Clays.Pane
import YM.Tinus.Nim
import YM.Clays.Reeds
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c L:Side}{N B i j k n F:ℕ}{I D:Type}[Fintype I] {A2 T2 Ae At M W0 X:ℝ}{a C t b w x v θ η ξ z m:ℝ}
-- polynomial bound after plan commissioned. Applies deterministic estimates.Support.
namespace Rates
local notation "X" k:arg => ((k:ℝ)+1)
structure Fuel (f:ℕ→ℝ) : Prop where
    gains:∃ (K:ℝ)(n:ℕ),0 ≤ K ∧∀ i:ℕ,|f i| ≤ K*((i:ℝ)+1)^n
lemma Fuel.add (f g:ℕ→ℝ)(h:Fuel f)(hx:Fuel g):Fuel (fun i=>f i+g i):=by
     obtain ⟨k,n,hk,h⟩:= h.gains; obtain ⟨l,m,hL,h'⟩:=hx.gains; refine ⟨k+l,n+m,add_nonneg hk hL,fun i=>?_⟩; have hp:1 ≤ (i:ℝ)+1:= by simp
     rw [add_mul]; exact (abs_add_le ..).trans (add_le_add ((h _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega)) hk)) ((h' i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega)) hL)))
lemma Fuel.mul (f g:ℕ→ℝ)(h:Fuel f)(hp:Fuel g):Fuel (fun i=>f i*g i):=by
     obtain ⟨k,n,hk,h⟩:=h.gains; obtain ⟨l,m,hL,h'⟩:=hp.gains; refine ⟨k*l,n+m,mul_nonneg hk hL,fun i=>?_⟩; rw[abs_mul,pow_add]; exact (mul_le_mul (h i) (h' i) (abs_nonneg (g i)) ((abs_nonneg _).trans (h i))).trans_eq (by ring)
lemma Fuel.cons (a:ℝ): Fuel (fun _=> a):=⟨|a|,0,abs_nonneg _,fun _=>by rw [pow_zero,mul_one]⟩
lemma Fuel.self : Fuel (fun i:ℕ=> (i:ℝ)):= ⟨1,1,zero_le_one,fun i=>by simp⟩
lemma Fuel.pow (f:ℕ→ℝ)(hf:Fuel f) (k:ℕ): Fuel (fun i:ℕ=> f i ^ k):=by
     induction k with|zero=>simp only [pow_zero]; exact Fuel.cons 1|succ k ih=>simp only [pow_succ]; exact Fuel.mul _ _ ih hf
lemma Fuel.absF (f:ℕ→ℝ)(hf:Fuel f) :Fuel (fun i:ℕ=> |f i|):=by constructor; simpa only [abs_abs] using hf.gains
local macro "payments_aes" : tactic => `(tactic| repeat' first | exact Fuel.cons _|exact Fuel.self | apply Fuel.add|apply Fuel.mul|apply Fuel.pow)
local notation "μ0"=> (1/8:ℝ)
local notation "u1"=> (24/256:ℝ)
local notation "α1"=> (25/256:ℝ)
local notation "ε"=> (1/256:ℝ)
open Stags Footprint Push.AbsoluteSums.Reserves Animals
set_option maxHeartbeats 400000 in
lemma polyT (k n F i j:ℕ)(T2 Ae At C θ z:ℝ): Fuel (fun B:ℕ=> growthP B k n F i j T2 Ae At C θ z):=by
     have h : Fuel (fun B=> hullP B F * C):=by unfold hullP; payments_aes
     have hb: Fuel (fun B=> Stags.bonus F B (1/256)):=by unfold Stags.bonus Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
     have hw: Fuel (fun B=> anth (1/256) (25/256+2*(1/256)) B):=by unfold anth Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
     have hc:Fuel (fun B=> absP B k n F (1/256) C):=by unfold absP roy hullP; payments_aes
     have hg:Fuel (fun B=>pledgeP B k n F C Ae At T2):=by unfold pledgeP; repeat' first | exact hw | exact hb | exact hc|exact Fuel.cons _| apply Fuel.add | apply Fuel.mul
     have hr:Fuel (fun B=>riseP i j B (1/256) u1):=by unfold riseP; payments_aes
     unfold growthP; dsimp only; repeat' first|exact h|exact hr|exact hg|exact hb|exact Fuel.cons _|apply Fuel.add|apply Fuel.mul
end Rates
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.Rates.polyT
