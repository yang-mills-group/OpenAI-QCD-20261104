import YM.Kwick.Corn
/-! Supplied Pan to Bowl on two orientations (powers8.D). tolerance rates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
variable {p q:ℕ}(α a ε η L Lb u v M1 M2 γ:ℝ)(x y:Z)(j:Axis)(P Q:BudgetPoint)(w w' r μ M W:ℝ)
variable {n:ℕ}{p:ℕ→Z}{Pt:ℕ→BudgetPoint}{A V:ℕ→ℝ}{Mv:Axis→ℕ→ℝ}(h:Pan n p Pt Mv A V u α a ε)
variable {K:ℕ→ℝ}(hK:0≤L)(hBp:∀ i:ℕ,0 < K i)(hT:∀ (i:ℕ),i<n → K i=L*K (i+1))(hd:L*a*u^11 ≤ 1/2)
local notation "Y"=> trunks p Pt A K
local notation "T"=> fun k:Fin 4=> nuP k Pt A V u L
local notation "F"=> (Fintype.card (Rings 10):ℝ)
local notation "ν" i:arg=> K i * Mv j i
include hK hBp hT h hd
lemma shinesG : Bowl j Y (fun i=>K i*Mv j i) (fun k=>nuP k Pt A V u L) n (L*a) ((L*F)*(α*u^8)) (L*F*(2*ε)):=by
     refine ⟨fun i hi=>?_,fun i hi=>?_,fun k v hv=>?_⟩
     · exact (trunk_value α a ε u j h hBp i hi).1
     · apply (trunk_sane α a ε L u j h hK hBp hT i hi).trans; refine add_le_add_left (add_le_add ?_ (mul_le_mul_of_nonneg_right hd (trunk_value α a ε u j h hBp (i+1) hi).2)) _; exact mul_le_mul_of_nonneg_left (sum_le_sum (fun k _=>mul_le_of_le_one_left (wageG ..) (pow_le_one₀ h.step.le h.high))) (mul_nonneg hK h.prim)
     refine (trunk_step α a ε L u j h hK hBp hT v hv k).trans_eq ?_ ; split_ifs <;> ring
omit h hd hBp hT
-- λ acquisition require budget step θ ratio & V.B motion. use vP existence & compare by eventually, generic.Analytical afterL no new.Hy. Want smooth Polynomial bounds first demanded table yields.
-- M0 path.M. 
lemma saving (k:Fin 4): (tierQ k).1=8∨ (tierQ k).1=10:=by decide +revert
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.shinesG
