import YM.VMarker.Limbs
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
namespace Wage
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
open QCD.Leaf QCD.Jets
variable {V J₁ K₀:Type} (G:Patron.Gem c (ample N I) E)(Ω:E→Finset I)(A':Set (Finset I))(Q: Patron.Rail c (ample N I) J₁)(K₁ : Patron.Rail c N K₀)
local notation "F'"=> Reel.render N p φ r G Ω A'
local notation "Σ'"=> Film.publication N p q Q A' θ
local notation "Λ'"=> turn I (D:=K) r
open QCD.Jets.Touch
variable (A₀ R': Grid c→ EvenA c N) (Tt : Finset I)(χ:Grid c)
local notation "w'"=> withdraw N p φ
local notation "u'"=> withdraw N p θ
local notation "O'"=> rootR R K
local notation "Ω0"=>vacR R K
local notation "op" => shutter K Tt
variable (hE:∀ i V,Mint N p φ q (Ω i) (G.view i V))(hG:G.Gather)(hH: Summable (letters G O.threshold χ))(hV:(Tt.powerset:Set (Finset I))⊆ A')(hp:Tip N p q Q O θ v w)(hC: Correspond (faultK N p θ Q) K₁)(hv:1 ≤ w)(hz:0 ≤ v)(hθ: 1 ≤ θ)(hφ:0<φ)
include hE hG hH hV hp hC hv hz hθ hφ
lemma clause (C:ℂ)(M':EvenA c N)(hx: u' (heartK Q O.threshold χ) = Λ' (w' (heartK F O.threshold χ))*O' M')(hm:wearK c N r (NormedSpace.exp (A₀ χ+ Ω0 (w' (Patron.total G O.threshold χ)))) = C • (exp (R' χ)*M')) : op (turn I r (outset N p φ G F A₀ χ (P:=O)))= C • op (relativeE N F' Σ' K₁ R' O.threshold χ):=by
     let V:= Patron.total G O.threshold χ; let H:= Reel.rope F' O.threshold χ
     have he:= Reel.presenceD N p q φ r G Ω A' hE hφ hG χ Tt hH hV
     let So:= A₀ χ+ Ω0 (w' V); let q':=wearK c N r
     have hEq : op (Λ' (O' (A₀ χ)+w' V))=op (O' (q' So)+H):=by
          unfold q' So; rw [map_add (wearK c N r), ← freeTurn,map_add (O'),map_add (Λ'),rollRoot,add_assoc,map_add op,map_add op,map_add op]; rw [map_add op] at he; exact congr_arg _ he
     have hθ':=zero_lt_one.trans_le hθ; let S':= Σ'; have hk:= Film.mergeFront N p q θ K₁ Q A' Tt hV hp.fits hθ' hp.tilt.uses hC χ (prints _ _ hp.tilt.uses hp.tilt.sold hv hz hθ)
     let T:= Reel.rope F' O.threshold χ; let Qx:= heartK F O.threshold χ
     unfold relativeE outset; rw [map_mul op,map_mul (Λ'),map_mul op,map_exp (Λ') (Λ').toLinearMap.toContinuousLinearMap.continuous,map_exp op (op).toLinearMap.toContinuousLinearMap.continuous,hEq,hk,Film.testifyK,hx]; -- check order map_mul rhs
     rw [← map_exp (op) (op).toLinearMap.toContinuousLinearMap.continuous]; -- turn pulls
     rw [exp_add, ←map_exp (O') (O').toLinearMap.toContinuousLinearMap.continuous, ←map_exp q' q'.toLinearMap.toContinuousLinearMap.continuous,show q' (exp So)=_ from hm]; simp only [map_smul,map_mul O',map_mul op,exp_add,←map_exp O' (O').toLinearMap.continuous_of_finiteDimensional,← map_exp O' (O').toLinearMap.toContinuousLinearMap.continuous,Algebra.smul_mul_assoc]
     change C • _= C • (op (O' (exp (R' χ)))*op (exp H)*(op (Λ' (w' Qx))*op (O' M'))); apply congr_arg; ring
end Wage
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Wage.clause
