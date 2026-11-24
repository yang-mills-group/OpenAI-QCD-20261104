import YM.Eole.MainK
import YM.Eole.Tomes
import YM.Eole.Buds
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.GasP
local notation "m"=> Keys c 6
local notation "P"=>Patio (m⊕Spine I)
variable {t u v x b w γ:ℝ}{U:BudgetPoint}
variable (q:I→Bool) (o:I→Site c)(F: Rail c (ample 6 I) K) (W:I→ℝ)
-- expand basis support over all physically allowed markers using F location.G
local notation "M"=> Hearts o F
set_option quotPrecheck false
local notation "V"=> withdraw 6 o t
local notation "X"=>sparkF q o F
variable (R:Reel c 6 I E)
-- root support tags proof.Y signs.
variable (Z:Bloc I J)
local notation "A"=>mark o F
local notation "Δ"=> ycard o F R
local notation "Y"=> hatsF o F
local notation "S"=>sensor q o F W R
local notation "L"=>Rootπ Z (Δ)
open QCD.Jets QCD.Jets.Touch
open Push.AbsoluteSums.Trees
variable {LL:Side}{η s ζ μ θ C r:ℝ}{D:ℕ}
local notation "μ0" => (1/8:ℝ)
local notation "μ2"=>(42/256:ℝ)
local notation "μE"=>(29/256:ℝ)
local notation "αk"=>(26/256:ℝ)
local notation "ε"=>(1/256:ℝ)
local notation "V1"=> taxK LL s 2
local notation "V0"=> taxK LL s (39/20)
local notation "VP"=> taxK LL s (1/20)
variable (K1:E→ℝ)(K2:K→ℝ)(hh: R.Occupant o q t U 2 (29/256) μ (fun _=>1))(ha: Wage.Tip 6 o q F U t (42/256) (taxK LL s 2))
local notation "H!"=>spareK o F R K1 K2 r
local notation "Fh"=> (2:ℝ)^U.order
local notation "NZ"=> E⊕Hearts o F
variable (k:ℕ)
local notation "Ω"=> hood o F R k
variable (hr:0<r)(hT:1≤t)(hZ:Ac.Hit (oldZ R) U.B K1 (29/256) μ)(hη: ∀ i,0 ≤ K1 i)(hx:Fires o D)(hK:Ac.Hit (Ruby.home F) U.B (taxed (oriD F) K2 (taxK LL s 2)) (42/256) 1)(hKp:∀ i,0 ≤ K2 i)
local notation "κ"=> share r U.B k (28/256)
local notation "A'"=> ((k+k+1:ℕ)^4:ℕ)
variable (hp:Basal.hullP U.B D*(share r U.B k (28/256)) ≤ (14/256:ℝ))(hκ: share r U.B k (28/256) ≤1)
variable (hμ: (((↑((k+k+1:ℕ)^4:ℕ):ℝ)*(share r U.B k (28/256)*μ) + (↑((k+k+1:ℕ)^4:ℕ):ℝ)*(taxK LL s (1/20))⁻¹)*((2:ℝ)^U.order)) ≤ C)
include hκ hr hp hμ hh ha hZ hη hx hK hKp
lemma gates_k : Ac.Hit (hood o F R k) U.B (QCD.GasP.taxed (swatch (hatsF o F)) (heightE U.order (spareK o F R K1 K2 r)) (taxK LL s (39/20))) (28/256) C :=by
    let c0:=(28/256:ℝ); let S1:= heightE U.order H!; let v:= taxed (swatch (hatsF o F)) (H!) V0
    have hE: Ac.Hit ((Ω) ∘ Sum.inl) U.B (v ∘ Sum.inl) (28/256) (↑((k+k+1:ℕ)^4:ℕ)*(κ*μ)):=by
       have ht : v ∘ Sum.inl = tiltE R.z K1 r:=funext fun i=> by unfold Function.comp v taxed; rw [show swatch Y (.inl i)=∅ from rfl,card_empty,pow_zero,one_mul]; rfl
       rw[ht]; exact drafted o k _ (oldZ R) K1 hh.booked.stays (fun i j he=>(inside ..).2 (hh.booked.stamp i (mem_image_of_mem _ he))) hr.le U.B U.B_pos (by norm_num) (QCD.Shells.Warmlet.fresh _ _ hZ (by norm_num) hη) hη hκ
    let g:=taxed (oriD F) K2 V0; have hhV:1 ≤ VP:= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le); have hhV':0< VP:=zero_lt_one.trans_le hhV; have hv':0 < V0:=Real.exp_pos _; have hg(i):0 ≤ g i:=mul_nonneg (pow_nonneg hv'.le _) (hKp i)
    have hK0: Ac.Hit (Ruby.home F) U.B g (28/256 +14/256) (VP)⁻¹:=by
       intro i; rw [show (28/256+14/256:ℝ)= 42/256 from by norm_num, ←mul_one ((VP)⁻¹)]; refine budget_mono (budget_scale (inv_pos.mpr hhV').le (hK i)) (fun i=>ite_nonneg (mul_nonneg (hg _) (Real.exp_pos _).le) le_rfl) fun j=>?_
       split; next h=>
           rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; unfold g taxed; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (hKp _)
           let A1:= (oriD F j).card; have hψ : VP * V0 = V1:=by unfold taxK; rw [← Real.exp_add]; congr 1; ring
           rw[←hψ,mul_pow,← mul_assoc]; apply le_mul_of_one_le_left (pow_nonneg hv'.le _); rw[inv_mul_eq_div, one_le_div hhV']; exact (le_of_eq (pow_one VP).symm).trans (pow_le_pow_right₀ hhV (card_pos.mpr (F.addr j).alive))
       rw [mul_zero]
    have hk: Ac.Hit ((Ω) ∘ Sum.inr) U.B (v ∘ Sum.inr) (28/256) (↑((k+k+1:ℕ)^4:ℕ)*(VP)⁻¹):=by
        let G':= tallK o F g r; have hv: v ∘ Sum.inr=G':= funext fun i=>by change V0^_ *(r^_*K2 i.fst)=r^_*(V0^_*K2 i.fst); rw [mul_left_comm]; rfl
        rw[hv]; exact lumber o F U.B k D g hx U.B_pos (by norm_num) hr hg hK0 hp
    intro i; let f'(t:E⊕Hearts o F):= if i∈Ω t then v t*Real.exp (c0*coverNumber U.B (Ω t)) else 0; have hf:SumBudget f' (((A':ℕ):ℝ)*(κ*μ)+ ((A':ℕ):ℝ)*(VP)⁻¹):= Extra.Iteration.Cost.sum (hE i) (hk i)
    refine budget_loosen ?_ (le_trans (le_of_eq (mul_comm ((2:ℝ)^U.order) _)) hμ); convert budget_scale (pow_nonneg (by norm_num:(0:ℝ)≤2) U.order) hf using 1; funext j; unfold f'; split; next h=> unfold v taxed heightE; rw[mul_left_comm (V0^_),mul_assoc]; -- simplify?
    next _=>rw [mul_zero]
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.gates_k
