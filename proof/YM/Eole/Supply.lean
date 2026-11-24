import YM.Eole.Gates
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
-- Energy summability & equality
local notation "U₀"=> ν
local notation "Θ"=> night (oldZ R) (sensor q o F W R t) U.threshold
local notation "ζ"=> U.threshold
local notation "μT"=> scaler m W
local notation "τ"=> taxed (swatch (hatsF o F)) (heightE U.order (H!)) V0
variable (AZ:Bloc I J)(p:J→Site c)(hG:Setting AZ (ycard o F R) (hatsF o F) q o p (oldZ R) (hood o F R k) (sensor q o F W R t) (spareK o F R K1 K2 r) U t)
include hG hT
lemma supplies (U':Grid c) : Summable (fun i:E⊕ Hearts o F=> ‖night (oldZ R) (sensor q o F W R t) U.threshold U' i‖):=by
      have hh':1≤ V0:=Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le); have hY:= gates_k q o F R K1 K2 hh ha k hr hZ hη hx hK hKp hp hκ hμ -- binder order W omitted
      have hn :=positiveZ AZ (Δ) (Y) q o p (oldZ R) _ _ _ hG (zero_lt_one.trans_le hT)
      have h_nn(i):0 ≤ τ i:=mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (mul_nonneg (pow_nonneg (by norm_num:(0:ℝ)≤ 2) _) (hn _))
      have he : Summable (τ):=by
           let v:=τ; let a x' i:= if x'∈ Ω i then v i * Real.exp ((28/256:ℝ)*coverNumber U.B (Ω i)) else 0; have h1 :Summable (fun i=>(∑ x':Site c,a x' i)):= summable_sum fun j _=> (hY j).2.1
           refine h1.of_nonneg_of_le h_nn fun j=> ?_; have hp:(Ω j).Nonempty:=by rcases j with j|j; exact (show (oldZ R j).Nonempty from ⟨_,(R.addr _).anchor⟩).mono (hG.grows j); exact ((Y j).alive.mono (Y j).part).mono (hG.gram j)
           obtain ⟨i,hi⟩:=hp; exact le_trans (show v j ≤a i j from by unfold a; rw [if_pos hi]; exact le_mul_of_one_le_right (h_nn _) (Real.one_le_exp (by positivity))) (single_le_sum (fun i _=>(hY i).1 j) (mem_univ i)) -- annotation
      refine he.of_nonneg_of_le (fun _=>norm_nonneg _) fun i=>?_ ; let X':= Θ U' i; have hP:=wages AZ (Δ) Y q o p (oldZ R) _ _ _ hG (zero_lt_one.trans_le hT) i U' -- use
      let s:= (H!) i; have hp0: ‖X'‖ ≤ Stitch.Tablet.credits t X':= Iris.loaded X'.val (Stitch.Tablet.chip t (Keys c 6) (Spine I)) (fun j=> by rcases j with j|j; exact hT; exact le_rfl)
      exact (hp0.trans hP).trans (le_trans (le_mul_of_one_le_left ((norm_nonneg _).trans (hp0.trans hP)) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))) (le_mul_of_one_le_left (show 0 ≤ (2:ℝ)^U.order * (H!) i from mul_nonneg (pow_nonneg (by norm_num) _) (hn _)) (one_le_pow₀ hh'))) -- edit names
lemma drama (x:Grid c)(F0:EvenA c 6): scaler (Keys c 6) W (NormedSpace.exp (rootR (Spine I) _ F0+Reel.rope R U.threshold x)*withdraw 6 o t (heartK F U.threshold x))=
   NormedSpace.exp (rootR (Spine I) m F0+∑' i,night (oldZ R) (sensor q o F W R t) U.threshold x (.inl i))* (∑' i,gift (night (oldZ R) (sensor q o F W R t) U.threshold x ∘ Sum.inr) Y (flags U.threshold x) i):=by
    let Z':= Θ x; have hy:=supplies q o F W R K1 K2 hh ha k hr hT hZ hη hx hK hKp hp hκ hμ AZ p hG x
    have hm:Summable (fun i:M=> ‖Z' (.inr i)‖):=hy.comp_injective Sum.inr_injective
    let z i:= Reel.mist R U.threshold i x; let C:= scaler (Keys c 6) W; have h0:C (rootR (Spine I) _ F0)=rootR _ _ F0:=Subtype.ext (Cupola.tarfib _ _ _)
    have h1:C (Reel.rope R U.threshold x)= ∑' i,Z' (.inl i):=by
         obtain ⟨f',hf,h⟩:=hh.reserve; simp only [abs_one,prod_const_one,one_mul] at hf; unfold Reel.rope; calc
         _=∑' i,C (z i):= C.toLinearMap.toContinuousLinearMap.map_tsum (creditE o q R f' hh.booked h hf (by norm_num) hT x)
         _ = ∑' i,Z' (.inl i):=by
                 refine tsum_congr fun i=>?_; change C (masked _ _ _ x)=masked _ _ _ x; by_cases hV:Healthy U.threshold (R.addr i).support x; · rw[masked_eq _ _ _ _ hV]; have h':= stamen m q W (R.z i) _ (hh.booked.stage i x|>.1); exact h'.trans (masked_eq _ _ (piece W R i) x hV).symm
                 rw [masked_ne _ _ _ _ hV,map_zero]; exact (masked_ne _ _ (piece W R i) x hV).symm
    rw[map_mul, NormedSpace.map_exp (μT) (μT).toLinearMap.toContinuousLinearMap.continuous, map_add]; refine congr_arg₂ (·*·) ?_ ?_
    · exact congr_arg NormedSpace.exp (congr_arg₂ (·+·) h0 h1)
    exact exact_bill q o F W ha hT (by norm_num) (Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)) x hm
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.drama
