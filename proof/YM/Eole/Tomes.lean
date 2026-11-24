import YM.Eole.Stars
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
local notation "G"=> Grid c
local notation "P"=>Patio (m⊕Spine I)
variable {t u v x b w γ:ℝ}{U:BudgetPoint}
variable (q:I→Bool) (o:I→Site c)(F: Rail c (ample 6 I) K) (W:I→ℝ)
-- expand basis support over all physically allowed markers using F location.G
local notation "M"=> Hearts o F
set_option quotPrecheck false
local notation "V"=> withdraw 6 o t
local notation "X"=>sparkF q o F
local notation "Y"=>hatsF o F
local notation "A"=>mark o F
variable (B₀ k D₀:ℕ)(Kf:K→ℝ)
open Push.AbsoluteSums -- edit
open ConnectedActivityE6 Reserves Blaze
local notation "A'"=> (k+k+1)^4
abbrev share (x:ℝ)(B:ℕ)(k:ℕ)(t:ℝ):ℝ:= x * Real.exp (t*( (k+k+1)^4:ℕ))
local notation "Φ"=> share x B₀ k v
local notation "S"=> fun i:K=> (F.addr i).place
noncomputable abbrev abode (k:ℕ)(j:M): Support c:= armsZ o k (hatsF o F j).place (mark o F j)
noncomputable def tallK (x:ℝ)(j:M):= x^(mark o F j).card*Kf j.fst
variable {α δ ε:ℝ}
variable (hv:Fires o D₀)(hB:0<B₀)(hp:0 ≤ v)(hz:0<x) (hf:∀ i,0 ≤ Kf i)
variable (he:Ac.Hit (fun i:K=>(F.addr i).place) B₀ Kf (v+ε) α)
include hB -- edit
include hv hp hz hf he
lemma lumber (hh:Basal.hullP B₀ D₀ * (share x B₀ k v)≤ ε) : Ac.Hit (abode o F k) B₀ (tallK o F Kf x) v ((↑((k+k+1)^4:ℕ):ℝ)* α):=by
     let z:=(k+k+1)^4; let R:=Φ; have hR:0 ≤R:=mul_nonneg hz.le (Real.exp_pos _).le; intro i; let T:=halo k {i}; have hT: (T.card:ℝ) ≤ (z:ℝ):=by exact_mod_cast (Corona.halo_size {i} k).trans (by norm_num[z]); -- let syntax
     let H j:K→ℝ:=fun k=>if j∈ (F.addr k).place then Kf k * Real.exp ((v+ε)*coverNumber B₀ ((F.addr k).place)) else 0; have hw j :SumBudget (H j) α:=he j
     have hD :SumBudget (fun j=>∑ i∈T,H i j) ((z:ℝ)*α):=budget_loosen (budget_over T H (fun _=>α) (fun i _=>hw i)) (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hT (budget_nonneg (he i)))
     let P' j:= if i∈abode o F k j then tallK o F Kf x j * Real.exp (v*coverNumber B₀ (abode o F k j)) else 0; have hz'(j):0 ≤P' j:=ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hz.le _) (hf _)) (Real.exp_pos _).le) le_rfl
     refine budget_fiberwise (f:=P') (fun i:M=> i.fst) hz' ?_ hD; intro j s hs
     let L:=birth o F j; let W:= Sigma.mk j (β:=fun i=> ↥(birth o F i)); let U' := (F.addr j).place
     have hK:s⊆ Finset.univ.image W:=by rintro ⟨t,y⟩ h; have ht:t=j:=hs _ h; subst j; exact mem_image_of_mem _ (mem_univ _)
     have hP (k:↥L): k.val ⊆ barn o U':= mem_powerset.mp k.2
     apply le_trans (sum_le_sum_of_subset_of_nonneg hK fun i _ _=>hz' i); rw[sum_image (show Set.InjOn W _ from fun i _ j _ h=>(Sigma.mk.inj_iff.mp h).2|>eq_of_heq)]; by_cases hx:i∈halo k U'; swap; · rw[sum_eq_zero (by intro z hb; exact if_neg fun hl=>hx (set_gain o _ _ _ (hP _) hl))]; exact hD.1 _
     obtain ⟨t,ht,hw'⟩:=halo_spec.mp hx; have hx' :t∈T:=halo_spec.mpr ⟨i,mem_singleton_self _,(separation_comm i t).le.trans hw'⟩; refine le_trans ?_ (single_le_sum (fun j' _=> (hw j').1 j) hx')
     let Y':=(coverNumber B₀ U':ℝ); let f:= Kf j * Real.exp (v*Y'); have hy:0≤Y':=Nat.cast_nonneg _; have hF:0≤ f:=mul_nonneg (hf _) (Real.exp_pos _).le
     refine (sum_le_sum (s:=univ) (show ∀ d:↥L, d∈univ→ P' (W d) ≤ f * R^d.val.card from ?_)).trans ?_
     · intro d _; unfold P'; split; next h=>
          let i:=d.val.card; have he:(coverNumber B₀ (abode o F k (W d)):ℝ)≤ ((coverNumber B₀ U'+i*((k+k+1)^4):ℕ):ℝ):=(Nat.cast_le.mpr (size_gain o U' k d.val (hP d) B₀ hB)); exact (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left he hp)) (mul_nonneg (pow_nonneg hz.le i) (hf j))).trans_eq (by rw [Nat.cast_add,Nat.cast_mul,mul_add,Real.exp_add, show R=x*Real.exp (v*(z:ℝ)) from rfl,mul_pow,← Real.exp_nat_mul]; change x^i * Kf j*(Real.exp _*Real.exp _) = _; unfold f Y' z i; ring_nf) -- exponent associativity ring_nf pushes Real arg
       exact mul_nonneg hF (pow_nonneg hR _)
     rw[←mul_sum, sum_coe_sort L (fun j=> R^j.card)]; let A1:=barn o U'; have hX :(A1.card:ℝ) ≤ Y' * Basal.hullP B₀ D₀:=by unfold Basal.hullP Y'; rw [← mul_assoc]; exact_mod_cast (barncard o U' D₀ B₀ hv)
     have hw_x: Real.exp ((A1.card:ℝ)*R) ≤ Real.exp (ε*Y'):=Real.exp_monotone ((mul_le_mul_of_nonneg_right hX hR).trans (by rw [mul_assoc,mul_comm ε]; exact mul_le_mul_of_nonneg_left hh hy))
     have hrr: (∑ j∈A1.powerset,R^j.card)=(1+R)^A1.card:=by rw [add_comm (1:ℝ),←prod_const,Finset.prod_add]; simp -- edit formula
     unfold H; rw[if_pos ht]; rw [show (∑ y∈L,R^y.card)=_ from hrr]; apply le_trans (mul_le_mul_of_nonneg_left (le_trans ?_ hw_x) hF); rw [show (v+ε)*_= v*Y'+ε*Y' from add_mul ..,Real.exp_add,mul_assoc] 
     rw [Real.exp_nat_mul]; apply pow_le_pow_left₀ (add_nonneg zero_le_one hR); exact le_trans (le_of_eq (add_comm ..)) (Real.add_one_le_exp _)
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.lumber
