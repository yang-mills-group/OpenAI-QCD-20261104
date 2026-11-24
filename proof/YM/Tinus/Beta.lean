import YM.Tinus.Shuck
import YM.Parishes.Braid
import YM.Parishes.Stair
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
namespace Stair
variable {w w' a b c₁ d₁ e y₃ ε ε' ε₁:ℝ}{Pt P Q R:BudgetPoint}
local notation "Wd" => fun (i:Jars d)=> u^(weightJ i)*princS x i P w
local notation "Sd"=>toted u x P w
local notation "W₁"=>wealth y.val Q.threshold w'
local notation "Wi"=>wealth x.val P.threshold w
variable {x y}
variable (x y)
-- exactly the quadratic spin lanes of the perturbation.V asset typ d can be any. hi used with d=8. coord powers.
lemma fallsP (i:Jars d)(hx:OffS x)(hz:weightJ i≠6)(he:weightJ i≠8) : princS x i P w=0:=by
     unfold princS wealth; refine Finset.sum_eq_zero (fun j hj=>?_); change ‖chartL P w j (gradeCut d i.val x)‖=0; rw [wpS]; split; next h=>
         rw [worthQ x j hx,show coord _ x.val=0 from ?_,mul_zero,norm_zero]; by_contra h'; rcases hx.route j h' with hp|hp; exact hz (congr_arg Prod.fst (h.symm.trans hp)); exact he (congr_arg Prod.fst (h.symm.trans hp))
     next _=>exact norm_zero
lemma pays_off (hx:OffS x)(hw:0 ≤ w): Wi=w^2*laps 6 x+w^2*laps 8 x:=by
     let f:= fun i:Jars d=> princS x i P w; rw [coinsS]; change (∑ i:Jars d,f i)=_; rw[←fruits x 6 hx hw (P:=P),←fruits x 8 hx hw (P:=P),Finset.sum_filter,Finset.sum_filter, ←sum_add_distrib]; refine sum_congr rfl (fun i _=>?_); split_ifs with h1 h2 h2 <;> first| omega| simp only [add_zero,zero_add]
     all_goals first| exact fallsP x i hx h1 h2| rfl
lemma toll_off (hx:OffS x)(hw:0 ≤ w): Sd = u^6*(w^2*laps 6 x)+u^8*(w^2*laps 8 x):=by
     unfold toted; rw[←fruits x 6 hx hw (P:=P), ←fruits x 8 hx hw (P:=P), Finset.mul_sum,Finset.mul_sum,Finset.sum_filter,Finset.sum_filter, ←sum_add_distrib]; refine sum_congr rfl (fun i _=>?_); by_cases h1:weightJ i=6
     · rw [h1]; norm_num
     by_cases h2:weightJ i=8; · rw [h2]; norm_num
     rw [if_neg h2,if_neg h1,zero_add,fallsP x _ hx h1 h2,mul_zero]
local notation "Up" k:arg=> Finset.univ.filter fun i:Jars d=>weightJ i<k
local notation "Δ6"=> u^6 * (w^2*laps 6 x)
lemma remits (k:ℕ)(hk:k=6 ∨ k=8) (hx:OffS x)(hw:0≤ w): (∑ j∈ (Up k), a*u^weightJ j *princS x j P w)= if k=8 then a* Δ6 else (0:ℝ):=by
     rcases hk with hk|hk; · subst k; rw [if_neg (by decide)]; refine sum_eq_zero fun i hi=>?_ ; have h:weightJ i<6:= (mem_filter.mp hi).2; rw [fallsP x _ hx (by omega) (by omega),mul_zero]
     subst k; rw [if_pos rfl,←fruits x 6 hx hw (P:=P), Finset.mul_sum,Finset.mul_sum,Finset.sum_filter, Finset.sum_filter]; refine sum_congr rfl fun i _=>?_; by_cases h:weightJ i<8
     · rw [if_pos h]; by_cases he:weightJ i=6; · rw[he,if_pos rfl,mul_assoc]
       rw [if_neg he, fallsP x _ hx he (by omega),mul_zero]
     rw [if_neg h,if_neg (by omega:weightJ i ≠ 6)]
lemma laps_nn (k:ℕ):0 ≤ laps k x:=sum_nonneg fun i _=>ite_nonneg (norm_nonneg _) le_rfl
set_option maxHeartbeats 460000 in
lemma sees_weight (k:ℕ)(hk:k=6 ∨ k=8)(hx:TypeBeta u w w' (v*w') a ε ε' P Q x y)(hw:0≤u)(ha:0≤a)(he:0≤ε)(hu:0≤w') (hw0:0≤w) (huX:OffS x)(huY:OffS y): w'^2*ripen k (u^k*v^2) x y ≤ (Fintype.card (Rings d))* ((if k=8 then a* Δ6 else 0)+ε*Wi + ε'):=by
     let T:=u^k*v^2; have hX:(if k=8 then a*Δ6 else 0)+ε*Wi + ε'≥0:=by
          have hp:0≤ ε':=by obtain ⟨f,_,h⟩:=hx.paid; exact (wealth_ge ..).trans h
          exact add_nonneg (add_nonneg (ite_nonneg (mul_nonneg ha (mul_nonneg (pow_nonneg hw _) (mul_nonneg (sq_nonneg _) (laps_nn ..)))) le_rfl) (mul_nonneg he (wealth_ge ..))) hp
     unfold ripen laps; rw [Finset.mul_sum]; refine le_trans (sum_le_sum (s:=Finset.univ) (g:=fun (_:Rings d)=> (if k=8 then a* Δ6 else 0)+ε*Wi+ε') (fun i _=> ?_)) ?_ -- implicit targets
     swap; exact (by rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact le_rfl) -- replace
     split; next h =>
        let f:Label d→ₗ[ℂ]ℂ:=(Stative.coord i.val).comp (labels d).subtype; have h4:= fare_lane x y i hx hw ha he; rw [h,remits x k hk huX hw0,worthQ _ _ huX,worthQ _ _ huY] at h4 -- order
        have hd: (w':ℂ)^2*Stative.coord i.val y.val- (u:ℂ)^k*((↑(v*w'):ℂ)^2*Stative.coord i.val x.val)=(w':ℂ)^2*f (y-(T:ℂ) • x):=by rw [map_sub,map_smul]; change _=_*(f y-(T:ℂ)*f x); unfold T; push_cast; change (w':ℂ)^2*f y-(_)*((_ )*f x)=_; ring
        rw[hd,norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg hu] at h4; exact h4
     next _=>rw[mul_zero]; exact hX
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.sees_weight
