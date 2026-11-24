import YM.Tinus.Beta
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
lemma wheelsP (t:ℝ)(hx:0≤ t)(k:ℕ): laps k ((t:ℂ) • x)= t*laps k x:=by
    unfold laps; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; split
    next h=> let f:Label d→ₗ[ℂ]ℂ:=(Stative.coord i.val).comp (labels d).subtype; change ‖f ((t:ℂ) • x)‖=_; rw[map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg hx]; rfl
    next h=> rw[mul_zero]
lemma lap_plus (k:ℕ) : laps k (x+y) ≤ laps k x + laps k y:=by
     unfold laps; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _=> ?_; by_cases h:weight i.val=k; · let f:Label d→ₗ[ℂ]ℂ:=(coord i.val).comp (labels d).subtype; simp only [if_pos h]; exact (congr_arg norm (map_add f x y)).trans_le (norm_add_le ..)
     simp [h]
lemma lap_minus(k:ℕ) : laps k (-x)=laps k x:=by
     unfold laps; refine sum_congr rfl fun i _=>?_ ; split; next h=> let f:Label d→ₗ[ℂ]ℂ:=(coord i.val).comp (labels d).subtype; exact (congr_arg norm (map_neg f x)).trans (norm_neg _)
     next h=> rfl
lemma wealthy_tip (t:ℝ)(k:ℕ): laps k ((t:ℂ) • x)=|t| * laps k x:=by
     by_cases h:0≤ t; · rw [wheelsP _ _ h,abs_of_nonneg h]
     rw [←lap_minus ((t:ℂ) • x),←neg_smul,← Complex.ofReal_neg,wheelsP _ _ (by linarith),abs_of_neg (lt_of_not_ge h)]
variable {U K Z₀ X Y A θ:ℝ}
-- x=input y=out. scales Engineering.V' = v*w_b **spin weighting**. unscaled lift.R=.3 conditions after-L.Brand. Norm op.Tr. 
variable (x y:Label 8)(h:K*u^8=1)
local notation "Yr"=> ((U* K:ℝ):ℂ) • y
local notation "Xr"=> (U:ℂ) • x
local notation "Nr"=> Fintype.card (Rings 8)
include h
set_option maxHeartbeats 700000 in
lemma realFu (k:ℕ)(hk:k=6∨k=8)(X:ℝ)(hX:K*(u^k*v^2)=X) (hu:0<u)(he:0<U)(hP:TypeBeta u w w' (v*w') a ε (ε*C) P Q x y) (hK: 0<K)(hs:0 ≤ a)(h0:0 ≤ ε)(hw:0<w)(hv:0<w')(hm0:w≤2*w') (hC:wealth x.val P.threshold w ≤ C)(h':Z₀=U*C/w^2)(hUx:OffS x)(hUy:OffS y): laps k ((Yr) - (X:ℂ) • (Xr)) ≤ (Nr:ℝ)*4*K*((if k=8 then a*u^6*laps 6 Xr else 0)+ 2*ε*Z₀):=by
       let D:=w'^2; let Y:=Yr; let z':= Z₀; have hg:= sees_weight x y k hk hP hu.le hs h0 hv.le hw.le hUx hUy
       have hT:0≤C:= (wealth_ge ..).trans hC; have ha:0 ≤ Z₀:=by rw[h']; exact div_nonneg (mul_nonneg he.le hT) (sq_nonneg _)
       have hr: (Y - (X:ℂ) • Xr)= ((U*K:ℝ):ℂ) • (y-((u^k*v^2:ℝ):ℂ) • x):=by unfold Y; rw [←hX, smul_sub,smul_smul,smul_smul]; congr 2; push_cast; ring
       have hw1:w^2 ≤4*w'^2:= (pow_le_pow_left₀ hw.le hm0 _).trans_eq (by ring)
       let J:= if k=8 then a*u^6*laps 6 Xr else 0; have hs' :0 ≤ J:= ite_nonneg (mul_nonneg (mul_nonneg hs (pow_nonneg hu.le _)) (laps_nn ..)) le_rfl
       have hZ : Z₀*w^2=U*C:=by rw[h']; field_simp
       apply le_of_mul_le_mul_left (a:=w'^2) _ (pow_pos hv 2); change w'^2*laps k (Y-(X:ℂ) • Xr) ≤ _; rw [hr,wheelsP _ _ (mul_nonneg he.le hK.le),mul_left_comm]
       refine (mul_le_mul_of_nonneg_left hg (mul_nonneg he.le hK.le)).trans ?_; let p:= if k=8 then a*(u^6*(w^2*laps 6 x)) else 0
       have hg:U*p = w^2*J:=by
          unfold p J; by_cases h:k=8; · rw [if_pos h,if_pos h,wheelsP _ _ he.le]; ring
          rw [if_neg h,if_neg h,mul_zero,mul_zero]
       let W':= wealth x.val P.threshold w; let V:=p+ ε*W'+ε*C; have hh: U*V ≤ w^2*(J+ 2*ε*Z₀):=by
            unfold V; calc
                 _ ≤ U*(p+ε*C+ ε*C):=mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_right (mul_le_mul_of_nonneg_left hC h0) p) (ε*C)) he.le
                 _= U*p+ (2*ε)*(U*C):=by ring
                 _= w^2*(J+2*ε*Z₀):=by rw [hg,←hZ]; ring
       change U*K*((Nr:ℝ)*V) ≤ D*((Nr:ℝ)*4*K*(J+2*ε*Z₀)); rw [show U*K*((Nr:ℝ)*V)= (Nr:ℝ)*K*(U*V) by ring]; refine (mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_right hw1 (add_nonneg hs' (by positivity)))) (by positivity)).trans_eq (by unfold D; ring)
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.realFu
