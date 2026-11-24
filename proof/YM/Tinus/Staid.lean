import YM.Tinus.StoneY
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
variable {U Pπ K Z₀ X Y A θ:ℝ}
-- x=input y=out. scales Engineering.V' = v*w_b **spin weighting**. unscaled lift.R=.3 conditions after-L.Brand. Norm op.Tr. 
variable (x y:Label 8)(h:K*u^8=1)
local notation "Yr"=> ((U* K:ℝ):ℂ) • y
local notation "Xr"=> (U:ℂ) • x
local notation "Nr"=> Fintype.card (Rings 8)
include h
local notation "Uy"=> laps 6 Yr+ laps 8 Yr
-- wage takes Tot + old.P.N. compress relative level older. avoid meta loops. Tick imposes.
local notation "Xw"=> laps 6 Xr +laps 8 Xr
local notation "Γ"=> Z₀
local notation "K₁"=> ((4*K)*a)
local notation "K₂"=>2*ε
set_option maxHeartbeats 750000 in
lemma sellsP (hX:0<K)(he:0<U)(hu:0<u)(hu1:u≤1)(ha:0 ≤ a)(hp: 4*a*u ≤ 1/2)(hε:0≤C)(hx:OffS x)(hy:OffS y)(hw:0<w)(hv:0<w')(hQ:w≤ 2*w')(hs: A' ≤ a*(toted u x P w+ u^9*C) + wealth y.val Q.threshold w')(ht: Z₀=U*C/w^2) : U*K*A'/w'^2 ≤ K₁*(Xw)+1/2*Γ+(Uy) :=by
    have heq:= h; have hz := pays_off y hy hv.le (P:=Q); have hz' := toll_off x hx hw.le (u:=u) (P:=P); rw [hz',hz] at hs
    have h₁:w^2 ≤ 4*w'^2:= (pow_le_pow_left₀ hw.le hQ 2).trans_eq (by ring)
    have hk: a*K*u^9 *4 ≤ 1/2:=by rw [pow_succ, ←mul_assoc, mul_assoc a K,heq]; linarith only [hp]
    let A0:=laps 6 x; let A1:=laps 8 x; let A2:=w'^2*laps 6 y+w'^2*laps 8 y; let g:=U*K
    have htP:Z₀*w^2= U*C:=by rw [ht]; field_simp
    have hE:0 ≤Z₀:=by rw [ht]; positivity
    have hχ: u^6*(w^2*laps 6 x)+u^8*(w^2*laps 8 x) ≤ 4*w'^2*(A0+A1):=by
         rw [mul_add]; exact add_le_add ((mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (laps_nn ..)) (pow_le_one₀ hu.le hu1)).trans (mul_le_mul_of_nonneg_right h₁ (laps_nn ..))) ((mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (laps_nn ..)) (pow_le_one₀ hu.le hu1)).trans (mul_le_mul_of_nonneg_right h₁ (laps_nn ..)))
    have hC:0 ≤ U*K:=mul_nonneg he.le hX.le; have hC0:0 ≤ a*K*u^9:=by positivity
    apply (div_le_iff₀ (pow_pos hv 2)).2
    rw [wheelsP x _ he.le, wheelsP x _ he.le,wheelsP y _ hC,wheelsP y _ hC]
    refine (mul_le_mul_of_nonneg_left (le_trans hs (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left hχ _) ha) _)) hC).trans ?_
    have hx : g*(a*(u^9*C)) ≤ 1/2*Γ*w'^2 := calc
             _= (a*K*u^9)*(Z₀*w^2):=by unfold g; rw[htP]; ring
             _≤ (a*K*u^9)*(Z₀*(4*w'^2)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ hE) hC0
             _= (a*K*u^9*4)*(Z₀*w'^2):=by ring
             _ ≤ _:= (mul_le_mul_of_nonneg_right hk (mul_nonneg hE (sq_nonneg _))).trans_eq (by ring)
    change g* (a*(4*w'^2*(A0+A1)+ _)+ A2) ≤ ((4*K)*a*(U*A0+U*A1)+1/2*Γ+(g*laps 6 y+g*laps 8 y))*w'^2; unfold A2; simp only [mul_add, add_mul]; unfold g at *; linarith only [hx]
-- local recurrence H on quantities.S after normalization.Price.Asset.W
variable {J K₀ Yx η R0 Y1:ℝ}
omit h
lemma winds (x y:Label 8)(hu:2 ≤ J)(hq: laps 6 (y-(J:ℂ) • x) ≤ K₀): 2*laps 6 x ≤ laps 6 y+ K₀ :=by
    have ht:= zero_le_one.trans ((show (1:ℝ)≤2 from one_le_two).trans hu); refine (mul_le_mul_of_nonneg_right hu (laps_nn ..)).trans ?_; rw [← wheelsP x _ ht]; have hx:(J:ℂ) • x= y+(-(y-(J:ℂ) • x)):=by abel
    exact (congr_arg _ hx).le.trans ((lap_plus ..).trans (by rw [lap_minus]; exact add_le_add_right hq _))
lemma cashY (x y:Label 8)(J:ℝ)(h: laps 8 (y-(J:ℂ) • x) ≤ K₀) (hp:|J-1|≤ η): laps 8 (y-x) ≤ K₀+η*laps 8 x:=by
     let w:ℂ:=J; let V:= ((J-1:ℝ):ℂ); have hh: y-x=(y-w • x)+ V • x:=by unfold V; push_cast; rw [sub_smul, one_smul]; unfold w; abel
     rw [hh]; exact (lap_plus ..).trans (add_le_add h ((wealthy_tip x (J-1) ..).trans_le (mul_le_mul_of_nonneg_right hp (laps_nn ..))))
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.sellsP
