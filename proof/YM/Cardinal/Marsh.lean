import YM.Cardinal.Bequest
/-!
 # Single arrangements in actual Units. Caps pre weights on pointed/reference layouts.P composed with updates.Yes.
   No explicit global identity in this run of the one-source cone. (All labels including that one use actual indicators; net also pays that weight). 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
-- Step references. No common label-union across books demanded. `w x partial` eq at outgoing health.Loosen.a' . Seat.S. set covering.
variable (x:Label d) (q:Bool) (Pt:BudgetPoint)
-- General base rank+remainder.R Over variant.Mert.Lo.Q.S.Defs.K
section
variable {Pt A H x q b} (G:CentreFrame (c:=c) Pt v x q A b (r+1) E K)
set_option quotPrecheck false
local notation "o"=> wrap c b
local notation "bp"=> pot (r+1) c b
local notation "Z!"=>basePack A b q d x G.moor (r+1)
local notation "W'"=> seed_w (a*coverNumber Pt.B (pot (r+1) c b))*β*wealth x.val Pt.threshold v
variable (V:Grid c)
abbrev tapeA (c:Side):= Patio (Keys c 6⊕ Spine Unit)
noncomputable def vote (A:Exhibit U)(b:Cover)(x:Label d)(q:Bool)(hp:moored x.val q) (t:ℝ)(r:ℕ)(c:Side)(V:Grid c): tapeA c:= masked t (pot r c b) (radiant 6 q (graphs (c:=c) d A b x) (graphing _ _ _ _ q hp)) V
local notation "Tq"=> goldM q
local notation "p!"=>fun (_:alpha)=>wrap c b
local notation "r!"=>fun (_:alpha)=>q
noncomputable def rayon (A:Exhibit U)(b:Cover)(x:Label d) (q:Bool)(hp:moored x.val q) (h:ℝ)(r:ℕ)(c:Side): Grid c→Lat.Fields c 6:=masked h (pot r c b) (graphs (c:=c) d A b x)
lemma sumBase (h:moored x.val q) (V:Grid c): Reel.rope ((basePack A b q d x h r).roll) t V=vote A b x q h t r c V:=by
    unfold vote Reel.rope; rw [tsum_fintype]; let S:= pot r c b; let Z: Puff c 6 (Jars d) q:= basePack A b q d x h r
    by_cases he:Healthy t S V; · rw [masked_eq _ _ _ _ he]; rw [show (∑ j, Reel.mist (Puff.roll 6 (basePack A b q d x h r)) t j V) = ∑ j:Jars d,Z.roll.mark j V from Finset.sum_congr (g:=fun j=>Z.roll.mark j V) rfl (fun j _=> masked_eq t (pot r c b) (Z.roll.mark j) _ he)] -- [Reel.mist,fun j=>masked_eq _ _ _ V (show Healthy _ (Z.roll.addr j).support _ from he)] -- rewrite defeq
                                 apply Subtype.ext; change Cove.light (Keys c 6⊕Spine Unit) (∑ j:Jars d,Z.roll.mark j V)=Cove.light (Keys c 6⊕Spine Unit) (radiant 6 q (graphs d A b x) (graphing _ _ _ _ q h) V); rw [map_sum]; let p:= LinearMap.toContinuousLinearMap ((coord (0,∅) : Pol d→ₗ[ℂ]ℂ).comp (labels d).subtype) -- dummy
                                 let f :Label d →ₗ[ℂ] Alg (Keys c 6):=(ContinuousMap.evalCLM ℂ V).toLinearMap.comp ((Realize.placed (A.t d) c b).comp (A.lead d)); change ∑ i:Jars d,stake (Keys c 6) (goldM q) (f _) = stake _ _ (f x); rw [← map_sum,← map_sum,sumCut] -- check map_comp types
    rw [masked_ne _ _ _ _ he]; exact sum_eq_zero fun i _=> masked_ne _ _ _ _ (show ¬Healthy _ (Z.roll.addr i).support _ from he)
lemma vote_add {x y:Label d} (hx:moored x.val q)(hy:moored y.val q)(hb:moored (x+y:Label d).val q) : vote A b (x+y) q hb t r c V=vote A b x q hx t r c V+ vote A b y q hy t r c V:=by
    unfold vote; by_cases hp: Healthy t (pot r c b) V
    · repeat rw [masked_eq _ _ _ _ hp]
      apply Subtype.ext; let f :Label d →ₗ[ℂ] Alg (Keys c 6):=(ContinuousMap.evalCLM ℂ V).toLinearMap.comp ((Realize.placed (A.t d) c b).comp (A.lead d)); change stake _ _ (f (x+y))=stake _ _ (f x)+ stake _ _ (f y); rw [map_add,map_add]
    repeat rw [masked_ne _ _ _ _ hp]
    rw [add_zero]
lemma vote_smul (s:ℂ)(hx:moored x.val q)(hy:moored (s • x).val q) : vote A b (s • x) q hy t r c V=s • vote A b x q hx t r c V:=by
    unfold vote; by_cases hp:Healthy t (pot r c b) V; · repeat rw [masked_eq _ _ _ _ hp]; 
                                                        apply Subtype.ext; let f :Label d →ₗ[ℂ] Alg (Keys c 6):=(ContinuousMap.evalCLM ℂ V).toLinearMap.comp ((Realize.placed (A.t d) c b).comp (A.lead d)); change stake _ _ (f (s • x))=s • stake _ _ (f x); rw [map_smul,map_smul]
    rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,smul_zero]
-- single relative notation
noncomputable def reading (F: Patron.Rail c 6 Zt)(Y:Grid c→ EvenA c 6)(V:Grid c):= pluck (Keys c 6) (goldM q) (relativeE 6 (Puff.roll 6 (ritual G)) G.spine F Y Pt.threshold V)
variable (hy:Published G H n j a s A' D)(ht:1 ≤ s)(hv:1 ≤ v)(ha:0≤a)(F:Patron.Rail c 6 Zt) (R:Grid c→ EvenA c 6)
local notation "C⁰"=>rootR (Spine alpha) (Keys c 6)
include ht hv ha hy
-- Only need baseP to show Book tint support. Can also use direct rank.Cost. 
variable (hP:Pilot H A d m k n j r α β)(hp:Pt.order=m)(hk: Pt.power=k)(hh:30*(r+1)≤c.val)(hF:∀ U,Summable fun i=>‖F.warp i U‖)
include hF hP hp hk hh
lemma read_earn : reading G F R V= pluck (Keys c 6) Tq ((rootR (Spine Unit) (Keys c 6) (NormedSpace.exp (R V)))*(Wcall 6 F G.spine V (t:=Pt.threshold)+(vote A b x q G.moor Pt.threshold (r+1) c V + Reel.rope G.p.roll Pt.threshold V)*rootR (Spine Unit) (Keys c 6) (heartK F Pt.threshold V))):=by
    have hm:= markedMatter 6 o F G.spine V R (roll 6 (ritual G)) (Puff.declare 6 o (ritual G) (rendition hP hp hk hv hh G hy).1) hy.lev (absentD 6 o G.spine V hy.taxed hy.lev ht hv ha) (hF V) -- syntax
    obtain ⟨z,hz,hL⟩:= hy.costs; have he:Summable fun j=>Reel.mist G.p.roll Pt.threshold j V:= grow_shape 6 o _ V ⟨_,fun i=>(hz i).sight,hL⟩ ha hv hy.sailX
    have hx:= sumBase G.moor (A:=A) (b:=b) (t:=Pt.threshold) (r:=r+1) V
    rw [reading,hm.1, ritual_eq, rope_plus 6 V _ _ he Summable.of_finite,hx] -- order
end
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.read_earn
