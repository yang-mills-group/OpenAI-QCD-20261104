import YM.Cardinal.Marsh
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
local notation "Tq"=> goldM q
local notation "p!"=>fun (_:alpha)=>wrap c b
local notation "r!"=>fun (_:alpha)=>q
variable {y:Label d} (W:CentreFrame (c:=c) Pt v y q A b (r+1) Uv Fv)
variable (hG:Published G H n j a s A' D)(α₁ α₂:ℝ)(hW:Published W H n j a s α₁ α₂)
noncomputable def sumup : CentreFrame (c:=c) Pt v (x+y) q A b (r+1) (E⊕Uv) (K⊕Fv):=
  { moor := by change parityAct (x.val+y.val)=gammaQ q • (x.val+y.val); rw [map_add,G.moor,W.moor,smul_add]
    p:=⟨Sum.elim G.p.addr W.p.addr,Sum.elim G.p.fill W.p.fill,fun i=>by rcases i with i|i; exact G.p.beams i; exact W.p.beams i⟩
    spine:= addFilm 6 G.spine W.spine }
include hG hW
lemma sumupP : Published (sumup G W) H n j a s (A'+α₁) (D+α₂):=by
   obtain ⟨g,hg,hG'⟩:=hG.costs; obtain ⟨w,hw,hW'⟩:=hW.costs; refine ⟨?_,⟨Sum.elim g w,fun i=>?_, fun i=> Extra.Iteration.Cost.sum (hG' i) (hW' i)⟩,beat_plus 6 (fun _=>wrap c b) (fun _=>q) _ _ hW.lev hG.lev,sink_add 6 _ _ hG.taxed hW.taxed,?_⟩
   · constructor
     · rintro (i|i); exact hG.sailX.anchor i; exact hW.sailX.anchor i
     · rintro (i|i); exact hG.sailX.stays i; exact hW.sailX.stays i
     · rintro (i|i); exact hG.sailX.label i; exact hW.sailX.label i
     · rintro (i|i); exact hG.sailX.shade i; exact hW.sailX.shade i
     rintro (i|i); exact hG.sailX.sees i; exact hW.sailX.sees i
   · rcases i with i|i; exact hg i; exact hw i
   rintro (i|i); exact hG.key _; exact hW.key _
omit hG hW
private lemma addr_t {U I:Type}[Fintype I](X Y: Reel c 6 I U)(h:X.addr=Y.addr)(he:X.z=Y.z)(hv:X.mark=Y.mark):X=Y:=by cases X; cases Y; congr
lemma sumupp : Puff.roll 6 (sumup G W).p=addReel 6 G.p.roll W.p.roll:=
   addr_t _ _ rfl (funext (fun i=>by rcases i with i|i<;> rfl)) (funext (fun i=>by rcases i with i|i <;> rfl))
noncomputable def byG (u:ℂ): CentreFrame (c:=c) Pt v (u • x) q A b (r+1) E K where
    moor:=by change parityAct (u • x.val)=gammaQ q • (u • x.val); rw [map_smul,G.moor,smul_comm]
    p:= ⟨G.p.addr,fun i=>u • G.p.fill i,fun i V=>Grass.Hom.smul (G.p.beams i V) _⟩
    spine:= feeK 6 G.spine u
lemma byGn (u:ℂ): Puff.roll 6 (byG G u).p=feeR 6 (roll 6 G.p) u:=by
   refine addr_t _ _ rfl rfl (funext fun i=>funext fun V=>?_)
   exact Subtype.ext (map_smul (stake (Keys c 6) Tq) ..)
include hG
lemma byGP (u:ℂ) : Published (byG G u) H n j a s (‖u‖*A') (‖u‖*D):=by
    obtain ⟨g,hg,hG'⟩:=hG.costs; let P:=Puff.roll 6 (byG G u).p; have hv(i):=flare_by _ _ _ (hg i) u
    refine ⟨⟨hG.sailX.anchor,fun i=>(hv i).sight.room,fun i=>(hv i).sight.borel,fun i x k=> ?_,fun i=> (hv i).sight.gate⟩, ⟨_,fun i=> hv i,?_⟩,beat_by 6 o G.spine hG.lev u,sink_by 6 _ hG.taxed _,fun i=> (show u • (0:Pol d)=0 from smul_zero u) ▸ (acting H b d (G.p.fill i) 0 (hG.key i) u)⟩
    · change Lat.slots 6 _ (u • _) = u • (G.p.fill i x); rw [map_smul,hG.sailX.shade]
    intro i; convert! budget_scale (norm_nonneg u) (hG' i) using 1; funext j; split
    next h=> rw [if_pos (show i∈(G.p.addr j).support from h)]; exact mul_assoc ..
    next h=> rw [if_neg (show i∉(G.p.addr j).support from h),mul_zero]
variable (F: Patron.Rail c 6 Zt)(D':Grid c→EvenA c 6)
variable (hP:Pilot H A d m k n j r α β)(hp:Pt.order=m)(hk: Pt.power=k)(hh:30*(r+1)≤c.val)(hF:∀ U,Summable fun i=>‖F.warp i U‖)(hv:1 ≤ v)(hs:1 ≤ s)(ht:0 ≤ a)
include hP hp hk hh hF hv hs ht
lemma applying (u:ℂ): reading (byG G u) F D' V=u • reading G F D' V:=by
   rw [read_earn (byG G u) V (byGP G hG u) hs hv ht F D' hP hp hk hh hF, read_earn G V hG hs hv ht F D' hP hp hk hh hF,byGn]
   obtain ⟨g,hg,hz⟩:=hG.costs; have hV:=grow_shape 6 o _ V ⟨_,fun i=>(hg i).sight,hz⟩ ht hv hG.sailX
   rw [rope_by _ V _ _ hV, vote_smul V u G.moor _]; rw [show (byG G u).spine=feeK .. from rfl, feeK_rit 6 F G.spine V u (absentD 6 o G.spine V hG.taxed hG.lev hs hv ht), ← smul_add, smul_mul_assoc, ← smul_add,mul_smul_comm,map_smul]
include hW
lemma gathered : reading (sumup G W) F D' V=reading G F D' V+reading W F D' V :=by
    rw [read_earn (sumup G W) V (sumupP G W hG α₁ α₂ hW) hs hv ht F D' hP hp hk hh hF,read_earn G V hG hs hv ht F D' hP hp hk hh hF, read_earn W V hW hs hv ht F D' hP hp hk hh hF,sumupp]
    obtain ⟨g,hg,hz⟩:=hG.costs; have hV:=grow_shape 6 o _ V ⟨_,fun i=>(hg i).sight,hz⟩ ht hv hG.sailX
    obtain ⟨w,hw,hz⟩:=hW.costs; have hZ :=grow_shape 6 o _ V ⟨_,fun i=>(hw i).sight,hz⟩ ht hv hW.sailX
    rw [rope_plus 6 V _ _ hZ hV, vote_add V G.moor W.moor, show (sumup G W).spine=addFilm .. from rfl, addK_rit 6 F G.spine V W.spine (absentD 6 o W.spine V hW.taxed hW.lev hs hv ht) (absentD 6 o G.spine V hG.taxed hG.lev hs hv ht),← map_add]; congr 1; ring
end
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.gathered
