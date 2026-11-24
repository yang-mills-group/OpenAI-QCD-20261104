import YM.Parishes.Pact
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
open MassiveQCD.Plate MassiveQCD.Plate.Card MassiveQCD.Plate.Card.Iris MassiveQCD.Ribbon MassiveQCD.Apron MassiveQCD.Cupola
open QCD.Loom.Fleet Ursell QCD.Patron QCD.Loom QCD.Kites QCD.Ruby
variable {I J:Type}
local notation "T"=> Spine Unit
local notation "K"=> Keys c 6
noncomputable def bears (X: QCD.Patron.Rail c 6 I): QCD.Patron.Rail c (ample 6 Unit) I:= ⟨X.addr, fun i=> bearing Unit c 6 ∘ X.warp i⟩
set_option quotPrecheck false
variable (o:Site c)(p:Bool) (X:QCD.Patron.Rail c 6 I)(Pt:BudgetPoint)
local notation "r†"=>fun (_:Unit)=>p
local notation "o†"=>fun (_:Unit)=>o
local notation "V★"=>bears X
local notation "R!"=> rootR T K
local notation "d!"=> withdraw 6 (fun (_:Unit)=>o) v
local notation "b!"=> banknote 6 (fun (_:Unit)=>o) v
lemma moveD (x:EvenA c 6)(hv:0<v):d! (bearing Unit c 6 x)= rootR T K x:= by rw [← show b! (R! x)=bearing Unit c 6 x from real_sector ..]; exact MassiveQCD.Cupola.home 6 _ v hv _
variable (hx:Pill X Pt.threshold v Pt.B a b)(hV:0<v)
include hV
lemma aroundD : faultK 6 (o†) v (bears X)=X:=by
    have h{Z V: QCD.Patron.Rail c 6 I}(h:Z.addr=V.addr)(he:Z.warp=V.warp):Z=V:=by cases Z; cases V; congr
    refine h rfl (funext (fun i=> funext (fun V=>?_))); change vacR _ _ (d! (bearing _ _ _ (X.warp i V)))=_; rw [moveD o _ hV]; exact MassiveQCD.Cupola.off ..
include hx
lemma gorge : Wage.Tip 6 (o†) (r†) V★ Pt v a b:=by
   let U:=bearing Unit c 6; let X':=hx.uses; let R:=V★; have hp(i V):R.warp i V=U (X.warp i V):=rfl
   refine ⟨⟨⟨fun i V G he hh=> congr_arg U (X'.uses i V G he hh),fun i=> U.toLinearMap.toContinuousLinearMap.continuous.measurable.comp (X'.reads i),fun i V=>pushGate _ _ _ (X'.role i V), fun i V hz=> X'.buys i V (fun hv=>hz ((congr_arg U hv).trans (map_zero _)))⟩,fun i=> paySector (I:=Unit) (X.warp i) (hx.pigment i),?_⟩,fun i V=>?_⟩
   · obtain ⟨f,hf,h⟩:= hx.sold.cost; refine ⟨f,hf,fun i V=>?_⟩; change ‖token _ _ _ (bearing Unit c 6 (X.warp i V))‖ ≤ _; rw [skill, MassiveQCD.Apron.guide Unit _ v] -- need p change
     exact (MassiveQCD.Apron.current Unit ..).trans_le ((le_of_eq (show ‖token _ _ _ (X.warp i V)‖= _ from skill v _).symm).trans (h i V)) -- args
   change Well _ _ _ _ (bearing Unit c 6 (X.warp i V)); let y:= X.warp i V; rw [← show b! (R! y)=bearing Unit c 6 y from real_sector ..]; exact Mint.launch (Mint.initiate ∅ hV _ (rootE 6 p _))
lemma treasury (V:Grid c)(hv:1 ≤ v)(hp:0≤a)(he:1 ≤ b) : d! (heartK V★ Pt.threshold V) = R! (heartK X Pt.threshold V):=by
    let W:= bearing Unit c 6; refine Eq.trans (congr_arg (d!) ?_) (moveD o _ hV); unfold Kites.heartK; change _= W.toLinearMap.toContinuousLinearMap _; rw [ContinuousLinearMap.map_tsum _ (profits X V hv he hx.sold hp _)]; apply tsum_congr; intro i; change tK V★ _ _ i=W _; unfold Ruby.tK; split; next h=>rw [if_pos (show Gas.separated (blocked (QCD.Ruby.home X)) i ∧ flags Pt.threshold V = i.biUnion (oriD X) from h)]; exact (map_prod W ..).symm
    next h=> rw [if_neg (show ¬ (Gas.separated (blocked (QCD.Ruby.home X)) i ∧ flags Pt.threshold V = i.biUnion (oriD X)) from h)]; exact (map_zero W).symm
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.gorge
