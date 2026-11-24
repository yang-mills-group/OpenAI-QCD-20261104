import YM.TIPS.Splice
import YM.TIPS.Stir
import YM.TIPS.Humbug
import YM.TIPS.Tap
import YM.TIPS.Tight
import YM.TIPS.Units
import YM.Differ.Treasures
import YM.TIPS.Tip
import YM.Oars.PursePages
import YM.Cape.Fuel
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D U :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Taxing
open QCD.Ruby Cove Cape SC
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j N:ℕ}
variable (q:I→Bool)
 open Stitch
-- charter activation Fame.New
variable (H: Massive.SourceRead.TaperHol){S:YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit S)(o:I → Cover)(r:I→ Label d)(F:∀ i:I,CentreFrame (c:=c) P v (r i) (q i) B (o i) (l+1) Unit Empty)(W:I→ℝ)
open Stags
variable {θ z:ℝ}
variable (hk:Pilot H B d P.order P.power k n l z θ)(hX:∀ i,Published (F i) H k n α t (W i) 0)(ht:1≤v)(ha:0 ≤ Γ)(hH:30*(l+1)≤ c.val)(hC:∀ i:I,Courtesy B (o i) (r i) (q i) P (F i) 4 Γ)(hG:∀ i j, ((ritual (F i)).addr j).support⊆Massive.Poised.Carte.Hem.pot P.B c (o i)) -- cost viewport
set_option quotPrecheck false
local notation "O"=> wrap c ∘ o
local notation "I₁"=>Jars d ⊕ Unit
local notation "Xp"=> unionL 6 (fun i:I=> burstY 6 q i (ritual (F i)))
local notation "T!"=> birthV Xp P.threshold
variable (p:I→ Label d) {U':I→Type}(M:∀ i,CentreFrame (c:=c) P v (p i) (q i) B (o i) (l+1) (U' i) Empty)(D':I→ℝ)(a :ℝ)(X:Reel c 6 I E)(hp:∀ i,Published (M i) H k n α t (D' i) 0)
local notation "Tφ"=>fun i:I=> simple (M i) (F i)
local notation "L₁"=>Gel.May.Roles q B o P d p l M X
local notation "L₀"=>Gel.May.Roles q B o P d (p+r) l (Tφ) X
local notation "Plume"=> GreenCap.Pavilion.EntranceW.plume q o B r l P (fun _=>Unit) F
local notation "Bp!" i:arg Q=> burstY (c:=c) 6 q i (ritual (Q))
-- world P≠ S inflated.G cost repair.Se.
local notation "A"=> Keys c 6
local notation "Ψ"=>Patio (A⊕Spine I)
variable (K:Code c 6)(e:ℂ)(F₀:Grid c→ℝ)(S₀: QCD.Run.St c)(V':BudgetPoint)(Q:Set (Finset I))(Y:Grid c→ Patio (Keys c 6⊕Spine I))(x:ℝ)(hw:V'.threshold=P.threshold)(hB:Tropic m L x)
variable (hP:P.B=highR L x) (hf: Fires (wrap c ∘ o) m)(hS:∀ i∈Q,Spaced (wrap c ∘ o) i P.B)
local notation "Z" b:arg=> taxK L x b
local notation "Zt"=>( (taxK L x ((2-1)/2))⁻¹)
local notation "α0"=> (1/8:ℝ)
-- use Tally K input heat ∃ even for all shutters
open Quills
include hk ht hH hw
variable (R : I→ Grid c→ QCD.Lat.Fields c 6)
local notation "Yᵀ" i:arg=> (spineV B (o i) (r i) (q i) P (F i))
lemma watchV (hh: PayLayer H B o q P K e F₀ S₀ p D' (l:=l) V' v (Z 1) a Zt Y Q k n) (hR:∀ i,spineV B (o i) (r i) (q i) P (F i)= R i) : ∀ (q':ℕ)(s:Fin q'→I)(V:Grid c), Quills.crest s∈ Q→Quills.numbered q (Keys c 6) s (Y V * NormedSpace.exp (∑ i:I,GreenCap.Pavilion.EntranceW.plume q o B r l P (fun _=>Unit) F i V)) = ∑ T∈(Quills.crest s).powerset,Quills.spliceG q s T • ((List.ofFn fun i=>R (Quills.tour T i) V).prod * Quills.numbered q (Keys c 6) (Quills.tour (Quills.crest s \ T)) (Y V)):=by
    obtain ⟨JJ,hI,J0,hJ,M,G,HG,Lb,J',h1,h2,h3,h4,hZ,hW⟩:=hh.booth
    let f:= Gel.May.Roles q B o P d p l J' M; have hp: Reel.Book O q f:=Gel.May.jointly q o M _ h2.booked (Stags.gatherings 6 (wrap c ∘ o) q _ (fun i=> Stags.burstP 6 O q _ _ (rendition hk rfl rfl ht hH _ (hZ i)|>.1)))
    intro z s V hz
    let w:=stampRoll B o q K e F₀ S₀ p P v l J' M Lb V'.threshold V; let Z':=Plume
    have hY':ValidPieces (Keys c 6) q Finset.univ w:=shores _ _ _ _ _ _ _ _ hp (hw.symm ▸ h3)
    let U:=Quills.crest s; let j':= Y V; let S' := NormedSpace.exp (∑ i:I,Z' i V)
    have hZ'(i:I): (Z' i V).val=stake A (burst q {i}) (R i V):= ((GreenCap.Pavilion.EntranceW.wholeq ..).2 : Cove.light _ (Z' i V)= _).trans (congr_arg (stake A (burst q {i})) (congr_fun (hR i) V)) -- implicit
    have hx : Quills.numbered q A s (Y V*S')= Quills.numbered q A s (w*S'):=by
        unfold numbered; change signG q s • pluck A _ _= signG q s • pluck A _ _; apply congr_arg; apply phoenixC A _ _ U _ _ (located q U); rw [map_mul,map_mul,hW _ hz V]
    refine hx.trans ((mul_comm S' w ▸ Quills.serveV A q s (fun i=>Z' i V) (fun i=>R i V) w hZ' hY').trans ?_) -- rewrite direction?
    refine sum_congr rfl fun i hi=>congr_arg (fun t=> spliceG q s i • ((List.ofFn fun j=> R (tour i j) V).prod * t)) ?_
    unfold numbered; let v':=Quills.tour (U\ i); change signG q v' • pluck A _ _= signG q v' • pluck A _ _; apply congr_arg; apply phoenixC A w _ U (hW _ hz V).symm; rw [club]; exact fun j h=>(Finset.mem_sdiff.mp (Ribbon.located q _ _ h)).1
end Taxing
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Taxing.watchV
