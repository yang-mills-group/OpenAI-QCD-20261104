import YM.Poised.Crested
import YM.Poised.Prong
/-!
# Accounts at all apertures. Covers actually Y^+ when using these. Bound with polynomial factor in length of input support (allows NOTshort in same currency).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y:ℝ}{H:Cash W τ μ L Q o C T (trimP T O δ β y)}{ι κ I E J D:Type}{N:ℕ}
variable {n p k d G l:ℕ} {a u r q v σ R z t w m γ α θ η :ℝ}{s:Side}
variable {V:Offer 1 α θ}{V':Offer 2 t η}
variable {P₁:Plan p}
variable {N':Libretto su n}{D:Heir.Record}{χ:Chi}
variable {P':Flight p k} {H':f.val=c.val*P'.L.val}
variable (Zt:Sun P' c f H' (coneK L r τ) γ q u a l (pesto P₁ P' H' (trunkM V V' (haloK L τ) m f)))(Zv:Sun P' c f H' (coneK L r τ) γ q u a l (pesto P₁ P' H' (trunkM V V' (haloK L τ) 0 f))) (hr:FairT P₁ D N' d l L τ u r q a v σ R O)
variable {WQ : Support f}(Γ:Cash W τ μ L Q o C T (Sands.lore Rx)) (hP:Plays N' D O Rx.p P T τ) (i:ℕ) (h:S.ratio=sliceL P' H') (hL:P'.L=L) (hn:1 ≤ n)
variable (hx:halo (radiusB τ+1) WQ ⊆ ((lore Rx).activities.reg i).support) (hu:0 < u)(hm:|m| ≤ haloK L τ)(hq:0 ≤ q)
set_option quotPrecheck false
local notation "Φ"=> (Zt.equip 6 (radiusB τ)).shortP
local notation "Xp"=> ((Sands.lore Rx).activities.reg i).support
include hL Zv Γ hP hx hu hm hn hr h hq
open Next.SectorChange
lemma slotsPrice (K: Forest S.ratio)(y:S.Choices) (U:Grid f)(hV:BeamRaw ((lore Rx).activities.reg i).support U (Sands.homeQ K Γ χ 1 i y D) v): Stanch WQ S.ratio ((Zt.equip 6 (radiusB τ)).shortP U - powerF (N:=6) (proton P' H')) d R:=by
    let p:=(lore Rx).activities.reg i; let X:= p.support; obtain ⟨V,C,z,ε,Z,hp,hz,hZ,hε,hπ,hM,hb,hp₁,hK,hv,ht,hA,hc⟩:= hr.tribute
    have h₀ : 0 ≤ gStep Rx.beta:=by unfold gStep; positivity
    let L₀:= homeQ K Γ χ 1 i y D; let B₀:= loom O (Heir.reach τ) N'.C; let a':=mapcase Γ i K
    have he':Agrees (inspected X) 1 L₀:=by
       let l:= (a'.extra (1:Frame c) (gStep Rx.beta)); have h:= (Fountain.stemming (k:=y) (q:=χ) (d:=0) a' hP (1:Grid f) 0 h₀ (by rw [show Next.SectorChange.tape (0:Prices su _)=0 from rfl,norm_zero,mul_zero]; positivity [D.guards,Rx.p.threshold_pos]) (0:Directions su c)).2.self_of_nhds
       simp only [map_zero,Work.G07.at_zero_increment] at h; have ha : Lattice.gauge (fun i:Site f=>su.lieExp ((0:Site f→su.Color) i)) L₀=L₀:=by funext i; simp [Lattice.gauge]
       change Agrees (inspected X) (increment 1 (display T K τ y true 0)) (Lattice.gauge _ L₀) at h
       rw [((hP.acts K y).costs true).home, Work.G07.at_zero_increment,ha] at h; exact h
    have hY₀: BeamRaw X U 1 v:=fun i hi hj=>by rw [he' _ (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hj)]; exact hV i hi hj
    have hX':beamAt X U 1 z:=gridBeam _ (hv _ _ _ _ _ hY₀) hp₁
    have he := canvass Zt Zv U (mores hX' hx) hK hz hu ht hZ
    let f0:= flareV (proton P' H')
    intro j hj; change (∑ l:Keys c 6,meets S.ratio _ _ _*‖(Φ _-_) _ _‖)≤ _; conv_lhs => arg 2; ext; arg 1; rw [h];
    exact (he j hj).trans (by rw [hL]; exact hA m hm hq Zt.stable.calf.le) -- `powerF` definal?
end YM.Massive.Poised
