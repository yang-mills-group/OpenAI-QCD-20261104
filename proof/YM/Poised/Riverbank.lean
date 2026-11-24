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
lemma leaps (ho:Short S Rx.p ((lore Rx).activities.reg i).support)(K: Forest S.ratio)(y:S.Choices)(V':Grid c)(g: Frame c)(hG:Heir.Canvas O (Brim.plate Γ i).site (Heir.reach τ) V' g n N'.C) (U:Grid f)(hV:BeamRaw ((lore Rx).activities.reg i).support U (Sands.homeQ K Γ χ V' i y D) v): Stanch WQ S.ratio ((Zt.equip 6 (radiusB τ)).shortP (Lattice.gauge (g ∘ S.ratio.parent) U) - powerF (N:=6) (proton P' H')) d R:=by
    let p:=(lore Rx).activities.reg i; let X:= p.support; obtain ⟨V,C,z,ε,Z,hp,hz,hZ,hε,hπ,hM,hb,hp₁,hK,hv,ht,hA,hc⟩:= hr.tribute
    let g':= g ∘ S.ratio.parent; let L₀:= homeQ K Γ χ V' i y D; let B₀:= loom O (Heir.reach τ) N'.C
    let a':=mapcase Γ i K
    have h₀ : 0 ≤ gStep Rx.beta:=by unfold gStep; positivity
    have hw:BeamRaw X (Lattice.gauge g' L₀) 1 (V*B₀*(D.Q+N'.M+N'.M)):=printing (k:=y) (q:=χ) (d:=0) a' hP hG ho hn p.anchor (1:Grid f) h₀ hε hp hπ hM
    have hX:= hv _ _ _ _ _ (celia _ _ _ hV g'); have hY:= raysFort _ _ _ hX (hv _ _ _ _ _ hw)
    have hX':beamAt X (Lattice.gauge g' U) 1 z:=fun i a b=> (hY i a b).trans hb
    have he := canvass Zt Zv (Lattice.gauge g' U) (mores hX' hx) hK hz hu ht hZ
    let f0:= flareV (proton P' H')
    intro j hj; change (∑ l:Keys c 6,meets S.ratio _ _ _*‖(Φ _-_) _ _‖)≤ _; conv_lhs => arg 2; ext; arg 1; rw [h];
    exact (he j hj).trans (by rw [hL]; exact hA m hm hq Zt.stable.calf.le) -- `powerF` definal?
omit hP hL Zv hm hn hq
include hx hr h hu Zt Γ -- ?
lemma streak (U V:Grid f)(hW:BeamRaw ((lore Rx).activities.reg i).support U V v): Stanch WQ S.ratio (Φ U - Φ V) d σ:=by
    obtain ⟨A,C,z,ε,Z,hp,hz,hZ,hε,hπ,hM,hb,hp₁,hK,hv,ht,hA,hc⟩:= hr.tribute
    have hX := gridBeam _ (hv _ _ _ _ _ hW) hp₁
    rw [h]; exact fun j hj=> (scrolls Zt U V (mores hX hx) hK hz hu.le d j hj).trans hc
-- sol.L budget contract
end YM.Massive.Poised
#print axioms YM.Massive.Poised.leaps
