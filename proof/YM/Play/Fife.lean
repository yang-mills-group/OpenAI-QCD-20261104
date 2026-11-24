import YM.Play.Park
import YM.Play.Lago
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
variable (χ:Chi)(U:Grid c)
open PhysicalNext.Repeat.Greenbelt
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
local notation "Cv"=> month (P₀:=P₀) M G p
local notation "sp" r=> prism T τ χ o.K U (allot r)
local notation "Sp" r=> planted (prism T τ χ o.K U (allot r)) (∅:Finset (Head S))
variable (hV:(united (closet H G M X z a) Y).Famous)
variable (Ω:Support c) (hM:M=roof G P₀ 30 (radiusB τ))
open Hypnos
variable (Z:Coat T F)(hZ:Z.manifest)(htZ:Z.x=τ)(hwZ:Z.width=o.K)
-- every interested trial (even D pin where separated) might need health on its FULL main support AND all its halos. 
open Stitch QCD.Anomaly Cupola
variable (w':Air f su)(hc:Calm Z Ω o.ξ β w') (hn:∀ i∈Ω,¬ Inside i Z.seeds (30*Z.B))
open Stitch.Tablet
variable (K₀:Finset E)(O₀: Finset D)
local notation "Pq" => pin O₀ K₀ (∅:Finset J)
local notation "Hz"=> (withdraw N z' a)
include H hV hM hZ htZ hwZ hc hn hw hk
variable (V: Matrix (Modes f N) (Modes f N) ℂ)
-- inertia spec in type.Avoid bubbles recursing equality of huge grade types
lemma horizonE (hp:owned (P₀:=P₀) G M (pin O₀ K₀ (∅:Finset J)) Ω) (hh:SliceRows.Stamp T)(ha:0<a)(hP:(∑ i∈ O₀,G.treats i (Z.input (Z.liftA β w')))=pond (Cove.ha c f N) V):
   let U:= Z.input (Z.liftA β w'); let B0:=∑ i∈ K₀,X.read O.threshold U i; let P:=QCD.Anomaly.splash (breezeP (Spine I) (G.shortP U)) (breezeX (Spine I) (stamping V)); Hz (skyM H G M X z a Y Pq F Z w') = P (NormedSpace.exp B0):=by
    intro U B0 P; let Q:=P (NormedSpace.exp B0); have hY:= thirst H G M X z a Y hw hk hV Ω hM Z hZ htZ hwZ w' hc hn K₀ O₀ hp hh ha -- edit
    apply Subtype.ext; dsimp only at hY; rw [hP] at hY; exact hY.trans (emitBy (Spine I) V _ (NormedSpace.exp B0))
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.horizonE
