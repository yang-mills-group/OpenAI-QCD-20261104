import YM.MassiveQCD.Apron.Groves
import YM.MassiveQCD.Charter.Lane
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "Β" => Ribbon.banknote N ((S').ratio.parent ∘ A) φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c N ⊕ Ribbon.Spine I
namespace Grove
open PhysicalNext.Repeat.Greenbelt Territory Horticulture
open scoped PhysicalNext.Repeat.Greenbelt
variable {q₁:I→Bool}{χ:Chi}{θ a₁ d₁ c₁:ℝ}
variable (hw:Y.Wave O.threshold q₁ A)
set_option linter.unusedSectionVars false in
lemma essences {E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E'][FiniteDimensional ℝ E']{V:E'→ Config su c}{x:E'} {j:ℕ} (hp:(Tx).Famous)(_he:Mode V x j a₁)
    (hv:∀ i, Zest (fun (U: Config su f) t=>(Vx).works i U (V t)) x j) :∀ i,Zest (fun (U:Config su f) t=>(Tx).works i U (V t)) x j:=by
   rintro (i|i|i)
   · obtain ⟨_,d,h⟩:=hp.pays (Sum.inl i) (V x); exact Zest.parallel ((norm_nonneg _).trans (h 1)) h
   · exact (hv (.inr (.inl i))).replay (bearer I c N)
   exact (hv (.inr (.inr i))).replay (bearer I c N)
include hw
-- unmarked portrait transfer on same widths.
lemma accustomed (hp : Colored (Vx))(hv:(Vx).speaking)(hB:0<radiusB τ) : (Tx).speaking ∧ Colored (Tx):=by
   let UT:= loommark I (united (VarnC H U N) (sailP H Γ N)); have hx: UT= united (loommark I (VarnC H U N)) (loommark I (sailP H Γ N)):= by unfold UT Fleet.united loommark; congr 1; funext i U V; cases i<;>rfl
   have ht:Colored (Y'):= flaps H (Z') (Zⁱ) Y A φ hw ((roofs (Z') P₀ 30 B le_rfl hB).1) (Stitch.Tablet.tonal G N (radiusB τ))
   have he: Tx = united (Y') UT:=by rw [hx]; rfl
   rw [he]; refine ⟨?_,?_⟩
   · refine Fleet.voice (Y') (floorsT H _ _ Y A φ hw) (utter I (united (VarnC H U N) (sailP H Γ N)) (fun i=> hv (.inr i)))
   have hU: Colored UT:=by
      apply larking; constructor; intro i; exact ⟨(hp.warp i).cont,fun j U V=>(hp.warp i).verse (.inr j) U V⟩
   exact ⟨fun i=>Fleet.graft _ (ht.warp i) (hU.warp i)⟩
end Grove
end YM.MassiveQCD.Apron
