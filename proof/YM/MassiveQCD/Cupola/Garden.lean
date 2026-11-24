import YM.MassiveQCD.Cupola.Left
import YM.MassiveQCD.Cupola.Funnel
import YM.MassiveQCD.Apron.Card
/-! # Bridge Cupola and Siege.Tower: paid on ONE trajectory -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
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
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote N loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c N ⊕ Ribbon.Spine I
local notation "d!"=> (vacR I' (Keys c N)).comp (withdraw N loc φ)
local notation "Fuel"=> Pipe.Clump S' (Wound (Zⁱ)⊕ Varn f c⊕ Gaze c)
variable (q':I→Bool)
local notation "R₁"=> Sum.elim (fun (u:Wound (Zⁱ)) => Y.markers u.val) (fun _:Varn f c ⊕ Gaze c=>∅)
variable {χ:Chi}{θ t:ℝ}{m₁ m₂:ℕ}
variable (hx:Neat Y)(he:Supplies L' d K H G U Γ Y A φ χ q' θ t m₁ m₂)
structure Destiny : Prop where
    clan : Regal N loc φ q' Tx R₁
    reflects (V:Grid c)(u:Clusters (Tx).Bright) : (d!) (honest Tx χ V u)= honest Vx χ V u
    dark (V:Grid c)(u:(Tx).Faber) : (d!) ((claim Tx χ).warp u V)=(claim Vx χ).warp u V
    pours (V:Grid c) (u:(Tx).Faber) : Well N loc φ q' ((claim Tx χ).warp u V)
    hearth (V:Grid c) (u:Clusters (Tx).Bright)(X:Clusters (Tx).Bright→RegularAddress c) : Mint N loc φ q' (swingE N Tx R₁ u) ((crude Tx χ X).view u V)
include he
include hx
omit [Countable E][Countable J] in
lemma bedchamber : ∀ i V W, (d!) ((Tx).works i V W)=(Vx).works i V W :=by
    let Yv:=Tx; let Z:=(d!); have hφ:0<φ:= zero_lt_one.trans_le he.strength
    have hv (i: EvenA c N): Z (Apron.bearing I c N i)= i:=by change vacR _ _ (withdraw _ _ _ _)=_; rw [← braces I loc,home _ _ _ hφ]; exact off I' _
    have h i V W: Z (Yv.works i V W)=(Vx).works i V W:=by
       rcases i with i|i|i
       · change Z ((δ⁻¹ ^ budget P₀ i.val:ℝ) • Β (Y.hue O.threshold (Z') i.val V))= _; rw [Fleet.plank]; change _ • vacR I' _ (withdraw _ _ _ _)= (δ⁻¹ ^ budget P₀ i.val:ℝ) • _; rw [home N _ _ hφ]; exact congr_arg _ (hueR Y (G.equip N B) hx ..)
       · exact hv _
       exact hv _
    exact h
omit hx
omit [Countable E][Countable J] in
lemma intent : Fleet.Regal N loc φ q' (Tx) R₁:=by
    have hφ:0<φ:= zero_lt_one.trans_le he.strength
    constructor; intro i V W; have hp (x: EvenA c N): Mint N loc φ q' ∅ (Apron.bearing I c N x) :=by
       rw [← braces I loc]; refine Mint.initiate _ hφ _ ?_; unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
    rcases i with i|i|i; swap; · exact hp _
    rotate_left; · exact hp _
    apply Mint.euro hφ; apply Mint.initiate _ hφ; exact (Y.lights_hue (G.equip N B) he.property (roofs (G.equip N B) P₀ 30 B le_rfl he.room.2).1 i.val _).1
omit he
local notation "Tag"=> Fleet.align Tx (Vx).works
set_option linter.unusedSectionVars false in
lemma fairEq : Fleet.align (Tx) (Vx).works=(Vx):= by dsimp only [Fleet.align,vantage,tableau,Fleet.united,loommark,closet,deckHue]-- maybe dsimp Foot orientation
include hx he
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 450000 in
lemma reflectingD (hX:(Vx).Famous)(V:Grid c)(x:Clusters (Tx).Bright) : (d!) (honest Tx χ V x)= honest Tag χ V x:=by
    have hg: (Tag).Famous := Eq.mp (congr_arg (fun x=>x.Famous) (fairEq L' d K H G U Γ Y A φ).symm) hX
    exact loomDay (Tx) (d!) (Vx).works he.title.favorable (bedchamber L' d K H G U Γ Y A φ q' hx he) χ V hg x
lemma darkD (V:Grid c)(x:(Tx).Faber) : (d!) ((claim Tx χ).warp x V)=(claim Tag χ).warp x V:=by
    obtain ⟨F⟩:= Tree.select (S').ratio L'.odd; exact mottoDay (Tx) (d!) (Vx).works he.title.favorable (bedchamber L' d K H G U Γ Y A φ q' hx he) χ V (Supplies.reveals L' d K H G U Γ Y A φ he F V|>.1) x.val
lemma destined (hX:(Vx).Famous) : Destiny L' d K H G U Γ Y A φ q' (χ:=χ) :=by
    have hφ:0<φ:= zero_lt_one.trans_le he.strength; have hw := he.title.favorable; have hd:= intent L' d K H G U Γ Y A φ q' he
    refine ⟨hd,fun V Uv=> reflectingD L' d K H G U Γ Y A φ q' hx he hX V Uv,fun V x=> darkD L' d K H G U Γ Y A φ q' hx he V x,fun V x=> mottoM N loc φ q' Tx R₁ hd hφ χ V x.val hw, fun V i Uv=>crudeM N loc φ q' Tx R₁ hd hφ χ V i Uv⟩
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.destined
