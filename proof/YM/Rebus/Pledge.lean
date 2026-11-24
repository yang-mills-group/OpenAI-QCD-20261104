import YM.Rebus.Rides
/-! # Payload pricing projections. One-vertex estimate for common-tile.Id.Loan.Pν normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot Apron Apron.Grove
open Play.Camp Stitch
open scoped Topology Matrix InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁ p₀ q₁ q₂ r' r t t' A₀ A₁ B' u u' s' σ θ η η₁ h' x x' a a' w w' z b v' Ω' φ ε :ℝ}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {N i j n k m l B Q t₀: ℕ}
-- exported accounting for scripts.
variable (L':Flight i j)(h:f.val=c.val*L'.L.val)(K: KernelChoices)
variable {X: Run.St f}{T:Tube su (Flight.visit L' K h)}{F:Tree.Forest (Flight.visit L' K h).ratio}
local notation "Sⁱ"=> Flight.visit L' K h
local notation "R"=> sliceL L' h
variable {Q': Target su P}{o:Target.Order su W}
variable (H:Cash W τ μ L'.L Q' o C T (trimP T O r' β b))
variable (G:Sun L' c f h η h' z a a' m X)
-- Exposure permit after-L. Use gamma both capsules negotiated for one episode. Does not change Builder ink.E.
variable (z₀: Hypnos.State su)(Kp:Patch)(S:Bed)
variable (hT: SliceRows.Stamp T)
variable {θ' α v₀ v₁ v₂ v₃ Z δ δ' ρ Γ v₄ v₅:ℝ}
namespace Wreaths
private lemma absolute {f:ℝ→ℝ} (h:Rate su L a f): Rate su L a (fun i=>|f i|):= h.compare (Eventually.of_forall (fun i=> (abs_abs (f i)).le))
lemma yields {W μ C :ℝ} (gT:Hypnos.State su)(P:Teller su)(o:Target.Order su W) (Q':Target su P)(J:Patch)(V: ℝ→ℝ)(he:Rate su L (-(1/2)) V)(hp:∀ᶠ x:ℝ in atTop,0≤V x)(hJ:J.Branches P.bind su)(t₀:ℝ):
    ∃ v' :ℝ, ∃ cp φ D' cb:ℝ→ℝ, Rate su L (-(1/2)) cp ∧ Rate su L (-(1/2)) φ ∧ Rate su L (-1) D' ∧ Rate su L t₀ cb ∧∀ᶠ x:ℝ in atTop,∀ (i j:ℕ)(L': Flight i j), L'.L=L →∀ (c f:Side)(h:f.val=c.val*L'.L.val)(K:KernelChoices)(O:BudgetPoint)(r β b:ℝ)(T:Tube su (Flight.visit L' K h))(H: Cash W x μ L'.L Q' o C T (trimP T O r β b)), (Flight.visit L' K h).patch=J → SliceRows.Stamp T → ∀ (E B:Bed)(T₀:Towers (Flight.visit L' K h).patch.L)(p p' :Clip)(η η':ℝ), Striation (T:=T) E B T₀ p p' η η' → Yield L' h K gT E H (V x) v' (cp x) (φ x) (D' x) (cb x) 0:=by
    obtain ⟨U,D,E,hU,hD,hE,h⟩:=cartSigns su P o Q' J L gT V hJ he hp μ C
    obtain ⟨u,Dp,hdp,hV⟩:=georgic su P o Q' J L V hJ he hp μ C
    obtain ⟨b,hb,hh⟩:= Coat.alarm_bills P L (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) t₀ o.rare
    refine ⟨|u|,_,U,_,b,absolute hE,hU,(absolute hD).add (absolute hdp),hb,?_⟩
    filter_upwards [h,hV, hh, he.below (by norm_num) _ gT.r_pos] with x hx hy hp hv i j S hL c f hz K O r β v T H hJ hSt Y B T₀ p p' η η' hT
    subst L
    refine shareK S hz K H gT J hSt B T₀ p p' Y hJ hT hx hy ((le_abs_self _).trans hv) hp.1 (fun F X hX ht he i=> ?_)
    have hg:= (H.laws.data.localP _ X hX ht he).sails; have he:=(hp.2 c f _ T F X hX H.laws.data.funds.length_eq hg (trimP T O r β v) (hX.symm ▸ H.laws.intake) {i}); rw [card_singleton,pow_one] at he; exact he
end Wreaths
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.Wreaths.yields
