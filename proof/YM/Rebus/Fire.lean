import YM.Rebus.Crave
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
set_option quotPrecheck false
variable (Z:Rise f N E J) (A: Stitch.Tablet Z I) (V₀: Finset (Finset I))(S': Finset E)(p:I→ Site f)(q:I→Bool)
local notation "xp"=> (sliceL L' h).parent∘ p
variable (Φ : Quince f N I)
local notation "Ap"=> spineP p N (majorT l*O.B)
local notation "Aw"=> can p (majorT l*O.B)
local notation "βg"=> gStep β
local notation "B0"=> radiusB τ
variable {Vp d mξ D' A₂ ιp h₈ :ℝ}
variable (Xz:Finset I)
local notation "Xy"=> shock Xz (Ap)
local notation "Xw"=> shock Xz (Aw)
local notation "Wx"=> heather xp (radiusB τ) Xz
local notation "p₁"=> parties Φ Xz
variable (hCp: TileW L' h K H Z A V₀ S' p q Xz r ε h₈ k t₀ l Φ)
-- grade particular costs. Numerics may require sign field.E
-- SKY always. no noisy root
lemma cost_up (hCp: TileW L' h K H Z A V₀ S' p q Xz r ε h₈ k t₀ l Φ): p₁∈Ledger Xy Xw (l*k) (l*t₀):=by
        have ht:=hCp.firefly; have hx:= hCp.card
        have hu i (hi:i⊆ Xz)(hv:i.Nonempty):= ht.scope i (hCp.closeP i hi) hv
        exact leaguer (Play.Chamber.lowMark Φ Aw Ap (Finset.Subset.refl Xz) hu) (Subset.refl _) (Subset.refl _) (by gcongr) (by gcongr)
include hCp
-- pull sensed V⊆Environmental including. Stitches sphere.Small support Origin
lemma ownsBr [Countable E] [Countable J] : let v:=G.equip N (radiusB τ); Play.Camp.owned (S:=Sⁱ) (P₀:=Z) v (roof v Z 30 (radiusB τ)) (Fj.pin (picksV f m (radiusB τ)) (fled A S' Xz) (∅: Finset J)) Wx:=by
    intro v; let K':=fled A S' Xz; let P₀:=Fj.pin (picksV f m (radiusB τ)) K' (∅:Finset J); have ht:0<B0:=by have hs:= H.laws.data.room.sight; omega
    let Rt:= Camp.Ray xp (baseTZ (radiusB τ))
    have hB: Camp.Gowns (S:=(Flight.visit L' K h)) v (roof v Z 30 (radiusB τ)) A p P₀ (10*radiusB τ) (τ:=τ) := prick L' h K G A p K' ht (fun i hi j hj=> (image_subset_image ((hCp.hollow.shape i (mem_filter.mp hi).1).2 j hj)).trans (Cape.puff R p l B0 O.B ht hCp.mast hCp.arch j)) -- Countable E needed.P0 hi shape
    refine Camp.frond (n:=10*B0) (τ:=τ) (S:=(Flight.visit L' K h)) v (roof v Z 30 (radiusB τ)) A p P₀ (?_) (Fj.pinK ..) hB Wx (?_)
    · intro i hi; unfold P₀ at hi; rw [Fj.pinX] at hi; exact hCp.hollow.shape i (mem_filter.mp hi).1 |>.1
    intro i hi j hj; unfold P₀ at hi; rw [Fj.pinX] at hi; refine Corona.halo_mono (?_) (?_); omega; exact singleton_subset_iff.mpr (mem_image_of_mem _ ((mem_filter.mp hi).2 hj))
-- fortune χ.
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.cost_up
#print axioms YM.MassiveQCD.Rebus.ownsBr
