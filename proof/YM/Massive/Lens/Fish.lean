import YM.Massive.Lens.Lily
import YM.Massive.Lens.Petal
import YM.Massive.Lens.Feet
import YM.Massive.Struck.Inherit
import YM.QCD.Finch.Tissues
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
namespace Warmlet
variable {β':ℝ}{t₅ p':ℝ}{θ σ:ℝ}
open Finch Stem Grove Moss Calm
open Villa King
open YM.QCD.Loom.Fleet Struck
-- departure stage in G.Coordinates
variable {j0 j1 p₀:ℕ}{a₁ b₁ a₂ b₂ m₀ t₀ η₀ :ℝ} (G:Flight n k)(H':f.val=c.val*G.L.val) (O₀:KernelChoices)
local notation "S'"=> G.visit O₀ H'
variable {T:Tube su (G.visit O₀ H')}{P₀:Plan n}{T₁:Garden.Offer 1 a₁ b₁}{T₂:Garden.Offer 2 a₂ b₂}
variable (Gz : Jets.Sun G c f H' t' u q η a l (pesto P₀ G H' (trunkM T₁ T₂ w m₀ f)))
variable (H:Cash W s μ G.L Q o C T (trimP T R δ β B₀))
variable {E J: Type}[Countable E][Countable J]
variable (Y':Rise f N E J) (U: Cash W s μ G.L Q o C T (lore (trimP T R δ β B₀)))
variable  {G' : St f}{X₀:ℕ→Atom su 2}{P':Plan k}{J' K' ε' τ:ℝ}(Ξ: Swathe G H' G' X₀ P' d C' J' K' ε' m)(Γ:Land c (Site c) (Site c))
local notation "ζ"=> radiusB s
set_option quotPrecheck false
local notation "G!"=> Gz.equip N ζ
local notation "R⁔"=> united (VarnC H Ξ N) (sailP H Γ N)
local notation "I₀"=> deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)
local notation "M₀"=> artV (deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)) Ξ Γ
local notation "U₀" => Clusters (M₀).Bright
local notation "Q₀" => ExtraK (I₀) Ξ Γ
local notation "A₀"=> Warmlet H (R⁔) (G!) Y'
local notation "R'"=>trunkP H (R⁔) (G!) Y' U
variable (χ:Chi)

-- subst address.R'. via Existential generic.P no bizarre Defeq across Mats. 
variable (K₂: Hera.Rights su j0)(N':Libretto su j0)(A3 V':ℝ)(β':E→ℝ)(K₀:E→Bool) {uF:ℝ}
local notation "C₀"=> Duke H (R⁔) (G!) Y'
local notation "Q⁺"=> chosen G H' O₀ Gz H Y' Ξ Γ
local notation "E⁺"=> horizonKey G H' O₀ Gz H Y' Ξ Γ
local notation "D'"=> col H (R⁔) (G!) Y'

variable (E' : E→ Dye)(J₁ : J→ Dye)
local notation "Dv"=> wages G H' O₀ Gz H Y' Ξ Γ E' J₁
variable (W₀:Site f × Flavor N→E)(T1 T2 T3:E→Prop) -- addr
local notation "G⁺"=> riseP G H' O₀ Gz H Ξ Γ Y' W₀ -- order check
-- payments.exp witness. all needed: for each flavor HR.B origin M.E.Act. 
variable {y' A' epsilon MS LS HS:ℝ} (mχ:Flavor N→ℝ)
include H'
lemma fernScale (x:ℝ): Fintype.card (Site f × Flavor N)*(2*(fern G.L ^5*x))/(Fintype.card (Site c):ℝ)= (Fintype.card (Flavor N):ℝ)* (2*fern G.L*x):=by
    unfold fern; rw [Fintype.card_prod, site_card, site_card,H']; push_cast; field_simp
lemma burst (hp:Boost G H' O₀ Gz H Y' (R⁔) N' K₂ V' β' K₀ U χ O t B b)(h0:∀ i,coverNumber R.B (Y'.row (W₀ i)).support ≤1 ∧ ∀ x,Y'.main (W₀ i) x=Y'.main (W₀ i) 1)(Ω: U₀→ RegularAddress c)(ht:0<t)(F: Gem c N U₀)(hV:F.view=(crude (M₀) χ Ω).view)(he:0≤B)(hF:Function.Injective W₀)(hχ:∀ i, (E' (W₀ i)).1=1) (hW:∀ i,Stew.panel 2 (Y'.main (W₀ i) 1).val=Grass.form (Finch.stripe N i.2 (localX i.1 ((mχ i.2:ℂ) • 1)))) (hA: Licence O B MS t (muteK F fun i=> i∈ Set.range (G⁺)))(hB:Licence O B LS t (muteK F (fun i=>(Dv i).1=1∧i∉Set.range (G⁺))))(hy:∀ i,β' i≤ y) (b₁:Flavor N):
       ‖flagRead b₁ t (Patron.total (muteK F (fun i=>(Dv i).1=1)) O.threshold 1)-t^2*(mχ b₁*flagW (Garden.barP G H'*proton G H'))‖ ≤ (Fintype.card (Flavor N):ℝ)*(2* fern G.L*y)+ LS:=by
    rw [Garden.rotateP (e:=H') P₀, ← fernScale G H']
    refine rate_earned F (proton G H') (G⁺) ((show Injective (E⁺) from key_copy G H' O₀ Gz H Y' Ξ Γ).comp hF) _ (fun i=>Iff.rfl) _ hA hB (fun i hi=>?_) mχ _ hW b₁ (fun i=>?_) ht he -- key_copy not Injective def? Lean coercion no ext arg maybe adjust
    · obtain ⟨j,rfl⟩:=hi; change (Dv (E⁺ (W₀ j))).1=1; rw [profitE]; exact hχ j
    rw [hV]; refine (massBoost G H' O₀ Gz H Y' U Ξ Γ χ K₂ N' V' β' K₀ W₀ hp h0 b₁ i Ω ht).trans ?_; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hy _) (pow_nonneg (fern_pos G.L).le _)) (by norm_num)
end Warmlet
end YM.QCD.Shells
