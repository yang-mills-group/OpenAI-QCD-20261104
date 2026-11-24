import YM.Massive.Lens.Lend
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
lemma carries_up (P:ι→Dye)(p:Clusters Y.Bright)(he:(Y.toner P p).1≠0)(T:ι→Prop)(hp:∀ i,P i≠0→ T i): King.stand Y T p:=by
    by_contra h; have hh: Y.toner P p=0:= sum_eq_zero fun i _=> sum_eq_zero fun j hj=> by by_contra hY; exact h ⟨i,j,hj,hp j hY⟩
    exact he (congr_arg Prod.fst hh)
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
abbrev chosen (x:C₀): U₀ := individual x.val.code
noncomputable def horizonKey (e:E): U₀:= chosen G H' O₀ Gz H Y' Ξ Γ ((address H (R⁔) (G!) Y').symm e)
local notation "Q⁺"=> chosen G H' O₀ Gz H Y' Ξ Γ
local notation "E⁺"=> horizonKey G H' O₀ Gz H Y' Ξ Γ
local notation "D'"=> col H (R⁔) (G!) Y'
lemma chosen_inj {u v:C₀}(h: Q⁺ u= Q⁺ v): u=v:= Subtype.ext (copyQ H (R⁔) (G!) Y' _ _ h)
lemma key_coded (e : E) : D' ((address H (R⁔) (G!) Y').symm e)= e:= (address H (R⁔) (G!) Y').apply_symm_apply e
lemma key_copy (i j:E) (h:E⁺ i=E⁺ j):i=j:= Equiv.injective _ (chosen_inj G H' O₀ Gz H Y' Ξ Γ h) -- need explicit
lemma keyed (p:C₀): E⁺ (D' p)=Q⁺ p:= congr_arg (Q⁺) ((address H (R⁔) (G!) Y').symm_apply_apply p)

lemma directL (Y: Fleet H ι N)(i:ι)(p:Y.Bright)(he:Aliased Y p i)(P:ι→Dye): Y.toner P (individual p)=P i:=by
    have hh:p.val.toRight={i}:=by rw [show p.val={Sum.inr i} from he]; ext; simp
    change ∑ _ : Fin (0+1), ∑ j∈p.val.toRight,P j=P i; simp [hh]
noncomputable def wages (E' : E→Dye)(J':J→Dye): U₀→Dye:= Fleet.toner (M₀) (rungC G H' Gz Y' E' J')
variable (E' : E→Dye)(J₁: J→Dye)
local notation "Dv"=> wages G H' O₀ Gz H Y' Ξ Γ E' J₁
lemma horizonPay (p:C₀): Dv (Q⁺ p)=E' (D' p):=by
     unfold wages; change (M₀).toner _ (individual p.val.code)=_; rw [directL G H' O₀ H _ (.inl p.val.label) _ p.val.earns]; change Villa.taxes E' J₁ p.val.label.val=_; unfold Villa.taxes; rw [stop H (R⁔) (G!) Y' p.val,(slate _ _ _ _ p.val (D' p)).1 (duke H (R⁔) (G!) Y' p) |>.1,sum_empty,sum_singleton,add_zero]
omit [Countable E] [Countable J] in
lemma shadowed (p:U₀)(h:(Dv p).1≠0): King.stand (M₀) nectarP p:=by apply carries_up (M₀) (Villa.rungC G H' Gz Y' E' J₁ (τ:=s)) p h; rintro (i|i) hi; exact trivial; exact (hi rfl).elim
end Warmlet
end YM.QCD.Shells
