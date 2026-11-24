import YM.Massive.Horizon.Summit
import YM.Massive.Commerce.Issue
import YM.QCD.Finch.Dad
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
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H (Port.Varn f c ⊕ Gaze c) N)
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
-- Anchor dictionary only needs single B. Y estimator equality of register. 
variable {E J: Type}[Countable E][Countable J]{D:Type}[Fintype D]
variable (H) (P': Send S.ratio N D) (Y':Rise f N E J)
local notation "L₀"=> P'
set_option quotPrecheck false
local notation "K₀"=> Wound (roof P' Y' 30 (radiusB s))
local notation "ζ"=> radiusB s
local notation "Y!"=> deckHue H P' Y' (roof P' Y' 30 ζ)
local notation "Z!"=> united (Y!) Y
local notation "A⁔"=> Warmlet H Y P' Y'
namespace Warmlet
local notation "Tz"=> (lore (trimP T R δ β B₀))
variable (p : Warmlet H Y P' Y')
open Moss King
variable (U: Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
local notation "U₀"=> Clusters (Z!).Bright
local notation "Q₀"=> Loom.first (Z!)
local notation "R'"=> trunkP H Y P' Y' U
local notation "A₀"=> Warmlet H Y P' Y'
set_option linter.unusedSectionVars false
lemma selects (j:U₀) (hp:Q₀ j): ∃ i:A₀,j=individual i.code:=by
    obtain ⟨c,i,hp,h⟩:=hp; exact ⟨Warmlet.mk i c h,hp⟩
noncomputable def teller (i:{j:U₀// Q₀ j}): A₀:= Classical.choose (selects H Y P' Y' i.val i.property)
local notation "l⁔"=> teller H Y P' Y'
lemma tell (i:{j:U₀//Q₀ j}): i.val= individual ((l⁔) i).code:= Classical.choose_spec (selects H Y P' Y' i.val i.property)
lemma tellinj: Function.Injective l⁔:=by intro i j he; exact Subtype.ext ((tell H Y P' Y' i).trans ((congr_arg (fun i:A₀=>individual i.code) he).trans (tell H Y P' Y' j).symm))
local notation "G!"=> P'
variable (Ω: U₀ → RegularAddress c) (hY:∀ i, (Ω i).support=(seatP (Z!).lightF) i)

-- residual budget on the restricted Warmlet gives marked term without any degeneracy charge outside budgets on Warmlet. No proposition about rotation here. --
variable (K': Hera.Rights su j)(ω₀:E→ℝ)(η₀:E→Bool)
local notation "p5"=> Warmlet.petty H Y (G!) Y' U
local notation "i⁔"=> Duke H Y (G!) Y'
variable (Z:ℝ) -- ambiguous Level
variable {a':ℝ} (χ:Chi)
lemma sectorCut (j:U₀) (h:¬ Q₀ j)(ht: King.stand (Z!) nectarP j) : Dated (Z!) Fury nectarP s j:=by
   by_contra he; have hp': crestP (Z!) j ≤ 1:=by
      by_contra! hz; exact he (Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hz,ht⟩)
   obtain ⟨q,u,hv,hm,hP⟩:= individualH (Z!) j hp' nectarP ht; rcases u with u|u; exact h ⟨q,u,hv,hP⟩; exact hm
lemma poor (T0:A₀→Prop)(w:E→Prop)(m:ℝ)(hC:Capstone L (Q.halo+8) O.power A B a' N' K' Z)(hε:0≤a')(hh:0≤ω₀)(hE:P'.trim+1≤R.B+R.B)(hZ0:P'.trim≤ζ)(hW₁:0<ζ)(hR:R.B≤2*ζ)(hQ₁:∀ p:i⁔,T0 p.val → w (col H Y P' Y' p))(hp : Valued Y'.row A (fun i=>if w i then ω₀ i else 0) R.B m) : Valued (R') B (fun p=> if T0 p then (p5) N' K' O Z ω₀ p else 0) ζ (a'*m):=by
      let wV(i:E):= if w i then ω₀ i else 0; let r₀ p:= p5 N' K' O Z wV p; let r(p:A₀):= p5 N' K' O Z ω₀ p
      have hR0:= bornZ H Y (G!) Y' U K' wV hE (fun i=>ite_nonneg (hh _) le_rfl) hC hR hZ0 hW₁ hε hp; have hR2:= perky H Y (G!) Y' U wV K' hR0
      have hR1(p:A₀)(hv:T0 p): r p=r₀ p:=by
          unfold r r₀ petty; split; swap; · rfl
          split; next h=> unfold doll wV; rw [if_pos (hQ₁ ⟨_,h⟩ hv)]
          next _=>rfl
      have h0(i):0 ≤ r₀ i:=vex (R') r₀ hR2 i
      apply valued_trim (R') r₀ _ _ _ hR2
      · intro i; change 0≤ if T0 i then r i else 0; split; next h=> exact (hR1 i h).symm ▸ h0 _
        next _=> exact le_rfl
      intro i; change (if T0 i then r i else 0) ≤ _; split; next h=> exact (hR1 i h).le
      next _=> exact h0 _
end Warmlet
end YM.QCD.Shells
#print axioms YM.QCD.Shells.Warmlet.poor
