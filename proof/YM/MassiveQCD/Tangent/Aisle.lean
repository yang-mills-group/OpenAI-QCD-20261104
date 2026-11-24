import YM.MassiveQCD.Charter.Calendar
import YM.MassiveQCD.Cabaret.Hydra
import YM.QCD.Finch.Dad
import YM.QCD.Moss.Muse
/-!
 # Aisle for the marked cluster assembly
 Actual sum layout. Costs on **all** with arbitrary marker support and generation preserved. Separate locator `seat` by supported true and coerces for repaint. -/
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
-- Anchor dictionary only needs single B. Y estimator equality of register. 
variable {E J: Type}[Countable E][Countable J]{D:Type}[Fintype D]
open King Moss Calm
variable (H) (P': Send S.ratio N D) (Y':Rise f N E J)
set_option quotPrecheck false
local notation "ζ"=> radiusB s
local notation "Y!"=> deckHue H P' Y' (roof P' Y' 30 ζ)
local notation "Z!"=> united (Y!) Y
local notation "A⁔"=> Warmlet H Y P' Y'
local notation "C₀"=> Clusters (Z!).Bright
namespace Warmlet
variable (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) (G:Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→RegularAddress c)
def callV (p:A⁔): C₀:= individual p.code
local notation "o☆"=> callV H Y P' Y'
noncomputable def seatsV (p:C₀): RegularAddress c:= if h:p ∈ Set.range o☆ then trunkP H Y P' Y' V (Classical.choose h) else G p -- binder order
local notation "L!"=> seatsV H Y P' Y' V G
lemma aisle (p:A⁔): L! (callV H Y P' Y' p)= trunkP H Y P' Y' V p:= by
     let r:= o☆ p
     have he: r∈Set.range o☆ := ⟨p,rfl⟩; exact (dif_pos he).trans (congr_arg (trunkP H Y P' Y' V) (copyQ H Y P' Y' _ _ (Classical.choose_spec he)))
lemma aisleWide (hp:∀ i, (G i).support=seatP (Z!).lightF i) (i:C₀): ((L!) i).site∈(G i).support ∧ (G i).support ⊆ ((L!) i).support ∧ ((L!) i).support⊆ Lattice.halo (Q.halo*ζ) (G i).support:=by
    by_cases he:i∈Set.range o☆
    · obtain ⟨p,rfl⟩:=he; have hV:(G (o☆ p)).support=past H Y P' Y' p:= (hp _).trans (cottage (Z!) p.code _ p.earns).1; rw [hV,aisle]; obtain ⟨hQ,hK⟩:= groom H Y P' Y' V p; exact ⟨hQ.symm ▸ (plateK H Y P' Y' V p).2.1,hK⟩
    rw [show L! i=G i from dif_neg he]; exact ⟨(G i).anchor,Subset.refl _,halo_subset ..⟩
-- Cost delta for bright extras, enough for every payment filler. Use weighted budget even if l=0 on non-portrait.
variable {H}
section limits
omit [Countable E][Countable J][Fintype D]
variable (Ω:ι⊕ Varn f c⊕Gaze c→ℕ)(Y:Fleet H (ι⊕ Varn f c⊕Gaze c) N)
lemma mintedH (p:Clusters Y.Bright) (he: 1≤ Y.depthT Ω p)(hv:∀ i, 0< Ω i → nectarP i): Dated Y Fury nectarP s p ∨∃ v:Y.Bright, ∃ i:ι, p=individual v ∧ Aliased Y v (.inl i):=by
    have h: stand Y nectarP p:=by
        by_contra hs; have hh:Y.depthT Ω p=0:= by
           unfold depthT; exact sum_eq_zero fun i _=> sum_eq_zero (fun j hj=> Nat.eq_zero_of_not_pos (fun he'=> hs ⟨i,j,hj,hv j he'⟩))
        omega
    by_cases hp: 2≤ crestP Y p
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp,h⟩))))
    obtain ⟨v,i,ht,hQ,hg⟩:= individualH Y p (by omega) nectarP h; cases i with | inl i=> exact Or.inr ⟨_,i,ht,hg⟩ | inr i=> exact hQ.elim
end limits
variable (H)
section pay
variable (Z₀:StageF f N E J)
-- critical accounting.Identity actual. No HEq commute. 
local notation "V0"=> Z₀.get 1
local notation "κ₀" => united (deckHue H P' (V0) (roof P' (V0) 30 ζ)) Y
lemma aislePower (x:Duke H Y P' (Z₀.get 1)): (κ₀).depthT (depth_charge Z₀ P' s) (callV H Y P' (V0) x.val)= Z₀.generation (col H Y P' (V0) x):=by
    let k:= x.val; let r:=k.code; let i:=k.label
    have he:r.val.toRight={Sum.inl i}:=by rw [(show r.val={Sum.inr (.inl i)} from k.earns)]; ext; simp
    let j:= col H Y P' (V0) x
    have hr:i.val={Sum.inr (.inl j)}:= duke H Y P' (V0) x
    change (∑ _:Option (Fin 0), ∑ i∈r.val.toRight, depth_charge Z₀ P' s i)=_; rw [sum_const,he,sum_singleton]; suffices hp:depth_charge Z₀ P' s (.inl i: Wound (roof P' (Z₀.get 1) 30 ζ) ⊕ ι)=Z₀.generation j by rw [hp,card_univ]; simp; rfl -- cases
    change depth_g Z₀ i.val = _; unfold depth_g
    simp_rw [hr]; have hh:= (slate H Y P' (V0) k j).mp hr; rw [show leftE {(Sum.inr (Sum.inl j) : Fj D E J)}={j} from hr ▸ (show leftE i.val= {j} from hh.1), show _root_.Eq (spent {(Sum.inr (Sum.inl j) : Fj D E J)}) ∅ from ?_]; rotate_left; · ext; simp [spent]
    simp
end pay
end Warmlet
end YM.QCD.Shells
