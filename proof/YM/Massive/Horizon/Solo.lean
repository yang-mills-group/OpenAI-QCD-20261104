import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Detrain
import YM.QCD.Purse.Silo
/-! Every principal E singleton really occurs on the bank, regardless budgets. -/
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

open PhysicalNext.Repeat.Deck PhysicalNext.Repeat.Deck.Mint
lemma sunning {D:Type*}(X:D → Support c)(i:D) : Ac.Spark X {i} ∧ Collide.spark X {i}:=by
  simp only [Ac.Spark,Collide.spark,Finset.singleton_nonempty,true_and, Finset.mem_singleton,forall_eq];exact ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
private lemma luminous (Y:Fleet H ι N)(i:ι)(hv:(Y.ground i).Nonempty)(ht:Y.limit i=∅): ∃ p:Y.Bright,p.val={Sum.inr i}:=by
   let L: Pipe.Clump S ι:={Sum.inr i}; have hM:Y.fullA L=Y.ground i:=by unfold Fleet.fullA; rw [singleton_biUnion];rfl
   have hh:L.toLeft=∅:=by ext; simp [L]; -- maybe nested simp
   have hY : L.toRight={i}:=by ext;simp [L]
   have he: hatch S ∅=(∅:Molecule S):= Finset.map_empty ..
   refine ⟨⟨L,⟨hM.symm ▸ hv,(sunning _ (Sum.inr i)).1,?_⟩,?_⟩,rfl⟩
   · unfold Pipe.born; rw [hh,hY,←he]; refine ⟨Mint.hatchT ..,?_,?_⟩
     · intro i' hi j hj h'; rw [show i'=i from mem_singleton.mp hi,show j=i from mem_singleton.mp hj] at h'; exact False.elim (h' rfl)
     rw [(Mint.not_used ..).2,Pipe.filterP,singleton_biUnion]; exact ht.symm
   rw [hh,←he,Mint.unrostered]
lemma present (e:E): ∃ p:Duke H Y P' Y', col H Y P' Y' p=e:= by
   let i: Fj D E J:=Sum.inr (Sum.inl e); let r':= roof P' Y' 30 ζ; let u':Wound r':=⟨{i},(sunning r' i).2⟩
   have ht: (r' i).Nonempty :=by
      let s:=(Y'.row e).site; refine ⟨S.ratio.parent s,halo_subset _ _ ?_⟩; -- image
      refine Finset.mem_image_of_mem _ (Finset.mem_union_left _ ?_); exact halo_subset _ _ (Y'.row e).anchor
   obtain ⟨p,hp⟩:=luminous H (Z!) (Sum.inl u') (by
     change ({i}: Finset _).biUnion r' |>.Nonempty; rw [singleton_biUnion]; exact ht
   ) (by
     have hh:spent ({i}:Finset _)=(∅:Finset J):=by unfold spent; ext; simp [i]
     change typo (Y'.wish (spent {i}))=∅; rw [hh]; simp [Rise.wish,typo]
   )
   let u:Duke H Y P' Y':=⟨⟨u',p,hp⟩, e,rfl⟩
   refine ⟨u,?_⟩; have he:= duke H Y P' Y' u; change ({.inr (.inl e)}:Finset (Fj D E J))=_ at he; simpa using he.symm
/-- the bijection retaining even entries whose owner value happens to be zero -/
def address : Duke H Y P' Y' ≃ E:= Equiv.ofBijective (col H Y P' Y') ⟨copyL H Y P' Y',present H Y P' Y'⟩
end Warmlet
end YM.QCD.Shells
#print axioms YM.QCD.Shells.Warmlet.address
