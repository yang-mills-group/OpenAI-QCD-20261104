import YM.MassiveQCD.Tangent.Aisle
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
local notation "o☆"=> callV H Y P' Y'
local notation "B!"=> Set.range o☆
local notation "o*"=> trunkP H Y P' Y' V
local notation "D⁔"=> seatsV H Y P' Y' V G
noncomputable def reSeat (p':Warmlet H Y P' Y'→ℝ)(t: C₀):ℝ:= if h:t∈(B!) then p' (Classical.choose h) else 0
noncomputable def marsh (χ:Chi) (W:C₀→Prop):Gem c N C₀:=⟨D⁔,(muteK (crude (Z!) χ G) W).view⟩
variable (χ:Chi)(W':Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→Prop)
local notation "Q0"=> marsh H Y P' Y' V G χ W'
local notation "R0"=> reSeat H Y P' Y'
-- reach payments. x for Warmlet subset, rest small dated. generic boarding
variable (f₀:Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→ℝ) (g':Warmlet H Y P' Y' →ℝ)
lemma seatOne (x:A⁔): R0 g' (callV H Y P' Y' x)=g' x:=by
     let t:=callV H Y P' Y' x; have h:t∈(B!) := ⟨x,rfl⟩; exact (dif_pos h).trans (congr_arg _ (copyQ H Y P' Y' _ _ (Classical.choose_spec h)))
omit [Countable E][Countable J][Fintype D] in
lemma richZ (x:{x:C₀ // x∈(B!)}): o☆ (Classical.choose (show ∃ q,o☆ q=x.val from x.prop))=x.val:=Classical.choose_spec x.prop
lemma takes (hg:Valued (o*) v g' O.B u): Valued (D⁔) v (R0 g') O.B u:=by
   let A (x:{x:C₀// x∈ B!}): A⁔:= Classical.choose x.prop; have he x:o☆ (A x)=x.val:=richZ H Y P' Y' x
   refine wire (o*) (fun x=>x∈ B!) _ A (fun i j h=>Subtype.ext (((he i).symm.trans (congr_arg _ h)).trans (he j))) (D⁔) ?_ g' hg (fun _=>rfl)
   intro i; nth_rw 1 [← he i]; exact aisle H Y P' Y' V G _
variable (hG:∀ i,(G i).support=seatP (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).lightF i)
-- Dated complement outside ALL Warm. Licence at active. hℓ: complement mask cost.
local notation "k*"=> fun i: C₀=> if W' i ∧ i∉ (B!) then f₀ i else 0
include hG
lemma surround (_hv:0 ≤ v) (hp: ∀ i,Woven (G i).site (seatP (Z!).lightF i) O t ((crude (Z!) χ G).view i) (f₀ i)) (hK:Hit (seatP (Z!).lightF) O.B (k*) v r):Valued (D⁔) v (k*) O.B r:=by
     intro i; refine budget_mono (hK i) ?_ ?_
     · intro j; apply ite_nonneg _ le_rfl; exact mul_nonneg (ite_nonneg (hp _).travel le_rfl) (Real.exp_pos _).le
     intro j; by_cases hD: W' j ∧ j ∉ (B!); swap; · simp only [if_neg hD,zero_mul,ite_self,le_rfl]
     have hj:(D⁔) j=G j:= dif_neg hD.2; dsimp only; by_cases he:(D⁔ j).site=i
     · rw [if_pos he]; rw [hj] at he; rw [hj,if_pos (show i ∈ _ from hG j ▸ he ▸ (G j).anchor),hG j]; -- rfl
     rw [if_neg he]; exact (hK i).1 j
-- may need fix rw across split. Rate etc
lemma marshal (hv:0≤v)(hg: Valued (o*) v g' O.B u) (hp:∀ i,Woven (G i).site (seatP (Z!).lightF i) O t ((crude (Z!) χ G).view i) (f₀ i))(ht:∀ (i:A⁔), W' (o☆ i)→Woven (((o*) i).site) (((o*) i).support) O t ((crude (Z!) χ G).view (o☆ i)) (g' i))(hK:Hit (seatP (Z!).lightF) O.B (k*) v r):Licence O v (u+r) t (Q0):=by
   let k:= k*; let g i:= reSeat H Y P' Y' g' i; have hk:= surround H Y P' Y' V G χ W' f₀ hG hv hp hK; have h:=takes H Y P' Y' V G g' hg
   refine ⟨fun i=>g i+k i, advance (D⁔) _ _ h hk,?_⟩; intro i; change Woven (((D⁔) i).site) (((D⁔) i).support) O t ((muteK (crude (Z!) χ G) W').view i) (g i+k i); rw [eitherX]; split
   next he=> by_cases hi:i∈ (B!)
             · obtain ⟨j,rfl⟩:=hi; rw [aisle,show g _= _ from seatOne H Y P' Y' g' j,show k (o☆ j)=0 from if_neg (fun h=> h.2 ⟨j,rfl⟩),add_zero]; exact ht j he
             rw [show (D⁔) i=G i from dif_neg hi, show g i=0 from dif_neg hi, show k i=f₀ i from if_pos ⟨he,hi⟩,zero_add,hG]; exact hp _
   next he=> exact ((freeK _ _).stretches (Subset.refl _) (add_nonneg (vex _ _ h i) (vex _ _ hk i)))
end Warmlet
end YM.QCD.Shells
