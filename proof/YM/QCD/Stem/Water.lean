import YM.QCD.Stem.Lyon
/-! # Actual bios. Outside old generation on Station. Costs independent tags conditional Pose. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open QCD Lat PhysicalNext.Repeat
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace PhysicalNext.Repeat.Greenbelt
variable {c f C F L₀ : Side} {P : Patch} {M D' n: ℕ} {K : Teller su}
variable {p a b W U V t d r g : ℝ}
open Loom Fleet Patron Cove GasP Grove Stew King
local notation "B'"=> radiusB p
open QCD.Beam QCD.Port
variable {S:StepData c f}{R:BudgetPoint}{T:Tube su S} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}{β δ:ℝ}{D: Cash W p a L₀ X o U T (trimP T R δ β b)}
variable {I:Type}{N:ℕ}
open Blaze King Silica Patron Sands Leaf Tee Orbit Garden Jets Flume Run YM.Next.Free
variable {B:Fleet D I N}{u v:ℕ}{O:Flight u v}{h:f.val=c.val*O.L.val}{A J μ γ C':ℝ}{π : St f}{U₀:ℕ→Atom su 2} {P':Plan v}
variable {L: Swathe O h π U₀ P' A J μ γ C' M}{Γ:Land c (Site c) (Site c)}
set_option quotPrecheck false
local notation "G"=>tiro B L Γ
local notation "S₀"=>artV B L Γ
variable {A₀:Clusters (S₀).Bright →RegularAddress c}{V₀:Chi}
local notation "T₀"=> crude (S₀) V₀ A₀
lemma rider {Z:Fleet D I N}{A:Clusters Z.Bright→RegularAddress c}(q:Z.Bright)(j:I)(he: j∈ q.val.toRight)(hZ:∀ U V,Z.works j U V=0): (crude Z V₀ A).view (individual q)=0:=by
    have hh(F: Tree.Forest S.ratio)(T₁:Coat T F): Z.bandL q.val T₁=0:=by
       have hv (p:Coat T F) z: Z.muscle j p z=0:=by unfold muscle; dsimp only; rw [show ∀ U V,Z.works j U V=0 from fun U V=>hZ U V]; exact smul_zero _
       unfold bandL; split
       next h=> simp only [choiceS,lows,regards, show ∀ (i:Coat T F) y, ∏ x∈q.val.toRight,Z.muscle x i y=0 from fun i y=> prod_eq_zero he (hv i y),smul_zero,integral_zero,sum_const_zero]
       next h=> exact rfl
    have hV V:Z.furnace V₀ V (individual q)=0:=by rw [carrying Z]; unfold brisk; simp only [choiceS,hh, sum_const_zero,smul_zero]
    funext U; change Patron.pepper (fun V=> Z.furnace V₀ V (individual q)) U=0; simp only [Patron.pepper,hV,map_zero,integral_zero]
open Cove.Send -- maybe Cove.Send
variable {V':Send S.ratio N I}{M': Cove.Fj I Empty Empty→Support c}
-- needs fintype I
lemma gadget [Fintype I] (i : Loom.Wound M') (U:Grid f)(V:Grid c): (deckHue D V' (Coda.virginR f N) M').works i U V=0:=by
    let P:= Coda.virginR f N; have h : Cove.hue V' P R.threshold i.val U=0:= nightly _ _ _ i.property.1 (Subsingleton.elim _ _) (Subsingleton.elim _ _) U
    change _ • hue V' P _ _ _=0; rw [h,smul_zero]
end YM.QCD.Moss
#print axioms YM.QCD.Moss.rider
