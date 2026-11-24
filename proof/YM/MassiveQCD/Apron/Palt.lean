import YM.MassiveQCD.Apron.Color
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (R':Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "Gm"=> deckHue H G P₀ R'
local notation "M"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
variable [Fintype D][Countable E][Countable J]
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ R')
local notation "Ξ"=> closet H G R' X z a
local notation "Β"=>banknote N z' a
variable {p₁:E→ℝ}{p₂:J→ℝ}{m:D→ℝ}{r s u η h γ:ℝ}
variable (hh:X.Coins p₁ p₂ h O.threshold)(hc:Peak G O.threshold h a r m)(hδ:0<δ)
local notation "b!"=> mintD H G P₀ R' m p₁ p₂ r
include hw hh hc hδ
lemma votes (i:Wound R'): 0 ≤ mintD H G P₀ R' m p₁ p₂ r i:=(norm_nonneg _).trans (cap H G R' X z a hw hh hc hδ i 1 1)
lemma steals (A: Wound R'→Site c)(hη:0≤η)(k n:ℕ): (Ξ).Theft F A (mintD H G P₀ R' m p₁ p₂ r) a η ∅ k n:=by
    let K:= b!; have h i (u:Coat T F) x: ‖token c M a ((Ξ).coming i u x)‖≤ K i:= ((Ξ).riseTiny u x _ i a).trans (cap H G R' X z a hw hh hc hδ i _ _)
    let hz:= votes H G R' X z a hw hh hc hδ
    exact ⟨hη,hz,by simp,fun j X _ _ _ z hj=>False.elim ((not_lt.mpr (h j X z)) hj),fun i X _ _ _ z=> (h i X z).trans (le_mul_of_one_le_left (hz i) (Real.one_le_exp hη))⟩
lemma occupation (A x:ℝ)(ht:0≤x)(v:ℝ)(χ:Chi)(j:ℕ): King.Honest (Ξ) A 0 x (b!) a v χ j (fun _=>0) ∅ 0 0:=by
    let Y:= Ξ; let g:= b!; let K:= votes H G R' X z a hw hh hc hδ; refine ⟨K,le_rfl,ht,?_,by simp⟩
    intro T' W h hU hh' hg E _ _ _ y V z₀ hy hu i he Q₀; have hp: 0≤King.windy (Ξ) 0 i:=(zero_mul _).ge; have he: Brush j (g i) (King.windy Y 0 i) Q₀ y:= (Brush.certified hp (wearK c M a (Y.works i _ (V y)))).climb (cap H G R' X z a hw hh hc hδ i _ (V y)) le_rfl
    exact ⟨Or.inl he,he.climb (le_mul_of_one_le_left (K i) (Real.one_le_exp ht)) le_rfl⟩
include hk
lemma grounds (i:Wound R')(hi:b! i≠0): ((Ξ).ground i).Nonempty:=by
    have hξ: leftE i.1≠∅∨spent i.1≠∅:=by_contra (fun he=>hi (by unfold mintD Cove.jewel; rw [if_neg (fun h=>he h.2),mul_zero]))
    have hx j: (Cove.native G P₀ j).image S.ratio.parent⊆ R' j:= (Finset.image_subset_image (halo_subset ..)).trans (hk.budget _)
    rcases hξ with hi|hi
    · obtain ⟨j,h⟩:= Finset.nonempty_iff_ne_empty.mpr hi; let w:= (P₀.row j); refine Finset.Nonempty.mono ?_ (Finset.Nonempty.image (⟨_,w.anchor⟩: w.support.Nonempty) S.ratio.parent); exact (hx (.inr (.inl j))).trans (subset_biUnion_of_mem R' (mem_toRight.mp (mem_toLeft.mp h)))
    obtain ⟨j,h⟩:= Finset.nonempty_iff_ne_empty.mpr hi; let w:= P₀.front j; exact Finset.Nonempty.mono ((hx (.inr (.inr j))).trans (subset_biUnion_of_mem R' (mem_toRight.mp (mem_toRight.mp h)))) (Finset.Nonempty.image (w.alive.mono w.part) S.ratio.parent)
lemma certify (ha:1≤a)(hp:Ac.Hit (Gm).ground (radiusB τ) (mintD H G P₀ R' m p₁ p₂ r) s u)(hs:0 ≤ s): Summable (mintD H G P₀ R' m p₁ p₂ r) ∧ (∀ V:Grid c,((Ξ).suitcase F).solves V) ∧(Ξ).Feasible:=by
   have hv i U V:= (tore _ ha).trans (cap H G R' X z a hw hh hc hδ i U V); have hV:= grounds H G R' X z a hw hk hh hc hδ; have hsum:= fishes (Ξ).ground (b!) hp (votes H G R' X z a hw hh hc hδ) hs hV
   exact ⟨hsum,fun V=>⟨b!,hsum,fun i U=>hv i U V⟩,⟨fun i U V hx=>hV i ((norm_pos_iff.mpr hx).trans_le (hv i U V) |>.ne')⟩⟩
end YM.MassiveQCD.Apron
