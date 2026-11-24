import YM.Mural.Drum
import YM.MassiveQCD.Apron.Harvest
/-! # the interior heft. Local laws require gauge-root agency, not full color. -/
set_option autoImplicit false
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
open Sway OrbitG Ribbon QCD.Mural
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
variable {q':I→Bool}(hw:X.Flora O.threshold q' z)(hk:Cove.Count G P₀ R')
local notation "Ξ"=> closet H G R' X z a
local notation "Β"=>banknote N z' a
variable {p₁:E→ℝ}{p₂:J→ℝ}{m:D→ℝ}{r s u η h γ x:ℝ}{w n:ℕ}
variable (hh: Firm n X x p₁ p₂ h O.threshold)(hc:Peak G O.threshold h a r m)(hδ:0<δ)(hr:1 ≤ x)(hu:∀ U:Grid f,∀ s:Finset (Fj D E J),Mild (Tablet.tunnel G s U))
local notation "b!"=> mintD H G P₀ R' m p₁ p₂ r
local notation "u!"=> family c N I
include hw hh hc hδ hr hu
lemma mink (i:Wound R')(U:Grid f)(V:Grid c): ‖paidM u! x n a ((Ξ).works i U V)‖≤ b! i:=by
    let p := X.hue t G i.1 U; let y:= X.markers i.1; have hp:Polite q' y p:= by
       unfold p Stitch.Tablet.hue; split; · exact politeStep _ (X.lights_col G hw _ U).1 rfl
       exact polite_nil ..
    change ‖paidM u! x n a (δ⁻¹ ^ budget P₀ i.1 • Β p)‖ ≤ _; rw [map_smul,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ δ⁻¹ ^ budget P₀ i.1)]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [Mural.payment]; exact (pennedM c N I z' a x n hc.cup p hp).trans_le (new_wage n X G x _ _ _ hc hu hw hh hr i.val U i.property)
lemma polling (A: Wound R'→ Site c)(hp:0≤η)(k j:ℕ) : Vigil (Ξ) u! F A (mintD H G P₀ R' m p₁ p₂ r) x n a η ∅ k j:=by
    let A₁:=Ξ; let Z:=paidM u! x n a; let f:=b!
    have h i (u:Coat T F) z: ‖Z (A₁.coming i u z)‖≤ f i:=by
        have hr:=Z.map_smul (A₁.riseP u z i); unfold Fleet.coming; rw [hr,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_of_nonneg (u.conserve ..).1).trans_le (u.conserve ..).2)); exact mink H G R' X _ _ hw hh hc hδ ‹_› hu i _ _
    have he i:0 ≤ f i:=(norm_nonneg _).trans (mink H G R' X z a hw hh hc hδ hr hu i 1 1)
    exact ⟨hp,he,by simp,fun j X _ _ _ z hj=> False.elim ((not_lt.mpr (h j X z)) hj),fun i X _ _ _ z=> (h i X z).trans (le_mul_of_one_le_left (he i) (Real.one_le_exp hp))⟩
omit hw hh hc hδ hr hu
include hk
lemma north (i:Wound R')(hi:b! i≠0): ((Ξ).ground i).Nonempty:=by
    have hξ: leftE i.1≠∅∨spent i.1≠∅:=by_contra (fun he=>hi (by unfold mintD Cove.jewel; rw [if_neg (fun h=>he h.2),mul_zero]))
    have hx j: (Cove.native G P₀ j).image S.ratio.parent⊆ R' j:= (Finset.image_subset_image (halo_subset ..)).trans (hk.budget _)
    rcases hξ with hi|hi
    · obtain ⟨j,h⟩:= Finset.nonempty_iff_ne_empty.mpr hi; let w:= (P₀.row j); refine Finset.Nonempty.mono ?_ (Finset.Nonempty.image (⟨_,w.anchor⟩: w.support.Nonempty) S.ratio.parent); exact (hx (.inr (.inl j))).trans (subset_biUnion_of_mem R' (mem_toRight.mp (mem_toLeft.mp h)))
    obtain ⟨j,h⟩:= Finset.nonempty_iff_ne_empty.mpr hi; let w:= P₀.front j; exact Finset.Nonempty.mono ((hx (.inr (.inr j))).trans (subset_biUnion_of_mem R' (mem_toRight.mp (mem_toRight.mp h)))) (Finset.Nonempty.image (w.alive.mono w.part) S.ratio.parent)
include hδ hc hh hu hw hr
lemma certPort (ha:1≤a)(hp:Ac.Hit (Gm).ground (radiusB τ) (mintD H G P₀ R' m p₁ p₂ r) s u)(hs:0 ≤ s): Summable (mintD H G P₀ R' m p₁ p₂ r) ∧ (∀ V:Grid c,((Ξ).suitcase F).solves V) ∧(Ξ).Feasible:=by
   have hv i U V:= (tore _ ha).trans ((Mural.light_minor _ hc.cup hr _).trans (mink H G R' X z a hw hh hc hδ hr hu i U V)); have hV:= north H G R' X z a hk (p₂:=p₂) (p₁:=p₁) (m:=m) (r:=r); have hsum:= fishes (Ξ).ground (b!) hp (fun i=> (norm_nonneg _).trans (hv i 1 1)) hs hV
   exact ⟨hsum,fun V=>⟨b!,hsum,fun i U=>hv i U V⟩,⟨fun i U V hx=>hV i ((norm_pos_iff.mpr hx).trans_le (hv i U V) |>.ne')⟩⟩
omit hk
lemma ensembleF (hp:(Gm).Famous)(ha:1≤a)(he:∀ U g, (∀ i,g (S.ratio.embed i)=1) →∀ i:Wound R', X.hue t G i.val (gauge g U)= X.hue t G i.val U): (Ξ).Famous:=by
    refine ⟨hp.horizons,hp.boot,?_,fun _ _ _ _ _=>rfl,?_,?_,hp.signs,hp.issued⟩
    · intro i V U Y hv; let p:=i.1; let ψ x:= δ⁻¹^budget P₀ p • Β x; exact congr_arg ψ (RG.UsesFinal.allReads O.threshold _ _ (X.ears2 G hw p) U Y hv)
    · intro i V; have hP (i:Wound R'):Measurable fun U=>Β (X.hue t G i.val U):= ((Β).toLinearMap.continuous_of_finiteDimensional.measurable).comp (X.glory2 G hw _)
      refine ⟨measurable_const.smul (hP _),mintD H G P₀ R' m p₁ p₂ r i,fun u=> (tore _ ha).trans ((Mural.light_minor _ hc.cup hr _).trans (mink H G R' X z a hw hh hc hδ hr hu i u V))⟩
    intro i V g hr U; change _ • Β (X.hue ..)= _ • Β _; rw [he U g hr i]
omit hh hc hu hr hδ
lemma factorsA : (Ξ).speaking:=by
   have hΦ i:Measurable (fun U=>Β (X.hue t G i U)):= ((Β).toLinearMap.continuous_of_finiteDimensional.measurable).comp (X.glory2 G hw _)
   exact fun i=>(measurable_const.smul (hΦ i.1)).comp measurable_fst
include hk
lemma residentF : (Ξ).gator:=by
    intro i U V; apply mixT; change pen N z' a (X.hue t G i.1 U).val ∈_; obtain ⟨hp,hZ⟩:=X.lights_field G hw hk _ U
    have he:=hp.exact; rw [← he]; apply Ribbon.entitled; · exact hZ _
    intro j hj; exact X.endowment2 G hw hk _ (mem_image_of_mem _ (Ribbon.located q' _ _ hj))
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.mink
#print axioms YM.MassiveQCD.Apron.certPort
