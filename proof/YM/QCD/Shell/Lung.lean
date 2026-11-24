import YM.QCD.Shell.Cash
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
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {F':Cash W s μ L Q o C T (lore (trimP T R δ β B₀))}{N':Libretto su j}{D:Heir.Record}
-- Hue bridge ANY δ.Surface.Mat. No wind.G.In when bads.
variable {E J:Type}[Countable E][Countable J] {d':Ratio c f}
local notation "Y'"=> F'
variable (G₁:Rise f N E J)
structure Tone (Q₁:Send d' N (Tr f))(G₁:Rise f N E J)(i:Finset (Fj (Tr f) E J))(a:ι):Prop where
    born : S.ratio=d'
    light : Y.window a = (inspected (brimW Q₁ G₁ i)).image d'.parent
    wander : Y.ground a= i.biUnion (Jets.Touch.roof Q₁ G₁ 30 (radiusB s))
    ear : Y.fine a= inspected (brimW Q₁ G₁ i)
    cash : ∀ U V,Y.works a U V = hue Q₁ G₁ R.threshold i U
    stops : spent i=∅
--open Collide -- spark?
lemma gardens {E J θ:Type} [Countable E][Countable J] (H:Cash W s μ L Q o C T (trimP T R δ β B₀)) (Y:Send S.ratio N (Tr f))(p:Rise f N E J) (i: Wound (Jets.Touch.roof Y p 30 (radiusB s)))(V:Fleet H θ N)(he: spent i.val=∅): Tone (united (deckHue H Y p (Jets.Touch.roof Y p 30 (radiusB s))) V) Y p i.val (Sum.inl i) :=by
     refine ⟨rfl,rfl,rfl,rfl,fun U V'=> ?_,he⟩; change δ⁻¹^(budget p i.val) • _ =_; rw [budget,he,show p.wish ∅=∅ by simp [Rise.wish]]; simp
variable {a':ι}{i:Finset (Fj (Tr f) E J)}{Q₁:Send d' N (Tr f)} (h:Tone Y Q₁ G₁ i a')
variable {k':ℕ}(hX: ((lore (trimP T R δ β B₀)).activities.reg k').support=brimW Q₁ G₁ i)
include h hX
set_option linter.unusedSectionVars false in
lemma grill : Choker Y a' Y' k':=by
    have he:Y.ground a'=halo (30*radiusB s) (Y.window a'):=by
       rw [h.light,h.wander]; let r:= d'
       have hz:=h.born; subst d'
       apply Finset.ext; intro j; constructor
       · intro he
         obtain ⟨p,hp,hv⟩:= mem_biUnion.mp he; obtain ⟨x,hx,hX⟩:= halo_spec.mp hv; obtain ⟨y,hy,rfl⟩:=mem_image.mp hx; apply halo_spec.mpr; rw [montane]; exact ⟨_,mem_image_of_mem _ (mem_biUnion.mpr ⟨p,hp,hy⟩),hX⟩
       exact fun he=> planet Q₁ G₁ i he
    have hb:=h.born
    refine ⟨?_, h.ear.trans ?_,?_, fun U V W=> (h.cash ..).trans (h.cash ..).symm,?_⟩ -- edit
    · unfold baseRead; rw [h.light,hX,hb,enlargement,Nat.zero_mul]; refine Finset.Subset.antisymm (halo_subset ..) ?_; intro i hi; obtain ⟨j,hj,h⟩:= halo_spec.mp hi
      have hk: lift (j-i)=0:=by funext k; exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp ((component_le _ k).trans h))
      have he:j=i:= sub_eq_zero.mp (by rw [← wrap_lift (j-i),hk,map_zero]); exact he ▸ hj
    · rw [hX]
    · let X:=trimP T R δ β B₀; change _⊆ yFoot S ((lore X).activities.reg k').support s Q.halo; change ((lore X).activities.reg k').support=_ at hX; rw [he,h.light, yFoot,hX]; unfold enlargement; rw [hb]; exact Corona.halo_mono (Nat.mul_le_mul_right _ (by linarith [Q.buys])) (Subset.refl _)
    intro U hh; rw [hX] at hh; rw [h.cash,Spice.maskingW Q₁ G₁ i h.stops]; exact RG.masked_ne _ _ _ _ hh -- synt
-- geometric halo_eq lens extr
end YM.QCD.Shells
