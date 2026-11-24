import YM.QCD.Shell.Ethos
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
-- Hue bridge ANY δ.Surface.Mat. No wind.G.In when bads.
variable {E J:Type}[Countable E][Countable J] {d':Ratio c f}
variable (G₁:Rise f N E J)
open Flume YM.Next.Free Stew Leaf Jets.Touch Jets.Sun -- inspect
variable {d₂ D' K:ℕ}{z:Support f}{x:ℝ}
lemma miles (X:Support f)(b B:ℕ)(h:0<B)(hs:b ≤ B+B): coverNumber B (halo b X) ≤ coverNumber B X * (4+4+1)^4 :=by
   obtain ⟨D,hx,hD⟩:= coverNumber_realized B X
   rw [← hD]; apply tiling (m:=3) h
   have hz := halo_ship _ hx.2; refine ⟨fun i hi=>?_,ship_halo _ ?_⟩
   · obtain ⟨x,h,h'⟩:= halo_spec.mp hi; obtain ⟨p,h,w⟩:=halo_spec.mp (hx.1 h); exact halo_spec.mpr ⟨p,h,(separation_triangle ..).trans ((Nat.add_le_add w h').trans (by omega))⟩
   intro i hi j hj; refine Relation.ReflTransGen.mono ?_ i j (hz i hi j hj)
   intro x y h; exact ⟨h.1,h.2.1,by have := h.2.2; omega⟩
-- arbitrary enlargement halo. Old external. For mask support.E all.
lemma touring (X:Support f)(m b B:ℕ)(h:0<B)(hs:b ≤ m*B): coverNumber B (halo b X) ≤ coverNumber B X * (((m+1)+1)+((m+1)+1)+1)^4 :=by
   obtain ⟨D,hx,hD⟩:= coverNumber_realized B X
   rw [← hD]; apply tiling (m:=m+1) h
   have hz := halo_ship _ hx.2; refine ⟨fun i hi=>?_,ship_halo _ ?_⟩
   · obtain ⟨x,h,h'⟩:= halo_spec.mp hi; obtain ⟨p,h,w⟩:=halo_spec.mp (hx.1 h); exact halo_spec.mpr ⟨p,h,(separation_triangle ..).trans ((Nat.add_le_add w h').trans (by rw [Nat.add_mul]; omega))⟩
   intro i hi j hj; refine Relation.ReflTransGen.mono ?_ i j (hz i hi j hj)
   intro x y h; refine ⟨h.1,h.2.1,?_⟩; rw [Nat.add_mul]; have := h.2.2; omega
lemma spreadCo (f c:Side)(d': Ratio c f)(i j:Site f): separation i j ≤ d'.count.val*(separation (d'.parent i) (d'.parent j)+2):=by
    have hp: separation (d'.embed (d'.parent i)) (d'.embed (d'.parent j)) ≤ d'.count.val*separation (d'.parent i) (d'.parent j):= scaled_root ..
    have hx:= Corona.near d' i; have he:= Corona.near d' j; refine (separation_triangle i (d'.embed (d'.parent i)) j).trans ?_; have hg:=separation_triangle (d'.embed (d'.parent i)) (d'.embed (d'.parent j)) j; rw [separation_comm (d'.embed (d'.parent j))] at hg; rw [Nat.mul_add]; omega
noncomputable def paceD (L:Side)(s:ℝ):ℕ:= L.val*(Malachite.radiusD s +2)
abbrev deckP (L:Side)(s:ℝ):ℕ:=(2*paceD L s+1)^4
open Dust
lemma treasure (X:Support f)(L:Ratio c f)(d:ℕ)(p:Support c)(x:Site f)(ho:x∈X)(he:X.image L.parent ⊆ p)(hp: coverNumber (radiusB s) p ≤ radiusB s)(hD:0<d): X.card ≤ deckP L.count s ∧ coverNumber d X ≤ deckP L.count s :=by
    let b:= radiusB s
    have ht(y)(hy:y∈p): separation (L.parent x) y ≤ Malachite.radiusD s:= (Corona.extent p (radiusB s) (he (mem_image_of_mem _ ho)) hy).trans (by unfold Malachite.radiusD; gcongr)
    let r:=paceD L.count s; have hh:X⊆ halo r {x}:= fun i hi=> halo_spec.mpr ⟨x,mem_singleton_self _,(spreadCo f c L x i).trans (Nat.mul_le_mul_left _ (by have hz:=ht _ (he (mem_image_of_mem _ hi)); omega))⟩
    refine ⟨(card_le_card hh).trans ((Corona.halo_size {x} r).trans (by simp [deckP,two_mul,r])),?_⟩
    apply le_trans (Corona.cover_mono (Subset.trans hh (Corona.halo_mono (Nat.le_mul_of_pos_right r hD) (Subset.refl _))) d); simpa [deckP,r,two_mul] using Corona.tile x r d hD
-- hooks count for swipe.B ≤ pre poly volume*flavors via L parent embed INJ
lemma flavorZ (P:Ratio c f)(p:Support f): (hooks (F:=N) P p).card ≤ 2*(2*p.card * Fintype.card Fiber * N):=by
    let X:= limits (F:=N) p; let d: Support c:= p.image P.parent; let Y:= limits (F:=N) d
    have hx:X.card=2*p.card*Fintype.card Fiber*N:=limits_card _
    have ht:(Y.map (hb c f N)).card ≤ X.card:=by
       rw [card_map,hx]; unfold Y; rw [limits_card]; gcongr; exact card_image_le
    have hh:hooks (F:=N) P p⊆ X.map (ha _ _ _)∪ Y.map (hb _ _ _):=by
       intro i hi; rw [hooked] at hi; rcases Creek.splits_index i with ⟨a,rfl⟩|⟨a,rfl⟩
       · change jointP P (ha c f N a)∈_ at hi; rw [rootA] at hi; exact mem_union_left _ (mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _,hi⟩))
       change jointP P (hb c f N a)∈_ at hi; rw [rootB] at hi; exact mem_union_right _ (mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨_,hi, P.embed_parent _⟩⟩))
    apply (card_le_card hh).trans ((card_union_le ..).trans (by rw [← hx,two_mul]; exact Nat.add_le_add (Finset.card_map ..|>.le) ht))
variable {g:Cove.Send d' N (Tr f)}{i:Finset (Fj (Tr f) E J)}{u':ι}{F':Cash W s μ L Q o C T (lore (trimP T R δ β B₀))}
variable (h:Tone Y g G₁ i u')(k:ℕ)(hz:((lore (trimP T R δ β B₀)).activities.reg k).support= brimW g G₁ i)
local notation "X'"=>brimW g G₁ i
local notation "K₁"=> Brim.plate F' k
include h hz
noncomputable def geoQ (L:Side)(s:ℝ)(N:ℕ):ℕ:=2*(2*deckP L s* Fintype.card Fiber*N)
lemma detailed (he:coverNumber (radiusB s) (K₁).support ≤ radiusB s) : coverNumber R.B (brimW g G₁ i) ≤ deckP L s ∧ (hooks (F:=N) d' (coreW g G₁ i)).card ≤ geoQ L s N:=by
    let k':=(lore (trimP T R δ β B₀)).activities.reg k; have hz': k'.support=X':=hz
    have hu : (X').image d'.parent ⊆ (K₁).support:=by
       have hk:(RG.inspected (X')).image d'.parent= Y.window u':=h.light.symm
       have hf:= grill Y G₁ h hz (F':=F'); apply Subset.trans (image_subset_image (Finset.subset_union_left (s₂:=_) : X'⊆ RG.inspected (X'))) ?_ ; change (RG.inspected (X')).image _⊆_; rw [hk]
       change _⊆ yFoot S _ _ _; rw [h.light,yFoot,hz,Footprint.enlargement,h.born]; exact halo_subset .. -- actually image(inspected). need
    have hP:=treasure X' d' R.B (K₁).support _ (hz' ▸ k'.anchor) hu he R.B_pos
    rw [show d'.count = L from (congr_arg Ratio.count h.born).symm.trans H.laws.data.funds.length_eq] at hP
    have hx:= (card_le_card (native_sub g G₁ i)).trans hP.1
    refine ⟨hP.2,?_⟩; apply (flavorZ d' (coreW g G₁ i)).trans; unfold geoQ; gcongr
end YM.QCD.Shells
