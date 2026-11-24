import YM.QCD.Purse.Table
/-!
 # All regular input labels appear in the real integral on the marked trajectory.
 Costs are per-portal; doesn't allow cutting a power or inserting a comparison
 label only at identity. `promotion_equi` identifies. Also authorize small whenever
 needed on those on-sites. -/
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
private lemma mother {z:ℕ} : Matter.troupe T (trimP T R δ β B₀) z n (∅:Molecule S)∧ (Matter.roster (∅:Molecule S)).flags=∅∧ Matter.own (∅:Molecule S)=∅:=by -- z undefined
   let p:Molecule S:=∅
   have h₀ : roster p = bareStores S:=by unfold roster; congr! 1
   have he : Matter.own p=∅:=by unfold Matter.own; ext; simp [p]
   have ht : Layout (roster p) z n p.toLeft:=by
     refine ⟨?_,?_,Packets.seeds_store ..⟩
     · simp [p]
     rw [show p.toLeft= ∅ from by ext; simp [p]]; simp
   refine ⟨⟨ht,?_,?_⟩,h₀.symm ▸ rfl,he⟩
   · change Contract.sealed _ (own p); rw [he]; simp [Contract.sealed]
   change Contract.incidence _ (own p) _; simp [he,Contract.incidence]
local notation "X!"=> roof P' Y' 30 ζ
lemma attendance (p:E) : ∃ x:Duke H Y P' Y', col H Y P' Y' x=p:=by
    let t:=ζ; let Pq:= trimP T R δ β B₀; let s': Fj D E J:= Sum.inr (Sum.inl p); let b : K₀ := ⟨{s'},?scorch⟩ -- edit
    case scorch => refine ⟨singleton_nonempty _,fun i hi j hj=>?_⟩; rw [mem_singleton.mp hi, mem_singleton.mp hj]; exact Relation.ReflTransGen.refl
    let r: K₀ ⊕ ι:= Sum.inl b; let Z:=united (Y!) Y; let Fq:=Z.shellF
    let W:QCD.Beam.Pipe.Clump S ((K₀)⊕ι):={Sum.inr r}
    have hh:W.toLeft=∅:=by ext; simp [W]; -- line
    have ht:W.toRight={r}:=by ext; simp [W]
    obtain ⟨hb₁,hb₂,hb⟩:= mother (T:=T) (R:=R) (δ:=δ) (β:=β) (B₀:=B₀) (n:=radiusB s) (z:=Q.halo)
    have hr':Fq.born W:=by
        unfold QCD.Beam.Pipe.born; rw [hh,ht]; refine ⟨hb₁,by simp [QCD.Beam.Pipe.eligibleP],?_⟩; rw [QCD.Beam.Pipe.filterP,singleton_biUnion, hb]; change ∅= typo (Y'.wish (spent b.val)); ext; simp [spent,b,s',Rise.wish,typo]
    have hW: Z.fullA W =(X!) s':=by
       unfold W Fleet.fullA; rw [Finset.singleton_biUnion]; change Finset.biUnion {s'} (X!)=_; rw [Finset.singleton_biUnion]
    let o:=(Y'.row p).site; have hA:S.ratio.parent o∈ Z.fullA W:=by
       rw [hW]; unfold roof; -- inspect
       apply halo_subset; exact mem_image_of_mem _ (mem_union_left _ (show o∈ brim P' Y' s' from halo_subset _ _ (Y'.row p).anchor))
    have hx: Z.Given W:= ⟨⟨_,hA⟩,⟨singleton_nonempty _,fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj]; exact Relation.ReflTransGen.refl⟩, hr'⟩
    let v : Z.Bright:= ⟨W,hx,hh.symm ▸ hb₂⟩
    let X: A⁔:=⟨b,v,rfl⟩
    let A': Duke H Y P' Y':= ⟨X,p,rfl⟩; refine ⟨A',?_⟩
    have hp: s'=Sum.inr (Sum.inl (col H Y P' Y' A')) := Finset.singleton_injective (duke H Y P' Y' A'); exact (Sum.inl.inj (Sum.inr.inj hp)).symm
lemma promotion_equi : Bijective (col H Y P' Y'):= ⟨copyL H Y P' Y',attendance H Y P' Y'⟩
-- install cover and plenitude prices after L. No expanding volume used as the delay.
abbrev HaloGate (i:ℕ)(L:Side) (x:ℝ) : Prop:= preCost i + 10*preCost i / L.val*1 ≤ radiusB x ∧ (9^4)^3 < L.val
lemma HaloGate.budget {i r : ℕ}(hp:HaloGate i L s)(h:r≤1): preCost i + 10*preCost i / L.val*r ≤ radiusB s:=by
   apply le_trans _ hp.1; gcongr
   · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
   exact_mod_cast h
set_option maxHeartbeats 600000 in
lemma tight_reach (p:Duke H Y P' Y')(F:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) (hs:HaloGate (Q.halo+8) L s) (hB:R.B ≤ 2*ζ)(hM:P'.trim≤ζ)(hL:P'.trim+1 ≤ R.B+R.B)(hz:0<ζ)(hp:coverNumber R.B (Y'.row (col H Y P' Y' p)).support ≤ 1): Small H Y P' Y' p.val F ∧ coverNumber R.B (brimW P' Y' p.val.label.val) ≤ 9^4 ∧ Heir.Short S R (brimW P' Y' p.val.label.val):=by
   have hd:S.ratio.count=L:=H.laws.data.funds.length_eq; have he:S.patch.L=L:=H.laws.data.funds.length_eq
   have hf:= terrestrial H Y P' Y' F p hM hB hz
   have hg: coverNumber R.B (brimW P' Y' p.val.label.val) ≤ 9^4:=by have hx:=sizeP H Y P' Y' p hL; omega
   refine ⟨?_,hg,?_⟩
   · change coverNumber ζ _ ≤ζ
     apply Nat.cast_le (α:=ℝ)|>.1
     apply hf.trans; unfold conversion; rw [hd]; exact hs.budget hp
   unfold Heir.Short; rw [he]; exact lt_of_le_of_lt (Nat.pow_le_pow_left hg _) hs.2
end Warmlet
end YM.QCD.Shells
