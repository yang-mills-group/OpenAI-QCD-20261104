import YM.QCD.Purse.Older
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
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
variable (i:K₀)
abbrev perms {N:Type*}(i:N):= individual i
structure Warmlet where
    label : Wound (roof P' Y' 30 (radiusB s))
    code : (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright
    earns : Aliased (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y) code (.inl label)
variable (p: Warmlet H Y P' Y') -- order? inspect compile
namespace Warmlet
lemma stop (p: Warmlet H Y P' Y'): spent p.label.val=∅:=by
    let b:=p.code; let H':=(Z!).shellF; have he:b.val={Sum.inr (Sum.inl p.label)}:=p.earns
    have ht: own b.val.toLeft= H'.filterP b.val.toRight:= b.property.1.2.2.2.2
    have hp:Y'.wish (spent p.label.val)=∅:=by
       rw [he,show Finset.toLeft ({Sum.inr (Sum.inl p.label)} : Pipe.Clump S (K₀ ⊕ ι)) = ∅ from ?_,show Finset.toRight ({Sum.inr (Sum.inl p.label)}: Pipe.Clump S (K₀ ⊕ ι)) ={Sum.inl p.label} from ?_, Pipe.filterP,singleton_biUnion] at ht; rotate_left
       · apply Finset.ext; intro i; simp
       · apply Finset.ext; intro i; simp
       have he: own (∅ : Molecule S)=∅:=by unfold own; apply Finset.ext; intro i; simp -- signatures
       rw [he] at ht; change ∅=typo _ at ht; exact Finset.image_eq_empty.mp ht.symm
    apply not_nonempty_iff_eq_empty.mp; intro hc; obtain ⟨t,ht⟩:=hc; exact (Finset.not_nonempty_empty) (hp ▸ (show Finset.Nonempty (Y'.wish (spent p.label.val)) from ((Y'.front t).alive.mono (subset_biUnion_of_mem (fun i=> (Y'.front i).inv) ht)))) -- congr
abbrev Ticket (p: Warmlet H Y P' Y'): Finset (Fj D E J):=p.label.val
abbrev Leaf (p:Warmlet H Y P' Y'):Support f := brimW P' Y' p.label.val
abbrev past (p:Warmlet H Y P' Y') :Support c:= (Z!).ground (.inl p.label)
lemma old_eq (p: Warmlet H Y P' Y'): past H Y P' Y' p = p.label.val.biUnion (roof P' Y' 30 (radiusB s)):= rfl -- order.
lemma brink (i:Finset (Fj D E J))(m:ℕ): Footprint.enlargement S.ratio m (radiusB s) (inspected (brimW P' Y' i))= i.biUnion (roof P' Y' m (radiusB s)):=by
    rw [montane]; unfold Footprint.enlargement; apply Finset.ext; intro x; constructor
    · intro hx; obtain ⟨y,h,hx⟩:=halo_spec.mp hx; obtain ⟨j,hb,rfl⟩:=mem_image.mp h; obtain ⟨a,ha,h⟩:=mem_biUnion.mp hb; exact mem_biUnion.mpr ⟨a,ha,halo_spec.mpr ⟨_,mem_image_of_mem _ h,hx⟩⟩
    intro hx; obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hx; obtain ⟨i,h,hx⟩:=halo_spec.mp hx; obtain ⟨j,hb,rfl⟩:=mem_image.mp h; exact halo_spec.mpr ⟨_,mem_image_of_mem _ (mem_biUnion.mpr ⟨a,ha,hb⟩),hx⟩
lemma stretchP (p: Warmlet H Y P' Y') : let m:= Q.halo; p.label.val.biUnion (roof P' Y' m (radiusB s))⊆ halo (m*ζ) (p.label.val.biUnion (roof P' Y' 30 (radiusB s))):=by
    intro m; rw [← brink,← brink]; exact Corona.halo_mono le_rfl (halo_subset ..)
lemma iden (p q:Warmlet H Y P' Y')(hp: p.label.val=q.label.val):p=q:=by
    rcases p with ⟨p,X,h⟩; rcases q with ⟨q,Y',h'⟩; have hx:p=q:=Subtype.ext hp; subst q; have hY:X=Y':=Subtype.ext (h.trans h'.symm); subst Y'; rfl
lemma copyQ (p q: Warmlet H Y P' Y')(hp: individual p.code=individual q.code): p=q:=by
    let V (p: Clusters (Z!).Bright):= p.2 none; have he : p.code=q.code:=congr_arg V hp
    have hQ:{Sum.inr (Sum.inl p.label)}=({Sum.inr (Sum.inl q.label)}: Pipe.Clump S (_⊕_)):= (p.earns.symm.trans (congr_arg Subtype.val he)).trans q.earns
    exact iden H Y P' Y' p q (congr_arg Subtype.val (by simpa using hQ))
lemma threshold (p: Warmlet H Y P' Y'): Finset.Nonempty (Leaf H Y P' Y' p):=by
    have hp := p.code.property.1.1
    have he:= (cottage _ _ _ p.earns).2; rw [he] at hp; change (p.label.val.biUnion (roof P' Y' 30 (radiusB s))).Nonempty at hp
    rw [← brink] at hp
    by_contra! hv; have hh : brimW P' Y' p.label.val=∅:=hv; rw [hh,show RG.inspected (∅:Support f)=∅ from ?_] at hp; swap
    · apply Finset.ext; intro i; simp [RG.inspected]
    obtain ⟨x,hx⟩:=hp; obtain ⟨p,hp,hx⟩:=halo_spec.mp hx; simp at hp
-- choose base f. In any Hue local dictionary with exactly 1 E must anchor. otherwise default. Need sup ⊆.
variable (p: Warmlet H Y P' Y')
lemma harbour (i:E)(hp:leftE p.label.val={i}): (Y'.row i).support ⊆ brimW P' Y' p.label.val:=by
    intro x hx; have hm : (Sum.inr (Sum.inl i))∈p.label.val:=mem_toRight.mp (mem_toLeft.mp (show i∈leftE p.label.val from hp.symm ▸ mem_singleton_self i)); apply subset_biUnion_of_mem _ hm; exact halo_subset _ _ hx
lemma oak : ∃ i:ℕ,((lore (trimP T R δ β B₀)).activities.reg i).support=brimW P' Y' p.label.val ∧ (∀ a:E,leftE p.label.val={a} → ((lore (trimP T R δ β B₀)).activities.reg i).site=(Y'.row a).site) ∧ S.ratio.parent ((lore (trimP T R δ β B₀)).activities.reg i).site∈ past H Y P' Y' p:=by
    let A i:=((lore (trimP T R δ β B₀)).activities.reg i); let Z:=brimW P' Y' p.label.val
    have he :∃ i: Site f,i∈ Z∧∀ a:E,leftE p.label.val={a}→i=(Y'.row a).site :=by
       by_cases ht:∃ a:E,leftE p.label.val={a}; · obtain ⟨a,h⟩:=ht; exact ⟨_,harbour H Y P' Y' p a h (Y'.row a).anchor,fun b hv=> (Finset.singleton_injective (h.symm.trans hv)) ▸ rfl⟩
       obtain ⟨x,hx⟩:= threshold H Y P' Y' p; exact ⟨_,hx,fun a he=> False.elim (ht ⟨a,he⟩)⟩
    obtain ⟨x,hx,hh⟩:=he; let R': RegularAddress f:=⟨x,Z,hx⟩; let v:=leafCode R'; have hp:= labelR R' (trimP T R δ β B₀); have hR:(A v).site=x:= congr_arg RegularAddress.site hp
    refine ⟨v, congr_arg RegularAddress.support hp,fun a he=> hR.trans (hh a he),?_⟩
    change S.ratio.parent (A v).site ∈ _; rw [hR,old_eq, ← brink]; exact halo_subset _ _ (mem_image_of_mem _ (mem_union_left _ hx))
end Warmlet
end YM.QCD.Shells
