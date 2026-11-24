import YM.QCD.Pant.Inlet
import YM.QCD.Fold.Cafe
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Coset
/-! # Transparent local filament. Prototype word for an exact period comparison. Forest, corrected slide choices and seam socks. No-limit letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory ProbabilityTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Coat Animals
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Loom Loom.Fleet
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Deck
open Further.PhysicalPeriodLimitF933 Macrame Stellar Mint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side}{N D:ℕ} {I J:Type}
variable {P: Teller su} {S: StepData c f} {R: Rep su f}{T:Tube su S}{κ W μ τ:ℝ}
variable {X : ConnectedActivityE6.Target su P} {o:ConnectedActivityE6.Target.Order su W}
variable (K: Cash W τ μ L X o κ T R)
open Fork Run Port Kit Gas GasP Ursell
-- ground independent revenues. triple order associate Jun via Varn⋆⊕Gaze
abbrev DarkV (c f:Side):= (Site f ⊕ Site c) ⊕ Site c
abbrev PeaceV (c f:Side):= Music c f ⊕ DarkV c f
abbrev BloomV (c f:Side) := Finset (PeaceV c f)
abbrev Wreath (c f:Side):= Clusters (BloomV c f)
def spinR (S: Ratio c f) : DarkV c f → Site c:= Sum.elim (Sum.elim S.parent id) id
def heartP (S:StepData c f): PeaceV c f → Site c:= Sum.elim (pace S) (spinR S.ratio)
def gradeV (T:PathData su) : PeaceV c f→ℕ:= Sum.elim (verse T) (fun _=>0)
-- inject code

def paste (c f:Side): Site f ⊕ Site c ↪ Varn f c:={toFun:=Sum.map (fun i=>(i,none)) (fun i=>(i,none)), inj':=by rintro (a|b) (c|d) <;> simp }
def washed (c f:Side): DarkV c f ↪ Varn f c⊕ Gaze c:={toFun:=Sum.map (paste c f) (fun i=>(i,none)), inj':=by rintro (a|b) (c|d)<;> simp}
def wades (S:StepData c f)(B:ℕ):DarkV c f→ Support c:=Sum.elim (fun i=> vap (paste c f i) S.ratio B) (fun i=> plank (sashP (i,none) B) S.ratio B)
local notation "B'"=> radiusB τ
def estateP:PeaceV c f→Support c:=Sum.elim (K.supportP ∘ (Mint.disc S)) (fun i=> halo (30*radiusB τ) (wades S (radiusB τ) i))
abbrev floorV (i: BloomV c f):= i.biUnion (estateP K)
abbrev summitV (i: Wreath c f):= unionOf (floorV K) i.2
-- heights requires distribution from h.root length
structure Fiat (p:BloomV c f):Prop where
 hot : Ac.Spark (estateP K) p
 sizes : p.card≤2
 earn i : i∈p → gradeV R.path i ≤radiusB τ
structure Mossy (p:Wreath c f):Prop where
 size : p.fst≤1
 each i : Fiat K (p.2 i)
 moves : coefficient (blocked (floorV K)) p.2 ≠0
-- cap geometry HEIR n needed .Meet. require ratio ≤B from room.
lemma centeredM (b:ℕ) (i: Site f ⊕ Site c)(s:Ratio c f):
   let r:=paste c f i; let p:=spinR s (.inl i); let X:=vap r s b; p∈ X∧ X⊆ neighbors (8*b+2) p :=by
   intro r p X
   have he:waxV r=none:=by cases i<;> rfl
   have hf:p=siteH r s:= by cases i with
                             | inl=> rfl
                             | inr i=> exact (s.embed_parent i).symm
   have hc:p∈X:= marks r s b (halo_subset _ _ (mem_singleton.mpr hf))
   refine ⟨hc,fun j hj=>?_⟩; obtain ⟨k,hk,hj⟩:=halo_spec.mp hj; obtain ⟨l,hl,rfl⟩:=mem_image.mp hk; apply (neighbors_mem ..).2; unfold payT at hl; rw [he] at hl; have hP:=Work.E04.parent_separation s (orbitM s r) l; have hZ:separation (orbitM s r) l≤ b:=(neighbors_mem ..).1 (show l∈neighbors b (orbitM s r) from hl); rw [hf]; unfold siteH; have h := separation_triangle (s.parent (orbitM s r)) (s.parent l) j; omega

def orbitD (m b:ℕ):ℕ:= Mint.width m b b+(48*b+10)
lemma centersP (i:PeaceV c f)(hp:gradeV R.path i ≤ B'):heartP S i∈ estateP K i ∧ estateP K i ⊆ neighbors (orbitD X.halo (B')) (heartP S i):=by
    rcases i with i|i
    · have h:= Mint.centered X.halo B' B' (lt_of_lt_of_le (by norm_num) K.laws.data.room.sight.1) i S T R hp; exact ⟨h.1,h.2.trans (Corona.halo_mono (Nat.le_add_right _ _) (Subset.refl _))⟩
    rcases i with i|i
    · obtain ⟨he,hg⟩:=centeredM B' i S.ratio; refine ⟨halo_subset _ _ he, fun j hj=>(neighbors_mem ..).2 ?_⟩; obtain ⟨k,hk,hj⟩:=halo_spec.mp (show j∈halo (30*radiusB τ) _ from hj); refine le_trans (separation_triangle _ k _) ?_; have he:= (neighbors_mem ..).1 (hg hk); change separation (spinR S.ratio (.inl i)) k + separation k j≤_; unfold orbitD; omega
    have ht:= K.laws.data.room.frame
    have hv: S.ratio.count.val +1≤ B':= by change _ ≤ radiusB τ at ht; change S.patch.L.val+1 ≤ radiusB τ; omega
    have hp := clover (i,none) B' S.ratio hv
    refine ⟨halo_subset _ _ (seaP (i,none) _ S.ratio (halo_subset _ _ (mem_singleton_self _))),fun z hz=>?_⟩
    have h:=hp hz; unfold Footprint.enlargement at h; rw [garrulous,image_id] at h; obtain ⟨x,hx,ht⟩:=halo_spec.mp h; have h1:separation i x≤ B':= (neighbors_mem ..).1 (show x∈neighbors (radiusB τ) i from hx); apply (neighbors_mem ..).2; have he:=separation_triangle i x z; change separation i z ≤ _; unfold orbitD; omega
lemma northG {z} (h:Fiat K z)(i) (hi:i∈ z): heartP S i∈floorV K z:=mem_biUnion.mpr ⟨_,hi,(centersP K i (h.earn i hi)).1⟩
lemma plowed {z} (h:Fiat K z): (floorV K z).Nonempty:=by obtain ⟨i,hi⟩:=h.hot.1; exact ⟨_, northG K h i hi⟩
local notation "τ'"=>orbitD X.halo B'
lemma kingly {z}(h:Fiat K z): coverNumber τ' (floorV K z) ≤2:=by
   refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi => ?_)).trans ?_)
   · let a:=heartP S i; refine (Corona.list_cost _ (show covers τ' (estateP K i) {a} from ⟨(centersP K i (h.earn i hi)).2, Corona.ship_halo _ (fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩)).trans_eq (card_singleton _)
   simpa using h.sizes
lemma royalty {z} (h:Mossy K z): coverNumber τ' (summitV K z) ≤4:=by
    let p:=floorV K
    let K₁ i : {p // Fiat K p}:=⟨z.2 i,h.each i⟩; let p₁ (i:{p // Fiat K p}):=p i.val
    have hr : coefficient (blocked p₁) K₁= coefficient (blocked p) z.2:= Meadow.movement _ _ _ _ (fun i j=>or_congr ⟨fun h=>congr_arg Subtype.val h, fun h=>Subtype.ext h⟩ Iff.rfl)
    have hf : ∀ i j,blocked p₁ i j → Ac.meets p₁ j (p₁ i):=by
      intro i j h; rcases h with rfl|h; rotate_left; · exact h
      obtain ⟨a,ha⟩:= plowed K i.2; exact ⟨a,ha,ha⟩
    have hx:=connected_pay (blocked p₁) p₁ τ' hf (m:=z.1) K₁ zero_le_one (hr.symm ▸ h.moves)
    unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have he i:(coverNumber τ' (p (z.2 i)):ℝ)≤ 2:=by exact_mod_cast kingly K (h.each i)
    have hh:(coverNumber τ' (summitV K z):ℝ)≤4:=by refine hx.trans ((sum_le_sum (fun i _=> he i)).trans ?_); rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; apply le_trans (mul_le_mul_of_nonneg_right (show ((z.fst+1:ℕ):ℝ)≤2 from by have hh:=h.size; exact_mod_cast (show z.fst+1≤2 by omega)) (by norm_num : (0:ℝ)≤ 2)); norm_num
    exact_mod_cast hh
abbrev tideP (m b:ℕ):=18*orbitD m b+8
lemma palace {z}(h:Mossy K z)(x)(hp:x∈ summitV K z): summitV K z ⊆ neighbors (tideP X.halo B') x:=by
   intro i hi; apply (neighbors_mem ..).2
   have he:=royalty K h; apply (Corona.extent _ τ' hp hi).trans; unfold tideP; exact (add_le_add_left (Nat.mul_le_mul_right _ he) (2*_)).trans_eq (by ring)
end YM.QCD.Moss
