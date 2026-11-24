import YM.Massive.Struck.Sail
import YM.Massive.Lens.Width
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y: Code c N) -- independent shape
set_option quotPrecheck false
namespace Carrier
variable {b:Flavor N}(φ:ℝ) (z s:ℂ)
-- predicates with no instance dependency.The mass root (K.N any). Each setter.§
def maidenTag (p:EIndex Y):Prop:= ∃ x: (Site c × Flavor N) × Tw,p= Sum.inr (Sum.inl x)
def hoeTag (p:EIndex Y):Prop:= ∃ x:Y.A × Tw, p= Sum.inr (Sum.inr (Sum.inl x))
def hayTag (p:EIndex Y):Prop:= ∃ x: Y.B × Tw,p= Sum.inr (Sum.inr (Sum.inr x))
def meadow (p:EIndex Y):Prop:= maidenTag Y p ∨ hoeTag Y p ∨ hayTag Y p
noncomputable def spring (x:Site c × Flavor N) : EIndex Y:= Sum.inr (Sum.inl (x,[]))
lemma spring_inj : Function.Injective (spring Y):=fun _ _ he=>congr_arg Prod.fst (Sum.inl_injective (Sum.inr_injective he))
lemma maiden_spring (x): maidenTag Y (spring Y x):=⟨_,rfl⟩
lemma pod_first (x) : turf Y (spring Y x)=pegE:= one_smul ℕ _
lemma reachP (p:EIndex Y)(he:(turf Y p).1≠0): meadow Y p:=by
    rcases p with i|i|i|i; exact (he rfl).elim; exact Or.inl ⟨_,rfl⟩; exact Or.inr (Or.inl ⟨_,rfl⟩); exact Or.inr (Or.inr ⟨_,rfl⟩)
lemma twoP (n p:ℕ)(hp:2 ≤ p)(he:1 ≤ n):2 ≤ (n • knot p).1:=le_trans hp (Nat.le_mul_of_pos_left _ he)
lemma lowP (hp:∀ i,2≤ Y.ad i)(p:EIndex Y)(he:(turf Y p).1=1): p∈Set.range (spring Y) ∨ hoeTag Y p:=by
    obtain h|h|h:= reachP Y p (by rw [he]; decide)
    · obtain ⟨⟨⟨x,i⟩,l⟩,rfl⟩:=h; left
      cases l with
      | nil=> exact ⟨(x,i),rfl⟩
      | cons a l=> change (digit (a::l) • pegE).1=1 at he; change digit (a::l)*1=1 at he; have hp:=digit_grew a l; omega
    · exact Or.inr h
    obtain ⟨x,rfl⟩:=h; exact (Nat.not_succ_le_self 1 (le_of_le_of_eq (twoP (digit x.2) (Y.ad x.1) (hp x.1) (digit_pos _)) he)).elim
-- tag control of prices
lemma limitAny (G:Gem c N I)(f:I→ℝ)(g:ℝ) (hp:Valued G.addr (1/8) f n g): Valued G.addr (1/16) f n g := by
    intro i; apply budget_mono (hp i)
    · intro j; dsimp only; split; exact mul_nonneg (vex _ _ hp j) (Real.exp_pos _).le; exact le_rfl
    intro j; dsimp only; split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num: (1/16:ℝ)≤1/8) (Nat.cast_nonneg _))) (vex _ _ hp j); exact le_rfl
local notation "q¹"=> (1/8:ℝ)
local notation "q⁺"=> (1/16:ℝ)
-- to avoid ite restructuring costs using valued across labels via function ext and Sum.elim S.Edge. membership defined constants
abbrev strike (W:ℝ) (X:I→Prop) (f:I→ℝ)(i:I):= if X i then W*f i else 0
-- simpler mechanical `extensions`: Valued via Eq sum. helper boot. use injection.
lemma coverPrice (L:Side)(tag:I→Bool)(G:Gem c N I)(X:Gem c N Ω)(E:Ω ↪ I)(hp:∀ i,G.addr (E i)=X.addr i)(V:I→Prop)(he:∀ i,V i ↔ i∈Set.range E)(f:I→ℝ)(b:Bool)(hY:∀ i,tag (E i)=b)
 (p:Ω→ℝ)(hQ: Valued X.addr q p n x)(hS:∀ i,f (E i)=p i) : Valued G.addr q (fun i=> if V i then inflate3 L tag f i else 0) n ((if b then (L.val:ℝ) else (L.val:ℝ)^2)*x):=by
    have hf(x:{i// V i}): ∃ i, E i=x.val:= (he x.val).mp x.property; choose a ha using hf; let r:ℝ:=if b then L.val else (L.val:ℝ)^2
    have hV(i): inflate3 L tag f (E i) = r*p i:=by unfold inflate3; rw [hY,hS]
    have hl:0≤r:=by unfold r; split <;> positivity
    refine wire _ V _ a (fun i j h=> Subtype.ext ((ha i).symm.trans ((congr_arg _ h).trans (ha j)))) _ (fun i=>?_ ) (fun i=>r*p i) (valued_mult _ _ hQ hl) (fun i=> ?_)
    · rw [← hp, ha]
    by_cases h: V i
    · rw [if_pos h,dif_pos h]; let Q:{i//V i}:=⟨i,h⟩; let x:=a Q; exact ((congr_arg (inflate3 L tag f) (ha Q)).symm.trans (hV x))
    rw [if_neg h,dif_neg h]

lemma pricedOr (X:I→RegularAddress c)(p:I→ℝ)(hp:0≤ p)(A B:I→Prop)(hA:Valued X v (fun i=> if A i then p i else 0) n a) (hB: Valued X v (fun i=> if B i then p i else 0) n t): Valued X v (fun i=>@ite ℝ (A i ∨ B i) (Classical.propDecidable _) (p i) 0) n (a+t):=by
    refine valued_trim X _ _ (fun i=>by dsimp only; split; exact hp i; exact le_rfl) ?_ (valued_sum X _ _ hA hB); intro i; rw [Pi.add_apply]; dsimp only
    by_cases hx:A i <;> by_cases hy:B i <;> simp [hx,hy]; exact hp i
lemma perri (hp:modulus P p r) (f:Y.master.ι→ℝ)(g:Site c×Flavor N→ℝ)(t:Y.A→ℝ)(k:Y.B→ℝ)(hz:SeatsE φ Y P L x ρ q¹ r p b f g t k)(hs:1 ≤ fan L ρ x):
   let V (i:EIndex Y):= inflate3 L (kind Y) (rings Y f g t k P) i; let A:=(Mast Y φ).row; let v:=(L.val:ℝ); let μ:=snack P r; let y:=snack P p
   (∀ i,0≤ rings Y f g t k P i) ∧ Valued A q⁺ (fun i=>if maidenTag Y i then V i else 0) P.B (v^2*μ) ∧ Valued A q⁺ (fun i=>if hoeTag Y i then V i else 0) P.B (v*y) ∧ Valued A q⁺ (fun i=>if meadow Y i then V i else 0) P.B (v^2*μ+(v*y+v^2*y)) :=by
   intro V A v μ y; let X(i):= rings Y f g t k P i; let G:=PackageE Y φ 1 1
   have hX:0≤ X:=vex G.addr X (sails Y φ 1 1 f g t k hz hp (by simp) (by simp) (by norm_num) hs).1; have hv:0≤ V:=fun i=> inflate_nil _ _ _ i (hX i)
   have hη:= hp _ (Or.inl (le_refl p)); have hθ:= hp _ (Or.inr (le_refl r))
   have pB0: Valued A q⁺ (fun i=>if maidenTag Y i then V i else 0) P.B (v^2*μ):=by
       let p':=rent Y φ 1 1; let E:((Site c × Flavor N) × Tw) ↪ EIndex Y := ⟨Sum.inr ∘ Sum.inl,Sum.inr_injective.comp (Sum.inl_injective)⟩; have ht : LowFare p' P q¹ (fan L ρ x) μ (logBudget P g):= flute _ 1 1 _ g (by simp) (by simp) (hz.rent) (by norm_num) hs hθ.1 hθ.2 -- args order
       refine limitAny G _ _ (coverPrice L (kind Y) G p' E (fun _=>rfl) _ (fun i=> ?_) X false (fun _=>rfl) (logBudget P g) ht.1 (fun _=>rfl)); exact exists_congr fun i=> Eq.comm
   have pB1: Valued A q⁺ (fun i=>if hoeTag Y i then V i else 0) P.B (v*y):=by
       let p':=louvre Y φ 1 1; let E:(Y.A × Tw) ↪ EIndex Y := ⟨Sum.inr ∘ Sum.inr ∘ Sum.inl,Sum.inr_injective.comp (Sum.inr_injective.comp (Sum.inl_injective))⟩; have ht : LowFare p' P q¹ (fan L ρ x) y (logBudget P t):= flute _ 1 1 _ t (by simp) (by simp) (hz.cool) (by norm_num) hs hη.1 hη.2 -- args order
       refine limitAny G _ _ (coverPrice L (kind Y) G p' E (fun _=>rfl) _ (fun i=> ?_) X true (fun _=>rfl) (logBudget P t) ht.1 (fun _=>rfl)); exact exists_congr fun i=> Eq.comm
   have pB2: Valued A q⁺ (fun i=>if hayTag Y i then V i else 0) P.B (v^2*y):=by
       let p':=heights Y φ 1 1; let E:(Y.B × Tw) ↪ EIndex Y := ⟨Sum.inr ∘ Sum.inr ∘ Sum.inr,Sum.inr_injective.comp (Sum.inr_injective.comp (Sum.inr_injective))⟩; have ht : LowFare p' P q¹ (fan L ρ x) y (logBudget P k):= flute _ 1 1 _ k (by simp) (by simp) (hz.heat) (by norm_num) hs hη.1 hη.2 -- args order
       refine limitAny G _ _ (coverPrice L (kind Y) G p' E (fun _=>rfl) _ (fun i=> ?_) X false (fun _=>rfl) (logBudget P k) ht.1 (fun _=>rfl)); exact exists_congr fun i=> Eq.comm
   refine ⟨hX,pB0,pB1,?_⟩; have h:= pricedOr A V hv (maidenTag Y) (fun i=>hoeTag Y i∨hayTag Y i) pB0 (pricedOr A V hv _ _ pB1 pB2)
   exact h

end Carrier
end Library
end YM.QCD.Struck
