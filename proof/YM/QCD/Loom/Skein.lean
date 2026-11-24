import YM.QCD.Loom.Issue
/-! # Quiet across adaptive enforce molecules. same-gauge blanket S.parent and no need V closed globally. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}
variable {H:Cash W τ μ L Q o C T R}{ι D E K:Type}{N:ℕ}
local notation "M"=> radiusB τ
structure Woods (P:Teller su) (L:Side) (a:ℝ)(X:ℝ→ℝ) (x:ℝ):Prop where
 frames : 0 ≤ X x
 cloth :∀ {c f:Side}{S:StepData c f}{T:Tube su S}{p:Tree.Forest S.ratio}(Z:Coat T p),Z.x=x→ S.patch.L=L→ Room P S T x→Z.manifest →∀ (V:Support c)(i:Site c) (w:Directions su f),halo (6*radiusB x) {i}⊆V→ Z.enforce (2*a) w (Z.plaza V)≠0 →¬Inside i Z.seeds (18*radiusB x) →∃ g b, Blanket S (Z.input w) Z.V i (4*radiusB x) g b (X x)
lemma hammock (P:Teller su)(L:Side)(a:ℝ)(ha:0<a):∃ X, Rate su L (-(1/2)) X ∧ ∀ᶠ x in atTop, Woods P L a X x:=by
   let f x:=2*(2*a)*fiery su x L; have he: Rate su L (-(1/2)) f:=Rate.flame.mul_left _
   have hF x:0≤f x:=mul_nonneg (by positivity) (temp_nonneg _)
   obtain ⟨w,h,hp⟩:= layered P L he (Eventually.of_forall hF)
   refine ⟨w,h,?_⟩; filter_upwards [hp] with x hp
   refine ⟨(hF x).trans hp.1, fun {c f' S T p} Z hX hL hh hm V i u hv hn hx=>hp.2 _ _ _ _ hL hh _ _ _ _ (by omega) ?_ (Z.signal u) ?_⟩
   · have hz:= hh.sight.1
     subst x
     have hF:= clean_far Z.seeds Z.V hm hx
     exact hF.shrink (v:=i) (by rw [separation_self]; omega) -- inspect hx type
   subst x
   have he:0<Z.t := hh.fiery
   have hg : 100≤ radiusB Z.x := hh.sight.1
   have h j (h:separation i j ≤ 4*radiusB Z.x): Grafted Z.V (Z.input u) (Z.signal u) j Z.B (f Z.x) S :=by
     refine Z.distant u j (hF Z.x) (clear hx (u:=11*Z.B+1) (show _ from ?_)) (fun p hp hP=>?_)
     · dsimp only [Coat.B]; omega
     have ht : p∈ Z.plaza V:= mem_filter.mpr ⟨mem_univ _,hP,Finset.not_disjoint_iff.mpr ⟨_,hv (halo_spec.mpr ⟨_,mem_singleton_self _, (separation_triangle ..).trans (show separation i j + separation j (atEdge S p) ≤_ from ?_)⟩),center_end p⟩⟩
     · apply (Z.protection V (a:=2*a) (by positivity) u hn p ht).trans_eq; unfold f Coat.t; rw [hL]
     change separation j (atEdge S p) ≤ radiusB Z.x at hp; omega
   refine ⟨fun j hj=> (h _ hj).read j (by rw [separation_self]; omega), fun j hj=> (h _ hj).norm j (by unfold distAt; rw [separation_self]; omega)⟩
lemma weir (Y:Coat T F)(w: Directions su f)(i:Site f)(p: Site c→ su.El)(b: LogField su c){a d:ℝ}(hB:100≤ M)(ha:0≤a)(hd:0≤d)(v:∀ x:su.El,Fork.colorLen (colour x-1) ≤d * su.chord x) (hx: Blanket S (Y.input w) Y.V (S.ratio.parent i) (4*M) p b a) :
   ‖Kit.settled (Fork.rider (gauge (constantGauge p S.ratio) (Y.input w)) M i)-Kit.settled 1‖ ≤ d*a:= Fork.renting _ i _ M (mul_nonneg hd ha) (fun k h=> (v _).trans (mul_le_mul_of_nonneg_left (hx.fine k ((Work.E04.parent_separation S.ratio _ _).trans (by omega))) hd))
end YM.QCD.Loom
