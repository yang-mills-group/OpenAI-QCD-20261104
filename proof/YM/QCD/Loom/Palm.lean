import YM.QCD.Beam.Writer
/-! # vacuum shuttles transporting ster V-visible marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}

open scoped Classical
-- Patio FiniteDim instance
instance venue {A:Type*}[Fintype A] : FiniteDimensional ℝ (Patio A):=by
   let E : Grass.Alg A→ₗ[ℂ]Grass.Alg A:=LinearMap.id
   haveI : FiniteDimensional ℂ (Patio A) := FiniteDimensional.of_injective (light A).toLinearMap (fun _ _=>Subtype.ext)
   exact FiniteDimensional.trans ℝ ℂ _
-- Envelope of guarded by support parameters
structure Fleet (H:Cash W τ μ L Q o C T R)(ι:Type)(N:ℕ) where
 limit : ι→Finset ℕ
 ground : ι→Support c
 fine : ι→Support f
 window : ι→Support c
 compat : ι→ι→Prop
 works : ι→Grid f→Grid c→EvenA c N

namespace Fleet
variable (Y:Fleet H ι N)
def riseP (O:Coat T F)(z:Air f su)(i:ι):= O.enforce (2*o.a) (O.liftA R.beta z) (O.plaza (Y.window i))
def coming (i:ι)(O:Coat T F)(z:Air f su) := Y.riseP O z i • Y.works i (O.input (O.liftA R.beta z)) O.V
-- contours vanish outside h. i data fixed. require symmetry&anal later.
structure Famous :Prop where
 horizons i : (Y.fine i).image S.ratio.parent⊆ Y.window i
 boot i : halo (30*radiusB τ) (Y.window i) ⊆ Y.ground i
 locally i (V): LocalOn (Y.fine i) (fun U=> Y.works i U V)
 read i (U): LocalOn (Y.window i) (Y.works i U)
 pays i V: Envelope (fun U=> Y.works i U V)
 roots i V g : (∀ j:Site _,g (S.ratio.embed j)=1) → ∀ (U:Grid f), Y.works i (Lattice.gauge g U) V= Y.works i U V
 signs i j: ¬ Y.compat i j → ¬Disjoint (Y.ground i) (Y.ground j)
 issued i j: j∈Y.limit i → ∀ x, x∈(R.activities.forced j).support → S.ratio.parent x ∈Y.ground i
lemma supremumG (i:ι)(h:Y.Famous){X:Coat T F}(he:X.x=τ)(hp:X.width=o.K): Envelope (fun a:F.Slice su ×Air f su=> Y.coming i (X.wrapY a.1) a.2):=by
    let U z:F.Slice su × Air f su := z; let f' (j:F.Slice su ×Air f su) := (X.wrapY j.1).liftA R.beta j.2
    have hh : Measurable f':=(X.airwards (v:=Prod.snd) (by rw [he,hp]; exact H.laws.data.access) H.laws.intake.ready measurable_fst).2.2 R.beta measurable_snd
    have hu: Measurable (fun j:F.Slice su ×Air f su=> (X.wrapY j.1).input (f' j)):= X.summon measurable_fst hh
    let A (j:F.Slice su × Air f su) := Y.riseP (X.wrapY j.1) j.2 i
    have he: Envelope A := by
       refine ⟨(X.enforce_b (2*o.a) (X.plaza (Y.window i))).comp hh, 1,fun j=>?_⟩
       have hm : A j∈Set.Icc 0 1:= X.conserve (X.plaza (Y.window i)) (2*o.a) (f' j); exact (Real.norm_of_nonneg hm.1).trans_le hm.2
    exact Env.scale he (Env.along (h.pays i X.V) hu)
lemma buds (i:ι)(h:Y.Famous): silence H (Y.ground i) (Y.coming (F:=F) i):=by
   intro X Z v w he ht hp
   have hh:Borough X Z (Y.ground i) v w ∅ ∅ R:=⟨ht,(observe _).1 hp,fun _ _=>Iff.rfl⟩
   have hB: Room P S T X.x:= he.symm ▸ H.laws.data.room
   have he' x (hi:x∈Y.window i): Cleanroom (Y.ground i) (30*X.B) x:=fun y hy=>h.boot i (halo_spec.mpr ⟨_,hi,(show separation x y ≤30*radiusB τ from congrArg (fun b=>30*radiusB b) he ▸ hy)⟩)
   unfold coming riseP; rw [hh.enforces hB _ he']; congr 1
   rw [h.read i (X.input (X.liftA R.beta v)) X.V Z.V (agrees_mono ht.actual fun i hi=> ((halo_subset ..).trans (h.boot _)) hi)]
   exact h.locally i _ _ _ (fun p h₁ _=> hh.quarters hB (fun j hx=> he' _ (h.horizons i (mem_image_of_mem _ h₁)) j (hx.trans (mul_le_mul_of_nonneg_right (by omega) (Nat.zero_le _)))))
variable (F)
def suitcase : Pipe H F (EvenA c N) ι:= ⟨Y.ground,Y.limit,Y.compat,Y.coming,Y.works⟩
lemma forwarded (h:Y.Famous) : (Y.suitcase F).Viable:=by
   refine ⟨h.signs,h.issued,fun i O he hp _=> Y.supremumG i h he hp,fun i=> Y.buds i h,h.pays,h.roots,?_⟩
   intro X he hx hk i v p hv
   change X.enforce _ _ _ • _=_; rw [X.underfoot (a:=o.a) (mul_pos o.large (show 0<X.t from (he.symm ▸ H.laws.data.room).fiery)) hv,one_smul]; rfl
end Fleet
end YM.QCD.Loom
