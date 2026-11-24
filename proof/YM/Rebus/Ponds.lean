import YM.Rebus.Sands
import YM.Play.Dulce
/-!
 # cert read kernels charged. Once resident.S of X always see entire required cube. No chart from incidental flags. Uses threshold & flags equality internally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {N i j n k m l B Q: ℕ}
-- observed on globally scaled coupling
noncomputable abbrev karm (κ:ℝ)(U:Grid c)(i:Kh c):ℝ := κ⁻¹ * Hypnos.marrow U (Fruit.bleep i) i.2.2
-- choose κ later. Enough only values. Alias supports.
variable (p:I→Site f)(q:I→Bool)(T:Finset (Finset I))
set_option quotPrecheck false
section
variable (Z:Rise f N E J) (A: Stitch.Tablet Z I)(Y:Finset E)
def glen (U:Grid f)(X: Finset I): Patio (Dh f N I):=∑ i∈Y with A.spine i=X,A.main i U
structure Vitae (T:Finset (Finset I))(r t κ A₀ :ℝ) (Q l:ℕ)(fP:Quince f N I) : Prop where
    shape i:i∈Y→ (A.spine i).Nonempty ∧ ∀ j∈ A.spine i,(Z.row i).support⊆ halo (majorT l*Q) {p j}
    accuracy i : i∈T→i.Nonempty→ ∀ (U : Directions su f), ‖U‖≤ r→Healthy t (Cape.cups p (innerT l*Q) i) (increment 1 U) → ‖glen Z A Y (increment 1 U) i-Oce.rose (Dh f N I) (karm κ (increment 1 U)) (fP i)‖ ≤ A₀
end
variable (R:Ratio c f)
local notation "Vh"=> R.parent ∘ p
-- ANY progress
variable (fP:Quince f N I)
private lemma faradayP {A B :Type}[Fintype A][Fintype B]{V W:A→ℝ}{P:Papers A (Patio B)}{S:Finset A}(hp:P∈Bera.Camp S n)(hw:∀ i∈S,V i=W i): Oce.rose B V P=Oce.rose B W P:=by
    let v:= ‖V‖+‖W‖+1
    have hv:1 ≤ v:= le_add_of_nonneg_left (add_nonneg (norm_nonneg V) (norm_nonneg W)); have hz (i):‖V i‖ ≤ v:= le_trans (norm_le_pi_norm ..) (by unfold v; linarith [norm_nonneg W]); have hW(i): ‖W i‖ ≤ v:= le_trans (norm_le_pi_norm ..) (by unfold v; linarith [norm_nonneg V]); have hf:= Bera.Oce.tang V W P hp (show Oce.bill V S v from fun i hi=>hz _) (fun i _=>hW _) hv (fun i hi=> (show ‖V i-W i‖ ≤ 0 from by rw [hw _ hi,sub_self,norm_zero])) le_rfl
    simp only [mul_zero, zero_mul] at hf; exact sub_eq_zero.mp (norm_le_zero_iff.mp hf)
local notation "X0"=> Dh f N I
local notation "Ax"=> spineP p N (majorT l*Q)
local notation "Aw"=> can p (majorT l*Q)
def shock (A:Finset I)(p:I→Finset ι): Finset ι:=@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) A p
-- local restore. TRUE gauge derivatives via scaled
open Bera.Oce
local notation "V!" V=> heather Vh B V
variable (Z:Rise f N E J) (A: Stitch.Tablet Z I)(Y:Finset E) (V:Finset I)(t κ':ℝ)
variable (hP:SetL p T Q l k m fP)(hQ:Q≤2*B)(hL:20*majorT l≤ R.count.val)(hB:0<B)
include hP hQ hL hB
lemma scaledK {U U':Grid f}(hi:V∈T)(hv:V.Nonempty)(X: Finset I)(h:∀ i:Bond f,R.parent i.1∈heather (R.parent∘p) B X→ U i=U' i)(he:V⊆X): Oce.rose X0 (karm κ' U) (fP V)=Oce.rose X0 (karm κ' U') (fP V):=by
     have hp:=hP.scope V hi hv; apply faradayP hp.2 -- inspect
     intro i hj; have hx:=gaugeFt R p hQ hL hB V i hj
     have he': (V! V) ⊆ (V! X):= Corona.halo_mono le_rfl (image_subset_image he); have hf: faceValue U (bleep i)= faceValue U' (bleep i):=by
        apply travel_local; intro e hi _; exact h e (he' (hx (mem_image_of_mem _ (List.mem_toFinset.mpr hi))))
     unfold karm marrow; rw [hf]
variable {r A₀:ℝ}(hX: Vitae p Z A Y T r t κ' A₀ Q l fP)
include hX
open Apron Apron.Grove Stitch
variable (O : BudgetPoint)(hx:t=O.threshold) (hh:A.Wave t q p)
include hx hh
lemma awoken (X:Grid f)(u:Directions su f) (S':Finset I)(hi:V∈T)(hv:V.Nonempty)(hp:V⊆ S')(hr:‖u‖ ≤ r)(h:∀ i:Bond f,R.parent i.1∈heather (R.parent∘p) B S'→ X i=increment 1 u i)(hZ:Healthy t (Cape.cups p (majorT l*Q) S') X): ‖puddle A Y X V (O:=O) - Oce.rose X0 (karm κ' X) (fP V)‖ ≤ A₀:=by
     let U:= increment 1 u
     have hg : Healthy t (Cape.cups p (majorT l*Q) S') U:=by
        unfold Healthy; rwa [Finset.disjoint_iff_inter_eq_empty, ← flags_agree _ _ _ _ (inspectPath R p hQ hL hB (Finset.Subset.refl (Cape.cups p (majorT l*Q) S')) _ _ h),← Finset.disjoint_iff_inter_eq_empty] --
     rw [scaledK p T R fP V κ' hP hQ hL hB hi hv S' h hp] -- order
     have hxP :puddle A Y X V (O:=O)=glen Z A Y U V:=by
        refine sum_congr rfl fun i hi=>?_ ; obtain ⟨hi,hv'⟩:=mem_filter.mp hi
        obtain ⟨j,hj⟩:=hv; have he': (Z.row i).support ⊆ Cape.cups p (majorT l*Q) S' := (hX.shape i hi|>.2 j (hv'.symm ▸ hj)).trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem _ (hp hj))))
        unfold Tablet.read; rw [←hx,masked_eq _ _ _ _ (Disjoint.mono_left he' hZ)]; exact hh.use i _ _ (agrees_mono (inspectPath R p hQ hL hB he' X U h) (fun i hi=>Finset.mem_union_left _ hi))
     rw [hxP]; apply hX.accuracy V hi hv u hr; exact Disjoint.mono_left (Corona.halo_mono (Nat.mul_le_mul_right _ (show innerT l ≤ majorT l from by unfold majorT Cape.orbital; omega)) (image_subset_image hp)) hg
omit hQ hL hB hx hP
variable (ht:∀ i∈Y,∀ x: Grid f,A.read t x i∈ Bera.vaultS univ ((A.spine i).card*m))
local notation "VA"=>shock V (Ax)
include ht hx
lemma wakesN (x: Grid f): parties (puddle (O:=O) A Y x) V∈vaultS (shock V Ax) (V.card*m):=by
    apply Chamber.censusD; intro v hv hN; refine Submodule.sum_mem _ fun i hi=> ?_; obtain ⟨hi,hξ⟩:=mem_filter.mp hi; obtain ⟨hf,hg⟩:=A.lights_read hh x i; have hy: (A.read t x i).val∈ Anomaly.Rim _ _:= Play.Chamber.parcelR q _ hf hg (ht i hi x) -- syntax
    change A.read O.threshold x i ∈ _; rw [← hx,← hξ]; apply (Anomaly.Rim.monotone (show (limits (F:=N) (Z.row i).support).disjSum (Ribbon.burst q (A.spine i))⊆ VA from ?_) le_rfl hy)
    rintro (i'|j) hj
    · obtain ⟨b,hb⟩:=hN; refine biDU.mpr ⟨_,hv hb,inl_mem_disjSum.mpr (mem_filter.mpr ⟨mem_univ _,(hX.shape i hi).2 _ (hξ.symm ▸ hb) (mem_filter.mp (inl_mem_disjSum.mp hj)).2⟩)⟩
    exact biDU.mpr ⟨_,hv (hξ ▸ Ribbon.located q _ j (inr_mem_disjSum.mp hj)), inr_mem_disjSum.mpr (mem_filter.mpr ⟨mem_univ _,rfl⟩)⟩
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.awoken
#print axioms YM.MassiveQCD.Rebus.wakesN
