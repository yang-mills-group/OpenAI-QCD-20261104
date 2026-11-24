import YM.TIPS.Humbug
import YM.TIPS.Tap
import YM.TIPS.Tight
import YM.TIPS.Units
import YM.Differ.Treasures
import YM.TIPS.Tip
import YM.Oars.PursePages
import YM.Cape.Fuel
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D U :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Taxing
open QCD.Ruby Cove Cape SC
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j N:ℕ}
variable (p:I→Site c)(q:I→Bool)
open Stitch Cape
-- mask restore.V need roof empty proof from accordance.Ap document. implement.
noncomputable def faux (N:ℕ)(c:Side)(I:Type)[Fintype I]: Film c N I Empty:=⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim⟩
local notation "X✱"=>faux N c I
lemma vacPay :Film.Beat N p q X✱ t ∧ Film.Stock N X✱ k v α t 0 (fun _=>1):=by
    refine ⟨⟨fun i=>Empty.elim i,fun i=>Empty.elim i,fun i=>Empty.elim i,fun i=>Empty.elim i,fun i=>Empty.elim i,fun i=>Empty.elim i,fun i=>Empty.elim i⟩,fun i=>Empty.elim i,fun i=>Empty.elim i,fun q=>⟨fun i=>Empty.elim i,Summable.of_finite,tsum_empty.le⟩⟩
variable (M: Patron.Rail c N U)
lemma verdict (V:Grid c)(h:Summable fun i=>‖M.warp i V‖): Film.reports N (faux N c I) M t V=rootR (Spine I) (Keys c N) (heartK M t V):=by
    let g:=fun i=> Film.spruced N X✱ M i V; let F:=rootR (Spine I) (Keys c N); have hg:Summable (fun i=>‖g i‖):= Summable.sum _ (Film.payable F.toLinearMap.toContinuousLinearMap h) (show Summable fun i=> ‖(X✱).mark i V‖ from Summable.of_finite); let D:= flags t V; let u i:=M.warp i V
    unfold Film.reports heartK; simp_rw [termsK]; rw [Film.stamps _ _ _ F h]; change (∑' i,Plate.roof _ g D i)=(∑' i,Plate.roof M.addr (F ∘ u) D i); rw [catalogue M.addr (F ∘ u) D (Film.payable F.toLinearMap.toContinuousLinearMap h),show (∑' i,Plate.roof _ g D i)= _ from catalogue (Film.addressSets N X✱ M) g D hg]; apply congr_arg (fun f:Hat c→ Tine c N I=> ∑' i, Plate.roof id f D i); funext i; refine (Film.coin_merge (M.addr) (faux N c I).addr (F ∘ u) (fun j=> (X✱).mark j V) (Film.payable F.toLinearMap.toContinuousLinearMap h) Summable.of_finite i).trans ?_; rw [fingerprint (faux N c I).addr,tsum_empty,add_zero] -- inspect
-- booking minimal geometry.
variable (Q:Finset (Finset I))(P:BudgetPoint)
noncomputable def comet (i:I): RegularAddress c:=⟨p i,Lattice.halo (majorT l*P.B) {p i}, halo_subset _ _ (mem_singleton_self _)⟩
variable (l m:ℕ)(F:I→ Grid c→ Lat.Fields c 6)(hF:∀ (i:I)(V:Grid c),Grass.Hom (q i) (F i V))
open Stags
set_option quotPrecheck false
noncomputable def shipY (l:ℕ): Reel c 6 I I:= ⟨comet p P (l:=l),fun i=> {i},fun i U=>⟨stake (Keys c 6) (burst q {i}) (F i U),even_stake (burst q {i}) (F i U) ((Ribbon.flavor q i).symm ▸ hF i U)⟩⟩
local notation "K✱"=> Keys c 6
local notation "T!"=> shipY p q P F hF l
lemma kinetic (i:I)(V:Grid c): Polite q {i} ((T!).mark i V):=⟨_,rfl⟩
lemma valueS (i:I)(V:Grid c): pluck K✱ (burst q {i}) ((T!).mark i V)=F i V:=quid ..
local notation "o" i:arg=> Lattice.halo (innerT l *P.B) {p i}
variable (hZ:∀ i,LocalOn (Lattice.halo (innerT l*P.B) {p i}) (F i)) (hf:∀ i V,F i V∈ region (limits ((comet p P (l:=l) i).support)))(hN:∀ i,Measurable (F i)) (ht:∀ i V g, Lat.slots 6 g (F i (Lattice.gauge g V))= F i V)
include hZ
lemma here (i:I): LocalOn (o i) ((T!).mark i):=fun U V he=>Subtype.ext (congr_arg (stake K✱ _) (hZ i U V he))
include hf hN ht
lemma booked : Reel.Book p q T!:=by
    refine ⟨fun _=> singleton_nonempty _,fun i=>?_,fun i=> ((stake K✱ (burst q {i})).measurable.comp (hN i)).subtype_mk,?_, fun i V=>?_, fun i V g=>?_⟩
    · change ({i}:Finset I).image p⊆ _; rw [image_singleton]; exact singleton_subset_iff.mpr ((comet p P (l:=l) i).anchor)
    · intro i U V h; apply here p q P l F hF hZ i; exact agrees_mono h (coe_subset.mpr (Corona.halo_mono (show innerT l*P.B ≤ majorT l*P.B from Nat.mul_le_mul_right _ (by unfold majorT Cape.orbital; omega)) (Finset.Subset.refl _)))
    · exact ⟨kinetic p q P l F hF i V, Ribbon.clad.gates _ (hf i V) _⟩
    · have hp:= vault 6 q {i} _ g (kinetic p q P l F hF i (Lattice.gauge g V)); apply pluckVisible; intro j; by_cases he:j=burst q {i}
      · rw [he,partColor,valueS,valueS,ht]
      exact (hp.spectral _ he).trans ((kinetic p q P l F hF i V).spectral _ he).symm
omit hf hN ht
open QCD.Anomaly
lemma vessel (hT: ∀ i,{i}∈Q)(he:∀ i V, ((T!).mark i V).val∈ Rim Finset.univ m): Vault p T! Q univ P.B l m:=by
    refine ⟨?_,fun i _=> ?_,fun i _ j hj=> ?_,fun i _ j hj=> ?_,fun i _ j hj=>?_ ,fun i _ V=>?_⟩
    · intro i _ j _ he; exact singleton_injective he
    · exact ⟨hT i,singleton_nonempty _,fun a ha b hb=> (((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm) ▸ Relation.ReflTransGen.refl) ⟩ -- match.m
    · rw [show j=i from mem_singleton.mp hj]; exact Finset.Subset.refl _
    · rw [show j=i from mem_singleton.mp hj]; apply Corona.halo_mono _ (Finset.Subset.refl _); unfold majorT Cape.orbital refuge innerT; nlinarith [P.B_pos]
    · rw [show j=i from mem_singleton.mp hj]; exact here p q P l F hF hZ _
    · rw [show (T!).z i={i} from rfl,card_singleton, one_mul]; exact he _ _
end Taxing
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Taxing.verdict
#print axioms YM.MassiveQCD.Sample.Taxing.vessel
#print axioms YM.MassiveQCD.Sample.Taxing.booked
