import YM.Oars.Canyon
import YM.Oars.FicusL
/-! # Revenue bundle.Sizes output from each k to all compatibles by Fleet.X.Ed -/
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
variable {c f:Side}{η M t t' μ θ :ℝ}{I E J :Type}[Fintype I]
variable (q:I→Bool)(X:Reel c 6 I E)(Taper:Massive.SourceRead.TaperHol) {U: YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(i:I)(k:Cover)(P:BudgetPoint){d n Dx nL r:ℕ}
local notation "Sp"=>LoomT.Single X i
local notation "K"=> Keys c 6
set_option quotPrecheck false
local notation "o"=>wrap c k
variable (p:Label d)
-- reputation.E.L uses Film too
structure Gel (u v V W:ℝ)(Dx nL r:ℕ):Prop where
   support : ∃ (S:Sp→Support c)(z:Sp→Label d), (∀ i:Sp, (X.addr i.val).support ⊆ S i) ∧ (∀ i, Carte.Hem.pot (r+1) c k ⊆ S i) ∧ (∀ i, Beacon.ActionTest Taper k (Reel.speaker q X i.val) (z i).val) ∧ Summable z ∧ (∑' i,z i)=p ∧ (∃ (f:Sp→ℝ), (∀ i:Sp, Flame (Reel.speaker q X i.val) P (S i) o u Dx nL (f i)) ∧ Ac.Hit S P.B f v V) ∧ ∃ (g:Sp→ℝ),(∀ i, Sight (X.addr i.val).support o 2 P u (Reel.speaker q X i.val) (g i)) ∧ Ac.Hit S P.B g v W -- beware Z phantom
variable (x:I→Site c)(he:X.Book x q)
-- motion payout.Foot o can vary
-- Life from Book cost.Round primitive shift pickup
variable (R:Type)(e:R→LoomT.Single X i) (Yt:Site c)(hY:∀ a, Yt∈ (X.addr (e a).val).support)
noncomputable def tender : Puff c 6 R (q i) where
    addr j:=⟨Yt,(X.addr (e j).val).support,hY j⟩
    fill j:=Reel.speaker q X (e j).val
    beams j V:=by unfold Reel.speaker; rw [(e j).property]; have hv:Hom (shade (burst q {i})) (pluck K (burst q {i}) (X.mark (e j).val V)):= serene _ (bright _); exact Ribbon.flavor q i ▸ hv
local notation "N"=>tender q X i R e Yt hY
include he
lemma tended : Puff.Seal 6 Yt N:=by
    refine ⟨fun _=>rfl,fun i x y e0=> congr_arg (pluck K _) (he.room _ x y e0),fun i=> (pluck K _).measurable.comp (he.permit _),fun i p k=>?_,fun i V=> (he.stage (e i).val V).2 _⟩
    let s:=burst q (X.z (e i).val); change Lat.slots _ _ (pluck _ s _) =pluck K s (X.mark (e i).val p); rw [←partColor,he.tint]
omit he
-- equivalence billing.L.
omit [Fintype I] in
lemma eurobud (e: I≃J)(f:J→ℝ)(hf:SumBudget (f∘e) M) : SumBudget f M:=by
    have hp:∀ i,0≤f i:=fun i=>by obtain ⟨i,rfl⟩:= e.surjective i; exact hf.1 _
    exact ⟨hp,e.summable_iff.mp hf.2.1,(e.tsum_eq f).symm.trans_le hf.2.2⟩
variable (U V:ℝ)(b':ℝ)
lemma candied (S:R→Support c)(e:R ≃ Sp) (z:R→ Label d)(hz:∀ i,Beacon.ActionTest Taper k (Reel.speaker q X (e i).val) (z i).val)(ht: Summable z) (hP:(∑' i, z i)=p)(f g:R→ℝ)
    (hF:∀ i, Flame (Reel.speaker q X (e i).val) P (S i) o η Dx nL (f i))(hG:∀ i,Sight (X.addr (e i).val).support o 2 P η (Reel.speaker q X (e i).val) (g i))
    (h1:∀ i,(X.addr (e i).val).support⊆S i)(h2:∀ i,Carte.Hem.pot (r+1) c k⊆ S i)(h3: Ac.Hit S P.B f b' U)(h4: Ac.Hit S P.B g b' V) : Gel q X Taper i k P p η b' U V Dx nL r:=by -- B may not param
       refine ⟨S ∘ e.symm,z ∘ e.symm,fun i=>by simpa using (h1 (e.symm i)),fun i=>h2 _,fun i=>?_, e.symm.summable_iff.mpr ht,(e.symm.tsum_eq z).trans hP,⟨f∘e.symm,?_,?_⟩,g∘e.symm,?_,?_⟩
       · simpa only [e.apply_symm_apply,Function.comp_apply] using hz (e.symm i)
       · intro i; simpa using (hF (e.symm i))
       · intro i; apply eurobud e; simpa [Function.comp_def] using h3 i
       · intro i; simpa using (hG (e.symm i))
       intro i; apply eurobud e; simpa [Function.comp_def] using h4 i
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Gel
