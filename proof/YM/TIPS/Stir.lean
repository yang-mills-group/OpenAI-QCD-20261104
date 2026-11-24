import YM.Profiles.Venues
import YM.Parishes.Rebates
import YM.Profiles.Wreaths
import YM.Profiles.Hoards
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
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Quills
variable (A:Type)[Fintype A] (q:I→Bool) (s:Fin n→I)
local notation "X"=> Patio (A⊕Spine I)
set_option quotPrecheck false
local notation "H!"=> numbered q A s
local notation "S"=>Ribbon.Spine I
omit [Fintype I] in
lemma plucks {B:Type}[Fintype B](x:Alg A)(y:Alg B)(u:Finset B): scrape A u (fiber B x * quill A y)= Grass.coef u y • x:=by
    let g:= quill A (B:=B); nth_rw 1 [← Grass.write y]; rw [map_sum,mul_sum,map_sum,sum_eq_single u]; · rw [map_smul,mul_smul_comm,map_smul,←markedOut,quid]
    · intro i hi h; rw [map_smul,mul_smul_comm,map_smul, ←markedOut,stakesX,if_neg h.symm,smul_zero]
    simp
-- choose any enumeration (don't impose order). covers hum.
noncomputable def tour (u:Finset I) (i:Fin u.card): I:= (u.equivFin.symm i).val
lemma snug (u:Finset I): Injective (tour u):=Subtype.val_injective.comp u.equivFin.symm.injective
lemma club (u:Finset I): crest (tour u)=u:=by
   ext i; rw [exists_fix]; constructor; rintro ⟨j,rfl⟩; exact (u.equivFin.symm j).2; intro h; refine ⟨u.equivFin ⟨i,h⟩,?_⟩; simp [tour]
variable (F:I→Patio (A⊕Spine I))(x:I→Alg A)(Y:Patio (A⊕Spine I))(hf:∀ i,(F i).val=stake A (burst q {i}) (x i))(hY:ValidPieces A q univ Y)
noncomputable def spliceG (T:Finset I) :ℂ:= signG q s *Grass.coef (burst q (crest s)) (armature q (tour (crest s \ T))*armature q (tour T))
-- no assumption grade of concat s.Card.
include hf hY
lemma bend (T:Finset I)(ht:T⊆ crest s): H! ((∏ i∈T,F i) * Y)=spliceG q s T • ((List.ofFn fun i=> x (tour T i)).prod * numbered q A (tour (crest s \ T)) Y):=by
    let n':= T.card; let Z:= ∏ i∈T,F i; let f' i:= Cupola.pick A q i Y; let h(i): X:= f' i; let U:=crest s; let t:= U\ T; let Φ:= numbered q A s
    have hPZ(L:Finset I): Polite q L (∏ i∈L,F i):=by
       induction L using Finset.induction_on with
       | empty=>rw [prod_empty]; exact polite_empty_one _
       | insert a b ha ih=> rw [prod_insert ha, ←singleton_union]; exact (show Polite q {a} (F a) from ⟨x a,(hf a).symm⟩).attached ih
    have hP: Polite q T Z:=hPZ T
    have hfy(i:Finset I): Polite q i (h i):= choseTuft A q i Y
    have htV: Φ (Z*Y)=Φ (Z*h t):=by
        nth_rw 1 [hY.wholeV]; rw [mul_sum,map_sum,sum_eq_single t]
        · intro i hi hiv; let T':=h i; by_cases hx:Disjoint T i
          swap; · rw [show Z* _ = 0 from hP.nilpotent (hfy i) hx,map_zero]
          change signG q s • pluck A (burst q (crest s)) (Z*T') = 0
          rw [show pluck A _ (Z*T')=0 from (?_:pluck A (burst q (crest s)) _=0),smul_zero]; apply (hP.attached (hfy i)).spectral; intro h'; apply hiv; have hT := burstUnique q h'; unfold t; change U=T∪i at hT; rw [hT]; ext x; constructor; intro h; exact mem_sdiff.mpr ⟨mem_union_right _ h,fun h1=> Finset.disjoint_left.mp hx h1 h⟩; intro h; obtain ⟨hz,hPq⟩:=mem_sdiff.mp h; exact (mem_union.mp hz).resolve_left hPq -- edit
        simp [t]
    let X':= List.ofFn fun i=>x (tour T i); let P:= (numbered q A (tour t)) (h t); let F':=fiber S (A:=A)
    have ht0: P=(numbered q A (tour t) Y):=by unfold P numbered; change signG q _ • pluck _ _ _= (signG q _) • (pluck _ _ Y); apply congr_arg; rw [club t]; unfold h f' Cupola.pick; rw [many,if_pos rfl]
    have hQ': (h t).val= F' P * quill A (armature q (tour t)):= Quills.charge A q (tour t) (h t) ((club t).symm ▸ hfy t) (snug t)
    have hZ : Z=(List.ofFn fun i=> F (tour T i)).prod:=by rw [List.prod_ofFn]; have hx:(∏ i∈crest (tour T),F i)=∏ i,F (tour T i):= Finset.prod_image ((snug T).injOn); exact (show ∏ i∈T,F i=_ from ((congr_arg (fun L:Finset I=> ∏ i∈ L,F i) (club T).symm).trans hx)) -- args
    have hf : Z.val=F' X'.prod*quill A (armature q (tour T)):=hZ.symm ▸ venous A q (tour T) F x hf
    change Φ (Z*Y)= _; rw [htV]; have hVal : (Z*h t).val=F' (X'.prod*P)*quill A (armature q (tour t)*armature q (tour T)):=by
       change Z.val*(h t).val= _; rw [hf,mul_assoc,(h t).property.central (quill A _)|>.eq,hQ',map_mul,map_mul]; simp only [mul_assoc]; -- commutes EVEN so no grades additional
    change signG q s • scrape A _ ((Z*h t).val)= _; rw [hVal,plucks,ht0]; exact (mul_smul ..).symm -- edit
lemma serveV : H! (NormedSpace.exp (∑ i:I,F i)*Y) = ∑ T∈ (crest s).powerset, spliceG q s T • ((List.ofFn fun i=>x (tour T i)).prod * numbered q A (tour (crest s \ T)) Y) :=by
    have hx(i:I): Polite q {i} (F i):=⟨_,(hf i).symm⟩
    have hp (L:Finset I): NormedSpace.exp (∑ i∈L,F i)=∏ i∈L,(1+F i):=by
       induction L using Finset.induction_on with
       | empty=> simp
       | insert a b ha ih=>
          rw [sum_insert ha,prod_insert ha, NormedSpace.exp_add, ih]; apply congr_arg (fun x=>x*_); let U:=F a; have hh :U^2=0:= (sq U).trans ((hx a).nilpotent (hx a) (by simp)); change NormedSpace.exp U=1+U; rw [← HasSum.tsum_eq (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) U),tsum_eq_sum (s:=range 2)]; norm_num [Finset.sum_range_succ,NormedSpace.expSeries_apply_eq]; intro i hi; have hi':2 ≤ i:=Nat.le_of_not_gt fun h=> hi (mem_range.mpr h); simp only [pow_eq_zero_of_le hi' hh,smul_zero]
    rw [hp,show (∏ i:I,(1+F i))= ∑ j∈(Finset.univ:Finset I).powerset, ∏ i∈j,F i from by simp [add_comm (1:X), Finset.prod_add],sum_mul,map_sum]; apply Eq.trans ?_ (sum_congr (g:=fun i↦ _) rfl (fun i hi=> bend A q s F x Y hf hY _ (mem_powerset.mp hi)))
    apply Eq.symm; refine sum_subset (s₁:=(crest s).powerset) (fun i hi=>mem_powerset.mpr (subset_univ _)) ?_; intro i hi hj
    let Z:=∏ j∈i,F j; have hF: Polite q i Z:=by
       unfold Z; clear hi hj
       induction i using Finset.induction_on with
       | empty=>rw [prod_empty]; exact polite_empty_one _
       | insert a b ha ih=> rw [prod_insert ha, ←singleton_union]; exact (hx a).attached ih
    have hk: shutter A (crest s) (Z*Y)=0:=by rw [map_mul, stamen_h A q _ _ _ hF, if_neg (fun h=>hj (mem_powerset.mpr h)),zero_mul]
    change signG q s • pluck A (burst _ _) (Z*Y)=_; rw [show pluck A (burst q (crest s)) (Z*Y)=0 from ((phoenixC A _ 0 _ (hk.trans (map_zero _).symm) _ (Ribbon.located q _))).trans (map_zero _),smul_zero] -- order inspect.
end Quills
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Quills.bend
#print axioms YM.MassiveQCD.Sample.Quills.serveV
