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
local notation "H!"=> numbered q A s
lemma venous (y:I→Patio (A⊕Spine I))(x:I→Alg A)(he:∀ i,(y i).val= stake A (burst q {i}) (x i)): Cove.light (A⊕Spine I) ((List.ofFn fun i=>y (s i)).prod) = fiber (Spine I) (List.ofFn (fun i=>x (s i))).prod * quill A (armature q s):=by
    induction n with
    | zero=>simp [armature]
    | succ n ih=>
       let z:=Fin.tail s; let U:=(List.ofFn fun i=>y (z i)).prod; let t:=U.val; let W:=(quill A) (armature q z); let J:=(List.ofFn fun i=>x (z i)).prod; let o:=s 0
       let F:=(fiber (Spine I) (A:=A)); let G:=quill A (B:=Spine I) -- verify
       let Q:=(G) (mono (burst q {o})); have hG: Plus t:= U.property; have H:t=F J * W:=ih z; have hu:(List.ofFn fun i=>y (s i)).prod=y (s 0)*U:=by rw [List.ofFn_succ,List.prod_cons]; rfl -- syntax
       rw [hu,arm,List.ofFn_succ,List.prod_cons,map_mul,map_mul,map_mul]
       change (y o).val*t=F (x o) * F J * (W*Q); rw [he,markedOut]; change (F (x o)* Q)*t=_; rw [mul_assoc,hG.central Q|>.eq, H]; simp only [mul_assoc]
lemma needleE (y:I→Patio (A⊕Spine I))(x:I→Alg A)(w:Patio A) (he:∀ i,(y i).val = stake A (burst q {i}) (x i))(h:Injective s) : H! ((rootR (Spine I) A w)* NormedSpace.exp (∑ i:I,y i))=w.val*(List.ofFn (fun i=> x (s i))).prod:=by
   have hx(i:I): Polite q {i} (y i):=⟨_,(he i).symm⟩
   let v:= rootR (Spine I) A w; have hw: Polite q ∅ v:=by unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
   have hp (L:Finset I): NormedSpace.exp (∑ i∈L,y i)=∏ i∈L,(1+y i):=by
       induction L using Finset.induction_on with
       | empty=> simp
       | insert a b ha ih=>
          rw [sum_insert ha,prod_insert ha, NormedSpace.exp_add, ih]; apply congr_arg (fun x=>x*_); let U:=y a; have hh :U^2=0:= (sq U).trans ((hx a).nilpotent (hx a) (by simp)); change NormedSpace.exp U=1+U; rw [← HasSum.tsum_eq (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) U),tsum_eq_sum (s:=range 2)]; norm_num [Finset.sum_range_succ,NormedSpace.expSeries_apply_eq]; intro i hi; have hi':2 ≤ i:=Nat.le_of_not_gt fun h=> hi (mem_range.mpr h); simp only [pow_eq_zero_of_le hi' hh,smul_zero]
   have hY(L:Finset I): Polite q L (∏ i∈L,y i):=by
       induction L using Finset.induction_on with
       | empty=>rw [prod_empty]; exact polite_empty_one _
       | insert a b hab ih=> rw [prod_insert hab,←singleton_union]; exact (hx a).attached ih -- DEP rw edits may not.
   have hF(L:Finset I): ∏ i∈L,(1+y i)= ∑ j∈L.powerset, ∏ k∈j,y k:=by
        -- prod_add,Mathlib.
        simp [add_comm (1:X), Finset.prod_add]
   let K:= crest s; rw [hp,hF, Finset.mul_sum,map_sum,sum_eq_single K]
   · have hV: ∏ i∈K,y i=(List.ofFn fun i=> y (s i)).prod:=by unfold K crest; rw [prod_image h.injOn]; exact (List.prod_ofFn ..).symm -- check
     rw [hV]; let X':= List.ofFn fun i=>x (s i); apply cuts A q s h; change Cove.light _ (v*_)= _; rw [map_mul, venous A q s y x he,map_mul]; exact (mul_assoc ..).symm -- order
   · intro i hi hj; let v:= ∏ j∈i,y j; have hh: Polite q i (HMul.hMul (rootR (Spine I) A w) v):= Eq.mp (congr_arg (fun s=> Polite q s (HMul.hMul (rootR (Spine I) A w) v)) (empty_union i)) (hw.attached (hY i))
     change signG q s • pluck A (burst q K) _=0; rw [show pluck A _ _=0 from hh.spectral _ (fun hl=>hj ((burstUnique q hl).symm)),smul_zero]
   simp
end Quills
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Quills.needleE
