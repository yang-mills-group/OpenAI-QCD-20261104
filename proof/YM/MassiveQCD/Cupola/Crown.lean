import YM.MassiveQCD.Ribbon.Shifts
import YM.MassiveQCD.Apron.Awake
/-! # Environments/resources on every monic sector of a cup.
 A monic sector is the full basis blade with even/odd burst convention; dress,
 parity orientation & all support footprints paid. No requirement of upward
 closure (for downstream deletion).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek Ribbon Function Finset MeasureTheory Filter NormedSpace
open scoped BigOperators Topology ContDiff Classical
variable (A:Type){I:Type}[Fintype A][Fintype I](q:I→Bool)
local notation "R" => Spine I
local notation "X"=>A⊕Spine I
-- true.S
noncomputable def pluck (s:Finset (Spine I)): Patio (A⊕Spine I)→L[ℂ] Alg A:= (scrape A s).comp ((light _).toLinearMap.toContinuousLinearMap)
noncomputable def chooseBlade (s:Finset R): Patio (A⊕Spine I)→L[ℂ] Patio (A⊕Spine I):=LinearMap.toContinuousLinearMap (((stake A s).comp (pluck A s)).toLinearMap.codRestrict ((roomA X).toSubmodule) (fun x=>even_stake _ _ (serene _ (x.property)))) -- actual visual
noncomputable abbrev pick (s:Finset I): Patio X→L[ℂ] Patio X:=chooseBlade A (burst q s)
lemma choice (s: Finset R)(x:Patio X) : light X (chooseBlade A s x)= stake A s (pluck A s x):=rfl
lemma many (s t: Finset R)(x:Patio X): pluck A s (chooseBlade A t x)=if s=t then pluck A s x else 0:= (stakesX A s t (pluck A t x)).trans (by split_ifs with h; exact congr_arg (fun r=> pluck A r x) h.symm; exact rfl)
lemma choseTuft (s:Finset I)(x:Patio X): Polite q s (pick A q s x):= ⟨_,choice _ _ _|>.symm⟩
lemma eq_pick (s: Finset I)(x:Patio X)(h:Polite q s x): pick A q s x=x:= by apply Subtype.ext; apply h.exact
lemma pluckVisible (x y:Patio X)(h:∀ s, pluck A s x=pluck A s y): x=y:= by apply Subtype.ext; exact vista A _ _ h
noncomputable def slash (S:Set (Finset I)):Patio X →L[ℂ] Patio X:=∑ i∈Finset.univ.filter (fun i=>i ∈ S),pick A q i
noncomputable abbrev chop (Z:Finset I):= slash A q (Z.powerset:Set (Finset I))
lemma control (S:Set (Finset I))(j:Finset R)(x:Patio X) : pluck A j (slash A q S x)=if ∃ i∈ S,j=burst q i then pluck A j x else 0:=by
   rw [slash,_root_.sum_apply,map_sum]; split
   next h=> obtain ⟨i,hi,rfl⟩:=h; rw [sum_eq_single i, pick,many,if_pos rfl]; exact fun k _ h=> (many A _ _ _).trans (if_neg fun ht=> h (burstUnique q ht).symm); simp [hi]
   next h=> exact sum_eq_zero fun i hi=> (many A _ _ _).trans (if_neg fun he=>h ⟨i,(mem_filter.mp hi).2,he⟩)
lemma control_pick (S:Set (Finset I))(j:Finset I)(x:Patio X) : pick A q j (slash A q S x)= if j∈ S then pick A q j x else 0:=by
   let t:= burst q j; have hp:(∃ i∈S,t=burst q i)↔j∈ S:=⟨fun ⟨k,hk,hr⟩=> (burstUnique q hr).symm ▸ hk,fun hf=>⟨j,hf,rfl⟩⟩; apply Subtype.ext; split
   next h=> show stake A t (pluck A t (slash A q S x)) = stake A t (pluck A t x); rw [control,if_pos (hp.2 h)]
   next h=> show stake A t (pluck A t (slash A q S x))=0; rw [control,if_neg fun he=>h (hp.1 he),map_zero]
-- algebra Subspace on supports, preservation under limits
structure ValidPieces (U: Finset I)(x:Patio X): Prop where
  wholly: chop A q U x=x
namespace ValidPieces
variable {A q}{U:Finset I}{x y:Patio (A⊕Spine I)}
lemma role (i:Finset I)(h:Polite q i x)(hp:i ⊆ U):ValidPieces A q U x:=by
   constructor; apply pluckVisible; intro s; rw [control]; split; rfl
   next ht=> exact (h.spectral _ (fun e=> ht ⟨i,mem_powerset.mpr hp,e⟩)).symm
lemma raise {U' : Finset I}(h:ValidPieces A q U x)(hp:U⊆U') : ValidPieces A q U' x:=by
   constructor; apply pluckVisible; intro i; rw [control]; split; rfl
   next hr=>refine Eq.trans ?_ (congr_arg (pluck A i) h.wholly); rw [control,if_neg fun ⟨j,hj,e⟩=>hr ⟨j,mem_powerset.mpr ((mem_powerset.mp hj).trans hp),e⟩]
lemma closedV : IsClosed {x: Patio (A ⊕ Spine I) | ValidPieces A q U x}:=by convert! isClosed_eq ((chop A q U).continuous) continuous_id using 1; ext x; exact ⟨fun h=>(show ValidPieces _ _ _ x from h).wholly,fun (h:(chop A q U) x = id x)=> (⟨h⟩: ValidPieces A q U x)⟩
lemma minus (h:ValidPieces A q U x): ValidPieces A q U (-x):= ⟨(map_neg ..).trans (congr_arg _ h.wholly)⟩
lemma plus (h:ValidPieces A q U x)(he:ValidPieces A q U y):ValidPieces A q U (x+y):= ⟨(map_add ..).trans (congr_arg₂ _ h.wholly he.wholly)⟩
lemma tilt (h:ValidPieces A q U x)(m:ℂ): ValidPieces A q U (m • x):= ⟨by rw [map_smul,h.wholly]⟩
lemma noneV : ValidPieces A q U 0:=⟨map_zero _⟩
lemma oneV : ValidPieces A q U 1:=role _ (polite_empty_one q) (empty_subset _)
lemma cost {D:Type}(p: Finset D)(f:D→Patio (A⊕Spine I))(h:∀ i∈p,ValidPieces A q U (f i)): ValidPieces A q U (∑ i∈p,f i):= ⟨by rw [map_sum]; exact sum_congr rfl fun i hi=> (h i hi).wholly⟩
lemma wholeV (h:ValidPieces A q U x): x=∑ i∈ (Finset.univ.filter (fun i=>i∈ (U.powerset:Set (Finset I)))),pick A q i x:= h.wholly.symm.trans (by unfold chop slash; rw [_root_.sum_apply]; refine sum_congr ?_ (fun i _=>rfl); ext x; simp)
lemma mul (h:ValidPieces A q U x)(he:ValidPieces A q U y): ValidPieces A q U (x*y):=by
    rw [h.wholeV,he.wholeV]; simp_rw [Finset.mul_sum,sum_mul]; apply cost; intro i hi; apply cost; intro j hj; apply role (j∪i) ((choseTuft _ _ _ _).attached (choseTuft _ _ _ _)); exact union_subset (mem_powerset.mp ((mem_filter.mp hj).2)) (mem_powerset.mp ((mem_filter.mp hi).2))
noncomputable def course (q:I→Bool) (U:Finset I): Subalgebra ℂ (Patio (A⊕Spine I)) where
    carrier:= {x|ValidPieces A q U x}
    add_mem':=plus
    mul_mem':=mul
    zero_mem':=noneV
    one_mem':=oneV
    algebraMap_mem' i:= by rw [Algebra.algebraMap_eq_smul_one]; exact oneV.tilt _
lemma powV (h:ValidPieces A q U x)(i:ℕ):ValidPieces A q U (x^i):= (course (A:=A) (q:=q) U).pow_mem h i
lemma tab {D:Type}{f:D→Patio (A⊕Spine I)}(h:HasSum f x)(hp:∀ i,ValidPieces A q U (f i)) : ValidPieces A q U x:=by have hv:= (chop A q U).hasSum h; exact ⟨(hv.congr_fun fun i=> (hp i).wholly.symm).unique h⟩ -- congr_fun orientation check
lemma exponent (h:ValidPieces A q U x): ValidPieces A q U (exp x):= tab (exp_series_hasSum_exp' (𝕂:=ℂ) x) (fun i=>(powV h i).tilt _)
end ValidPieces
lemma splash {S:Set (Finset I)}{U:Finset I}(x:Patio X)(hp: S⊆ (U.powerset:Set (Finset I))): ValidPieces A q U (slash A q S x):=by
   refine ⟨?_⟩; apply pluckVisible; intro i; rw [control]; split; rfl
   next hr=> rw [control,if_neg fun ⟨j,hj,e⟩=>hr ⟨j,hp hj,e⟩]
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.ValidPieces.exponent
