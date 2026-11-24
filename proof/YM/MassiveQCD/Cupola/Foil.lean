import YM.MassiveQCD.Cupola.Dollar
/-! # Tape publication costs on specific & any monic sectors -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function Loom
open MeasureTheory NormedSpace Filter
open scoped Topology BigOperators ContDiff Classical Matrix
variable {c:Side}{I J:Type}[Fintype I]
variable (N:ℕ)(o:I→Site c)(φ:ℝ)(q:I→Bool)
local notation "M"=> ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "X"=> K⊕Spine I
open Patron Sway OrbitG Villa Stitch Apron
structure Mint (s:Finset I)(x:EvenA c (ample N I)):Prop where
    spark : (banknote N o φ ∘ withdraw N o φ) x=x
    shows : Polite q s (withdraw N o φ x)
structure Well (x:EvenA c (ample N I)):Prop where
    spark : (banknote N o φ ∘ withdraw N o φ) x=x
    applies : ValidPieces (Keys c N) q univ (withdraw N o φ x)
noncomputable def trophy (S:Set (Finset I)): EvenA c (ample N I) →L[ℝ] EvenA c (ample N I):= ContinuousLinearMap.restrictScalars ℝ ((banknote N o φ).toLinearMap.toContinuousLinearMap.comp ((slash (Keys c N) q S).comp ((withdraw N o φ).toLinearMap.toContinuousLinearMap)))
namespace Mint
set_option quotPrecheck false
variable {N φ o q}{s t:Finset I}{x y:EvenA c (ample N I)}
lemma launch (h: Mint N o φ q s x) : Well N o φ q x:=⟨h.spark,ValidPieces.role _ h.shows (subset_univ _)⟩
private lemma plaits (s : Finset I)(x: Patio (Keys c N ⊕ Spine I)): slash (Keys c N) q ({s}:Set (Finset I)) x=pick (Keys c N) q s x:=by unfold slash; rw [_root_.sum_apply,sum_eq_single s (by simp) (by simp)]
lemma gauge (h:0<φ) : Mint N o φ q s x ↔ trophy N o φ q {s} x=x:=by
    let A:= Keys c N; let P:= withdraw N o φ; let V:= banknote N o φ; have he x:trophy N o φ q {s} x=V (pick A q s (P x)):=congr_arg V (plaits s (P x))
    constructor; intro hp; rw [he,eq_pick A q s (P x) hp.shows]; exact hp.spark
    intro hh; rw [he] at hh; let z:= pick A q s (P x); have he:P x=z:= (congr_arg P hh.symm).trans (home N o φ h z); refine ⟨show V (P x)=x by rw [he]; exact hh, he.symm ▸ (choseTuft _ _ _ _)⟩
lemma initiate (s:Finset I)(h:0<φ)(x:Patio (Keys c N⊕Spine I))(hx:Polite q s x): Mint N o φ q s (banknote N o φ x):=⟨congr_arg _ (home N o φ h x), (home N o φ h x).symm ▸ hx⟩
lemma boon (h:Mint N o φ q s x)(hx:Mint N o φ q t y):Mint N o φ q (s∪t) (x*y):= ⟨by simp only [comp_apply,map_mul]; exact congr_arg₂ (·*·) h.spark hx.spark, by rw [map_mul]; exact h.shows.attached hx.shows⟩
lemma none (s:Finset I): Mint N o φ q s 0:=⟨by simp, by rw [map_zero]; exact polite_nil ..⟩
lemma oneV : Mint N o φ q ∅ 1:= ⟨by simp,by rw [map_one]; exact polite_empty_one _⟩
lemma sum (h:0<φ) (s:Finset I)(u:Finset J)(x:J→ EvenA c (ample N I))(hx:∀ i∈u,Mint N o φ q s (x i)) : Mint N o φ q s (∑ i∈u,x i):=(gauge h).mpr (by rw [map_sum]; exact sum_congr rfl (fun i hi=> (gauge h).mp (hx i hi)))
lemma product (s:J→ Finset I)(u:Finset J)(x:J→ EvenA c (ample N I))(hx:∀ i∈u,Mint N o φ q (s i) (x i)) : Mint N o φ q (u.biUnion s) (∏ i∈u,x i):=by
    induction u using Finset.induction_on with
    | empty=>rw [Finset.prod_empty,biUnion_empty]; exact oneV
    | insert i s hi ih=> rw [prod_insert hi,biUnion_insert]; exact (hx _ (mem_insert_self ..)).boon (ih (fun _ h=> hx _ (mem_insert_of_mem h)))
lemma euro (h:0<φ)(k:ℝ)(hx:Mint N o φ q s x): Mint N o φ q s (k • x):=(gauge h).mpr (by rw [map_smul,(gauge h).mp hx])
lemma integral {J:Type*}[MeasurableSpace J](h:0<φ)(s:Finset I)(p:J→EvenA c (ample N I))(a :Measure J)(hp:∀ i,Mint N o φ q s (p i)): Mint N o φ q s (∫ i,p i ∂a):=by
   by_cases he:Integrable p a; swap; · rw [integral_undef he]; exact none _
   apply (gauge h).mpr; rw [← ContinuousLinearMap.integral_comp_comm _ he]; exact integral_congr_ae (Eventually.of_forall (fun x=> (gauge h).mp (hp x)))
lemma color (h:0<φ)(z:Lat.Frame c)(hh:Mint N o φ q s x): Mint N o φ q s (sways (Lat.rotates (ample N I) z) x) :=by
    rw [show sways (Lat.rotates (ample N I) z) x=banknote N o φ (parcelColor N z I (withdraw N o φ x)) from (congr_arg _ hh.spark.symm).trans ((across N o φ q s z _ hh.shows).symm)] -- ... syntax
    exact initiate _ h _ (vault N q s _ z hh.shows)
end Mint
namespace Well
variable {N φ o q}{x y:EvenA c (ample N I)} -- type implicit syntax earlier.S
lemma crown (h:0<φ) : Well N o φ q x↔ trophy N o φ q ((Finset.univ:Finset I).powerset:Set (Finset I)) x=x:=by
    let A:= Keys c N; let t:= chop A q Finset.univ; let P:=withdraw N o φ; let u:=banknote N o φ; change _↔ u (t (P x))=x; constructor
    · intro ⟨hp,hx⟩; rw [hx.wholly]; exact hp
    intro hv; have he:P x=t (P x):=(congr_arg P hv.symm).trans (home N o φ h _); exact ⟨(congr_arg u he).trans hv, ⟨he.symm⟩⟩
lemma plus (h:0<φ)(hp:Well N o φ q x)(he:Well N o φ q y): Well N o φ q (x+y):= (crown h).mpr (by rw [map_add,(crown h).mp hp,(crown h).mp he])
lemma minus (h:0<φ)(hp:Well N o φ q x): Well N o φ q (-x):= (crown h).mpr (by rw [map_neg,(crown h).mp hp])
lemma zeroV : Well N o φ q 0:= (Mint.none (∅:Finset I)).launch
lemma boon (h:Well N o φ q x)(hx:Well N o φ q y):Well N o φ q (x*y):= ⟨by simp only [comp_apply,map_mul]; exact congr_arg₂ (·*·) h.spark hx.spark, by rw [map_mul]; exact h.applies.mul hx.applies⟩
lemma oneV : Well N o φ q 1:= Mint.oneV.launch
lemma flash (hp:Well N o φ q x): Well N o φ q (NormedSpace.exp x):=by
    let p:=withdraw N o φ; let v:=banknote N o φ; have hx : p (exp x)= exp (p x):= map_exp p p.toLinearMap.toContinuousLinearMap.continuous x -- · argument?
    constructor; · exact ((congr_arg v hx).trans (map_exp v v.toLinearMap.toContinuousLinearMap.continuous _)).trans (congr_arg _ hp.spark)
    exact hx.symm ▸ hp.applies.exponent
lemma total (h:0<φ){f:J→EvenA c (ample N I)}(hp:∀ i,Well N o φ q (f i)):Well N o φ q (∑' i,f i):=by
    by_cases hh:Summable f; swap; · rw [tsum_eq_zero_of_not_summable hh]; exact zeroV
    apply (crown h).mpr; rw [ContinuousLinearMap.map_tsum _ hh]; exact tsum_congr fun i=>(crown h).mp (hp i)
lemma product (u:Finset J)(x:J→ EvenA c (ample N I))(hx:∀ i∈u,Well N o φ q (x i)) : Well N o φ q (∏ i∈u,x i):=by
    induction u using Finset.induction_on with
    | empty=>rw [Finset.prod_empty]; exact oneV
    | insert i s hi ih=> rw [prod_insert hi]; exact (hx _ (mem_insert_self ..)).boon (ih (fun _ h=> hx _ (mem_insert_of_mem h)))
lemma sum (h:0<φ) (u:Finset J)(x:J→ EvenA c (ample N I))(hx:∀ i∈u,Well N o φ q (x i)) : Well N o φ q (∑ i∈u,x i):=(crown h).mpr (by rw [map_sum]; exact sum_congr rfl (fun i hi=> (crown h).mp (hx i hi)))
lemma euro (h:0<φ)(k:ℝ)(hx:Well N o φ q x): Well N o φ q (k • x):=(crown h).mpr (by rw [map_smul,(crown h).mp hx])
lemma pin (s:Finset (Spine I))(h:0<φ)(hp: Well N o φ q x) : load (fun _=>φ) (pluck (Keys c N) s (withdraw N o φ x)) ≤ ‖Loom.token c (ample N I) φ x‖:= ((atWorth N o φ h s (withdraw N o φ x))).trans_eq (congr_arg (fun u=> ‖token c (ample N I) φ u‖) hp.spark)
end Well
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.Well.pin
