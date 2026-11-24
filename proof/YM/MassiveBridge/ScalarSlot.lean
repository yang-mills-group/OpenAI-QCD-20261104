import YM.MassiveBridge.SlotDeriv

/-!
# Units in W expectations

 via all-order swaps on points, then continue by comparing holomorphic
 functions which ignore that slot completely. Don't infer from spacelike commutation
 an assumption about overlapping tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Unary
open Function Set Filter Analysis MeasureTheory Distribution
open Boundary hiding Fields Surface Waves Letter Sentence
open Probe Mink Mink.Poincare Complex
open Fields (distinct pointMoment)
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace
variable {n : ℕ} {Q:Sequence} {P:Calibration Q} {X:Fields} {S:X.Kernel} {Y:Waves X} {W:Surface X} {B:∀ n, Blanket n} {A:W.Aurora B}
lemma unit_even (E:X.System P): X.homogeneous false X.unit := by
  change X.parity X.unit=X.unit
  rw [← E.units 0 none, E.parity]
  congr 1
  apply Subtype.ext
  rw [P.sym.parityActs,P.sym.unitActs, UV.parityAct, UV.unit, TensorProduct.map_tmul]
  simp

section points
lemma unit_first (H:Fields.Euclidean S) (l : Cluster X)(x:E4) (h:distinct (F:=X) ((x,X.unit)::l)):
    pointMoment S ((x,X.unit)::l) = pointMoment S l:=by
  have he : (x,X.unit)::l = realize (Fin.cons X.unit (tokens l)) (Points.cons x (positions l)) := by
    rw [realize,List.ofFn_succ]
    simp only [Points.cons, points_apply, Fin.cons_zero,List.cons.injEq, true_and]
    exact (List.ofFn_get l).symm
  have hc : Points.cons x (positions l) ∈ conf _ := by rw [he] at h; simpa using h
  rw [he,readAt, H.unit l.length _ hc]
  unfold pointMoment
  congr 2

lemma add_point(l r:Cluster X)(x:E4)(v w:X.W): pointMoment S (l++(x,v+w)::r)=pointMoment S (l++(x,v)::r)+pointMoment S (l++(x,w)::r):=by
  let i : Fin (l.length + (r.length+1)):= ⟨l.length,by omega⟩
  let q:Points (l.length+(r.length+1)):= points (Fin.append (positions l).ofLp (Points.cons x (positions r)).ofLp)
  let z : Fin (l.length+(r.length+1)) → X.W:= Fin.append (tokens l) (Fin.cons 0 (tokens r))
  have e (v:X.W): l++(x,v)::r = realize (update z i v) q:=by
    rw [realize]
    let j := Fin.append l.get ((x,v)::r).get
    have hh : (fun k=> (q k,update z i v k))=j:=by
      funext k
      refine Fin.addCases (fun k=>?_) (fun k=>?_) k
      · have he: k.castAdd _ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_castAdd] at HH; omega
        rw [update_of_ne he,show j (Fin.castAdd (r.length+1) k)=l.get k from Fin.append_left l.get ((x,v)::r).get k]; simp only [Fin.append_left,q,z,points_apply]
        rfl
      refine Fin.cases ?_ ?_ k
      · rw [show Fin.natAdd _ 0=i from Fin.ext (by simp [i]),update_self] -- easier simp
        change (q (Fin.natAdd l.length 0),v)= j (Fin.natAdd l.length 0)
        simp [j,q,Points.cons]
      intro a
      have he: Fin.natAdd l.length a.succ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_natAdd,Fin.val_succ] at HH; omega
      rw [update_of_ne he, show j _=r.get a from (Fin.append_right ..).trans (by change ((x,v)::r).get a.succ=r.get a;rfl)]
      simp only [Fin.append_right,q,z,Points.cons,Fin.cons_succ,points_apply]
      rfl
    rw [hh]; unfold j
    rw [List.ofFn_fin_append,List.ofFn_get,List.ofFn_get]
  rw [e (v+w),e v, e w,readAt,readAt,readAt,MultilinearMap.map_update_add]

private lemma unit_steps (E:X.System P) (H:Fields.Euclidean S)(l r: Cluster X)(x y:E4) (v:X.W)
    (h: distinct (l++ (x,v)::(y,X.unit)::r)):
    pointMoment S (l++ (x,v)::(y,X.unit)::r)=pointMoment S (l++ (y,X.unit)::(x,v)::r):=by
  have he (u:X.W) (p) (hu:X.homogeneous p u): pointMoment S (l++(x,u)::(y,X.unit)::r)= pointMoment S (l++ (y,X.unit)::(x,u)::r):=by
    have hv : distinct (F:=X) (l++(x,u)::(y,X.unit)::r):=by rw [locations] at *; simpa only [List.map_append,List.map_cons] using h
    simpa using H.swap l r _ _ hv p false hu (unit_even E)
  let t:=X.parity v
  have hz: X.parity t=v:=E.folded v
  let k :ℂ:=2⁻¹
  let b:= k • (v+t)
  let a:= k • (v-t)
  have hsum: b+a=v:=by
    unfold b a; rw [←smul_add, show v+t+(v-t)= (2:ℂ) • v from by -- force scalar
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num [k]
  have ha: pointMoment S (l++(x,a)::(y,X.unit)::r)=pointMoment S (l++ (y,X.unit)::(x,a)::r):=he a true (show X.parity a = -a from by
       unfold a t k at *; rw [map_smul, map_sub,hz, show X.parity v - v= -(v-X.parity v) from by abel, smul_neg])
  have hb: pointMoment S (l++(x,b)::(y,X.unit)::r)=pointMoment S (l++ (y,X.unit)::(x,b)::r):= he b false (show X.parity b=b from by
       unfold b; rw [map_smul,map_add,hz]; congr 1; exact add_comm ..)
  have eq (u:X.W): l++ (y,X.unit)::(x,u)::r = (l++[(y,X.unit)]) ++ (x,u)::r := by simp
  conv_lhs => rw [← hsum,add_point]
  conv_rhs => rw [eq,← hsum,add_point,←eq,←eq]
  rw [ha,hb]

lemma unit_point (E:X.System P)(H:Fields.Euclidean S)(l r:Cluster X)(x:E4)(h: distinct (l++(x,X.unit)::r)): pointMoment S (l++(x,X.unit)::r)=pointMoment S (l++r):=by
  induction l using List.reverseRecOn generalizing r with
  | nil => simpa using unit_first H r x (by simpa using h)
  | append_singleton l a ih =>
    obtain ⟨y,v⟩:=a
    simp only [List.append_assoc,List.cons_append, List.nil_append] at *
    rw [unit_steps E H l r y x v h]; apply ih
    rw [locations] at *; exact ((List.Perm.append_left l (List.Perm.swap _ _ _)).map Prod.fst).nodup h

variable {α:Type*}
lemma ofFn_skip (f : Fin (n+1) → α)(i: Fin (n+1)):(List.ofFn f).eraseIdx i.val = List.ofFn (f ∘ i.succAbove) := by
  refine List.ext_get (by have := i.isLt; simp [List.length_eraseIdx, *]) (fun j hj ht=>?_)
  rw [List.get_ofFn, List.get_eq_getElem, List.getElem_eraseIdx hj]
  split_ifs with h
  · rw [List.getElem_ofFn, comp_apply,Fin.succAbove_of_castSucc_lt]
    · rfl
    exact h
  rw [List.getElem_ofFn, comp_apply,Fin.succAbove_of_le_castSucc]
  · rfl
  exact Nat.le_of_not_lt h

lemma iso_arity (E:X.System P)(H:Fields.Euclidean S)(v: Fin (n+1)→X.W)(x:Points (n+1))(h:x∈conf _)(i:Fin (n+1))(hz:v i=X.unit):
    S (n+1) x v=S n (points (x.ofLp ∘ i.succAbove)) (v ∘ i.succAbove):=by
  rw [← readAt,← readAt]
  let l :=realize v x
  have he:l.eraseIdx i = realize (v ∘ i.succAbove) (points (x.ofLp ∘ i.succAbove)):=ofFn_skip _ _
  let m:=l.take i
  let r := l.drop (i.val+1)
  have ht : l = m ++ (x i,X.unit)::r:=by
     have hi : i.val < l.length := by unfold l realize; rw [List.length_ofFn]; exact i.isLt
     have H : l[i.val]=(x i,X.unit):= by unfold l realize; rw [List.getElem_ofFn];exact Prod.ext rfl hz
     unfold m r; rw [← H]
     nth_rw 1 [←List.take_append_drop (i.val+1) l, ← List.take_concat_get hi]
     simp
  change pointMoment S l=_
  rw [← he,List.eraseIdx_eq_take_drop_succ] -- keep l
  nth_rw 1 [ht]
  exact unit_point E H m r (x i) (by rw [←ht]; exact (realized ..).2 h)

end points

open Work.C09 (time_compare)
lemma restrict_unit (E:X.System P)(H:Fields.Euclidean S) (hh:Y.Region S)(v:Fin (n+1)→X.W)(i:Fin (n+1))(hv:v i=X.unit)(x:Points (n+1))(y:Heights (n+1))(hy:y∈east _):
   Y.restricted v y x= Y.restricted (v ∘ i.succAbove) (y ∘ i.succAbove) (points (x.ofLp ∘ i.succAbove)) := by
  let P(z):=Y.F _ z (Boundary.trace x) v
  let Q(z: Times (n+1)):=Y.F _ (z ∘ i.succAbove) (Boundary.trace x ∘ i.succAbove) (v ∘ i.succAbove)
  have hQ:DifferentiableOn ℂ Q (strict _):=by
     apply (hh.hol _ _ _).comp (f := fun z:Times (n+1)=> z ∘ i.succAbove)
     · unfold Function.comp; fun_prop
     intro z hz
     exact hz.comp (Fin.strictMono_succAbove i)
  have he (u:Heights (n+1))(p:u∈east _) (b:ℝ): P (fun i=>(↑(u i + b*0):ℂ)*I) = Q (fun i=>(u i:ℂ)*I) := by
     unfold P Q; simp only [mul_zero,add_zero]
     rw [hh.roots (n+1) v _ u p, iso_arity E H v _ (clear p _) i hv]
     exact (hh.roots n (v ∘ i.succAbove) _ _ (p.comp (Fin.strictMono_succAbove i))).symm
  have tp := time_compare P Q (hh.hol _ v _) hQ 0 he (shift x y) (Waves.shift_strict x hy)
  simp only [ofReal_zero, add_zero] at tp; exact tp

open WithLp
-- product volume without any constant factors

def linearFin (n : ℕ): Points n ≃ᵐ (Fin n→E4):=(PiLp.homeomorph 2 (fun _:Fin n => E4)).toMeasurableEquiv
lemma linearFin_preserve (n: ℕ):MeasurePreserving (linearFin n):= Points.volume_product n

def partialCut (i:Fin (n+1)): Points (n+1)≃ᵐ E4×Points n:=MeasurableEquiv.trans (linearFin _) <| MeasurableEquiv.trans (MeasurableEquiv.piFinSuccAbove (fun _=>E4) i) (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (linearFin _).symm)
lemma partialCut_at (i:Fin (n+1))(x: Points (n+1)): partialCut i x=(x i,points (x.ofLp ∘ i.succAbove)):=rfl
lemma partialCut_volume (i:Fin (n+1)): MeasurePreserving (partialCut i) volume (volume.prod volume) :=
   (((MeasurePreserving.id (volume:Measure E4)).prod (linearFin_preserve n).symm).comp (volume_preserving_piFinSuccAbove _ i)).comp (linearFin_preserve _)

lemma ignore_unit (E:X.System P)(H:Fields.Euclidean S) (hh:Y.Region S)(v:Fin (n+1)→X.W)(i:Fin (n+1))(hv:v i=X.unit) (f:Fin (n+1)→Test4)(y:Heights (n+1))(hy:y∈east _):
  Y.psi v y (Joint.materialize _ f) = (∫ x, f i x) * Y.psi (v ∘ i.succAbove) (y ∘ i.succAbove) (Joint.materialize n (f ∘ i.succAbove)) := by
  let A:= Joint.materialize _ f
  let B:= Joint.materialize _ (f ∘ i.succAbove)
  let U:= Y.restricted (v ∘ i.succAbove) (y ∘ i.succAbove)
  let T(q:E4×Points n):= f i q.1 * (U q.2 * B q.2)
  have e: (fun x=> Y.restricted v y x * A x)= T ∘ partialCut i:=by
    funext x
    rw [restrict_unit E H hh v i hv _ y hy, comp_apply, partialCut_at]
    unfold A T B; rw [Joint.material_at,Joint.material_at,Fin.prod_univ_succAbove _ i]; change _= (f i (x i))*(Y.restricted _ _ _ * ∏ j:Fin n, f _ (x _)); ring
  unfold Waves.psi
  rw [e]; apply ((partialCut_volume i).integral_comp (partialCut i).measurableEmbedding T).trans
  exact integral_prod_mul (f i) (fun x=> U x * B x)

lemma W_unit (E:X.System P)(H:Fields.Euclidean S)(hh:Y.Region S)(hb:Y.NonTangentialFree W)
    (v:Fin (n+1)→X.W)(i:Fin (n+1))(hv:v i=X.unit) (f:Fin (n+1)→Test4):
   W.W _ v (Joint.materialize _ f) = (∫ x, f i x)* W.W n (v ∘ i.succAbove) (Joint.materialize n (f ∘ i.succAbove)) := by
   let l(y:Heights (n+1)):=y ∘ i.succAbove
   have e:Tendsto l (𝓝[east (n+1)] 0) (𝓝[east n] 0) := by
     have hc:Continuous l := by unfold l comp; fun_prop
     exact hc.continuousWithinAt.tendsto_nhdsWithin (fun y hy=> hy.comp (Fin.strictMono_succAbove i))
   haveI := awaits (light (n+1))
   exact tendsto_nhds_unique_of_eventuallyEq (hb.corner ..) (tendsto_const_nhds.mul ((hb.corner ..).comp e)) (Eventually.mono self_mem_nhdsWithin fun y h=> ignore_unit E H hh v i hv f y h)
end YM.Massive.Bridge.Unary
