import YM.Gust.Horn
import YM.Gust.TopP
import YM.Rill.Print
-- Adapt sorted permutation.Tr.Ph
set_option autoImplicit false
set_option maxHeartbeats 580000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}{m n k d:ℕ}
abbrev pulseTags(l:Strip K)(i:Fin l.length):= (l.get i).2
abbrev grove(K: Choir)(v:Fin n→K.W)(x:Points n):Strip K:=List.ofFn fun i=>(x i,v i)
lemma grooved(x:Points n)(v:Fin n→K.W): tone (grove K v x)= K.total _ x v:= by exact report ..
lemma garden(x:Points n)(v:Fin n→K.W): Strip.distinct (grove K v x) ↔ x∈conf n:=by rw [Strip.spots,grove,List.map_ofFn,List.nodup_ofFn]; rfl
lemma unitMark (H :Foil P K T): markedW T false (lampU P K):= meMem (relic H 0) 0
lemma unit_first (H:Foil P K T)(l:Strip K)(x:E4)(h:Strip.distinct ((x,lampU P K)::l)): tone ((x,lampU P K)::l)=tone l:=by
       let z:=Points.cons x (locus l); have he: grove K (Fin.cons (lampU P K) (pulseTags l)) z=(x,lampU P K)::l:=by rw[grove,List.ofFn_succ]; simp only [z,Points.cons, points_apply, Fin.cons_zero,List.cons.injEq,true_and]; exact List.ofFn_get _
       rw [←he] at h ⊢; rw[grooved,H.functor _ _ ((garden ..).1 h)]; unfold tone; congr
lemma add_point(l r:Strip K)(x:E4)(v w:K.W): tone (l++(x,v+w)::r)=tone (l++(x,v)::r)+tone (l++(x,w)::r):=by
  let i : Fin (l.length + (r.length+1)):= ⟨l.length,by omega⟩
  let q:Points (l.length+(r.length+1)):= points (Fin.append (locus l).ofLp (Points.cons x (locus r)).ofLp)
  let z : Fin (l.length+(r.length+1)) → K.W:= Fin.append (pulseTags l) (Fin.cons 0 (pulseTags r))
  have e (v:K.W): l++(x,v)::r = grove K (update z i v) q:=by
    rw [grove]
    let j := Fin.append l.get ((x,v)::r).get
    have hh : (fun k=> (q k,update z i v k))=j:=by
      funext k
      refine Fin.addCases (fun k=>?_) (fun k=>?_) k
      · have he: k.castAdd _ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_castAdd] at HH; omega
        rw [update_of_ne he,show j (Fin.castAdd (r.length+1) k)=l.get k from Fin.append_left l.get ((x,v)::r).get k]; simp only [Fin.append_left,q,z,points_apply]
      refine Fin.cases ?_ ?_ k
      · rw [show Fin.natAdd _ 0=i from Fin.ext (by simp [i]),update_self] -- easier simp
        change (q (Fin.natAdd l.length 0),v)= j (Fin.natAdd l.length 0)
        simp [j,q,Points.cons]
      intro a
      have he: Fin.natAdd l.length a.succ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_natAdd,Fin.val_succ] at HH; omega
      rw [update_of_ne he, show j _=r.get a from (Fin.append_right ..).trans (by change ((x,v)::r).get a.succ=r.get a;rfl)]
      simp only [Fin.append_right,q,z,Points.cons,Fin.cons_succ,points_apply]
    rw [hh]; unfold j
    rw [List.ofFn_fin_append,List.ofFn_get,List.ofFn_get]
  rw [e (v+w),e v, e w,grooved,grooved,grooved,MultilinearMap.map_update_add]

private lemma unit_steps (hK:K.Domestic)(H:Foil P K T)(l r: Strip K)(x y:E4) (v:K.W)
    (h: Strip.distinct (l++ (x,v)::(y,(lampU P K))::r)):
    tone (l++ (x,v)::(y,(lampU P K))::r)=tone (l++ (y,(lampU P K))::(x,v)::r):=by
  have he (u:K.W) (p) (hu:markedW T p u): tone (l++(x,u)::(y,(lampU P K))::r)= tone (l++ (y,(lampU P K))::(x,u)::r):=by
    have hv : Strip.distinct (Q:=K) (l++(x,u)::(y,(lampU P K))::r):=by rw [spots _] at *; simpa only [List.map_append,List.map_cons] using h
    simpa using H.flips l r _ _ p false hv hu (unitMark H)
  let t:=T.parity v
  have hz: T.parity t=v:=T.even hK v
  let k :ℂ:=2⁻¹
  let b:= k • (v+t)
  let a:= k • (v-t)
  have hsum: b+a=v:=by
    unfold b a; rw [←smul_add, show v+t+(v-t)= (2:ℂ) • v from by -- force scalar
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num [k]
  have ha: tone (l++(x,a)::(y,(lampU P K))::r)=tone (l++ (y,(lampU P K))::(x,a)::r):=he a true (show T.parity a = -a from by
       unfold a t k at *; rw [map_smul, map_sub,hz, show T.parity v - v= -(v-T.parity v) from by abel, smul_neg])
  have hb: tone (l++(x,b)::(y,(lampU P K))::r)=tone (l++ (y,(lampU P K))::(x,b)::r):= he b false (show T.parity b=b from by
       unfold b; rw [map_smul,map_add,hz]; congr 1; exact add_comm ..)
  have eq (u:K.W): l++ (y,(lampU P K))::(x,u)::r = (l++[(y,(lampU P K))]) ++ (x,u)::r := by simp
  conv_lhs => rw [← hsum,add_point]
  conv_rhs => rw [eq,← hsum,add_point,←eq,←eq]
  rw [ha,hb]

lemma unit_point (hK:K.Domestic)(H:Foil P K T)(l r:Strip K)(x:E4)(h: Strip.distinct (l++(x,(lampU P K))::r)): tone (l++(x,(lampU P K))::r)=tone (l++r):=by
  induction l using List.reverseRecOn generalizing r with
  | nil => simpa using unit_first H r x (by simpa using h)
  | append_singleton l a ih =>
    obtain ⟨y,v⟩:=a
    simp only [List.append_assoc,List.cons_append, List.nil_append] at *
    rw [unit_steps hK H l r y x v h]; apply ih
    rw [spots _] at *; exact ((List.Perm.append_left l (List.Perm.swap _ _ _)).map Prod.fst).nodup h

end YM.Massive.Gust
#print axioms YM.Massive.Gust.unit_point
