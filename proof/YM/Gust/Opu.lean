import YM.Gust.Empt
import YM.Gust.TopP
set_option maxHeartbeats 710000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n:ℕ}(a:Axis)
local notation "Ω"=>lampU P K
lemma tone_two (x y:E4)(u v:K.W): tone [(x,u),(y,v)]= K.total _ (points (![x,y])) (![u,v]):=by
     let X:= points (![x,y]); let p:= (![u,v]); rw [show [(x,u),(y,v)]=grove K p X from ?_, grooved]; unfold grove; rw[List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]; rfl
variable (t:K.W)(hw:t∈Col T true)(hy:t≠0)
include hK hf hw hy
lemma hero (x y:E4)(u v:ℝ)(hx:x=pet a u)(hh:y=pet a v)(hX:x≠y):∃ p∈Col T true,∃ q∈Col T true,tone [(x,p),(y,q)]≠0:=by
     have h:u≠v:=fun he=>hX (hx.trans ((congr_arg (pet a) he).trans hh.symm)); subst x; subst y
     obtain h|h:=h.lt_or_gt; · refine ⟨_,litWay T hK a true hw,_,hw,?_⟩; rw [tone_two,unitPair hf a t u v h]; exact credible hK hf a t (sub_pos.mpr h) hy
     refine ⟨_,hw,_,litWay T hK a true hw,?_⟩
     let z:= T.adj a t; let X:= pet a u; let Y:= pet a v; have hg(p:K.W)(hp:p∈Col T true):markedW T true p:=by rw[markedW,(hue ..).1 hp]; simp[tauMod]
     have he: tone [(X,t),(Y,z)]= -tone [(Y,z),(X,t)]:=by simpa using hf.flips [] [] (X,t) (Y,z) true true ((spots _).mpr (by simp [hX,X,Y])) (hg t hw) (hg _ (litWay T hK a true hw))
     change tone [(X,t),(Y,z)]≠0; rw [he]; exact neg_ne_zero.mpr (by rw [tone_two]; exact (unitPair hf a t v u h).symm ▸ credible hK hf a t (sub_pos.mpr h) hy)
omit hK hf hw hy
variable (v z:Gala T n)
noncomputable def add_o(u:Mater T n): Mater T (n+1) :=
   { u:= u.u.map Fin.succ
     v:= Fin.cons (u.v 0) (Fin.cons Ω (fun i=>u.v i.succ))
     mem :=by
            intro j; induction j using Fin.cases with
            | zero=> simpa only [q,Fin.cases_zero,Fin.cons_zero,Option.isSome_map] using u.mem 0
            | succ j=> induction j using Fin.cases with
                       | zero=> have he:Kind.q (Option.map Fin.succ u.u) ((0:Fin (n+1)).succ)=false:=by cases u.u <;> simp only [q,Fin.cases_succ,Option.map_some,Option.map_none] <;> simp [Ne.symm (Fin.succ_ne_zero _)]
                                rw[he]; exact coinP hf
                       | succ j=> have he:q (Option.map Fin.succ u.u) j.succ.succ=q u.u j.succ:=by cases u.u <;>simp[q]
                                  rw [he]; exact u.mem j.succ }
noncomputable def pour (v:Gala T n): Gala T (n+1):= v.map fun x=>(x.1,add_o hf x.2)
include hf
lemma pour_app: pour hf (v++z)= pour hf v++pour hf z:=by simp only [pour,List.map_append]
lemma pour_seed: wall (pour hf v) 0= wall v 0:=by simp [wall,pour,add_o,List.map_map,comp_def]
lemma pour_grown (i:Fin n): wall (pour hf v) i.succ.succ=wall v i.succ:=by simp [wall,pour,add_o,List.map_map,comp_def]
lemma pour_unit : ∀ x∈ wall (pour hf v) ((0:Fin (n+1)).succ),x.2=Ω:=by
       intro p hp; unfold wall pour at hp; rw[List.map_map] at hp; obtain ⟨x,h,rfl⟩:= List.mem_map.mp hp; rfl
omit hf
noncomputable def occupy (n:ℕ)(x y:K.W)(hx:x∈Col T true)(hy:y∈Col T true): Mater T (n+1) where
     u:=some 0
     v:= Fin.cons x (Fin.cons y (fun _=>Ω))
     mem i:=by
          induction i using Fin.cases with
          | zero=> exact hx
          | succ i=> induction i using Fin.cases with
                     | zero=> exact hy
                     | succ i=> simp only [q,Fin.cases_succ,Fin.cons_succ]; rw [show decide _=false from ?_]; exact coinP hf; simp
include hK hf
lemma throwU (U:Strip K)(L v:Strip K)(h:∀ x∈L,x.2=lampU P K)(hh:Strip.distinct (U++ (L++v))): Strip.distinct (U++v) ∧ tone (U++(L++v))=tone (U++v):=by
        induction L with
        | nil=> simpa using hh
        | cons p q ih=>
             rcases p with ⟨x,w⟩; have he:w=lampU P K:=h (x,w) List.mem_cons_self; subst w
             rw [List.cons_append] at hh ⊢; rw [unit_point hK hf _ _ _ hh]; apply ih (fun i hi=> h _ (List.mem_cons_of_mem _ hi)); rw[spots] at hh ⊢; exact ((List.Sublist.map Prod.fst ((List.sublist_cons_self ..).append_left _))).nodup hh
omit hK hf
end YM.Massive.Gust
#print axioms YM.Massive.Gust.pour_grown
#print axioms YM.Massive.Gust.occupy
#print axioms YM.Massive.Gust.hero
