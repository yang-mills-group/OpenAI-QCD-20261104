import YM.Siro.Jason
import YM.Ward.Axis
set_option maxHeartbeats 570000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Ward (inc Latest Earliest)
open Fields (SimpleK homogeneous distinct pointMoment)
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators Classical
variable {F:Fields}{a b:Axis}{S:F.Kernel}(V:Chamber S a)(H:Brawl S)
include V H
local notation "κ"=> F.W
lemma happ (x:E4)(b:Axis)(v:Cluster F)(p:F.W)(hx:distinct v)(s:ℝ)(h:∀ z∈v,z.1 a< inc b x s a) : AnalyticAt ℝ (fun t=> pointMoment S (v ++ [(inc b x t,p)])) s:=by
  have he : ∀ᶠ r : ℝ in 𝓝[<] (inc b x s a), ∀ i ∈ v, i.1 a < r := by
    have hg i (hi : i∈v) : ∀ᶠ r : ℝ in 𝓝[<] (inc b x s a), i.1 a<r :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds (h i hi))
    simpa using (eventually_all_finset v.toFinset).mpr (fun i hi => hg i (by simpa using hi))
  obtain ⟨k,hk,hb⟩ := (he.and self_mem_nhdsWithin).exists; let w := -(k • basis a)
  have hF:Positive (reflect (carry v w) a) a:=by
      refine ⟨reflects a (still hx _),fun z hz=>?_⟩; rw[reflectedPoint,List.mem_map] at hz; obtain ⟨r,hr,rfl⟩:=hz; rw[List.mem_reverse] at hr; obtain ⟨u,hu,rfl⟩:= List.mem_map.mp hr; simp[w,Signed.mirrored]; linarith [hk _ hu]
  let i: Future F a:=⟨_,hF⟩; let y:=x+w; let t(s:ℝ):= inc b y s; have hh r:t r=inc b x r+w:=by unfold t y inc; abel
  have hp : 0< t s a :=by rw[hh]; change k < inc b x s a at hb; simpa[w,inc] using hb
  apply (((innerSL ℂ (V.GNS.plant i)).restrictScalars ℝ |>.analyticAt _).comp (show AnalyticAt ℝ (fun r=>spotR V p (t r)) s from ?_)).congr
  · have hy : Continuous t:= continuous_const.add (continuous_id.smul continuous_const); have hw:Continuous (fun z=>t z a):= (EuclideanSpace.proj (𝕜:=ℝ) a).continuous.comp hy
    filter_upwards [hw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with r hr
    have H_d: distinct (v++[(inc b x r,p)]) :=by
                rw [locations,List.map_append,List.nodup_append]; refine ⟨locations.mp hx,by simp,?_⟩; intro z hz z' h' hh'; have he : z'=inc b x r:=by simpa using h'
                obtain ⟨c,hc,hζ⟩:=List.mem_map.mp hz; have hm:= hk c hc; change 0<t r a at hr; rw [hh] at hr; simp [w] at hr; rw [hζ, hh', he] at hm; simp [inc] at hm; exact hm.not_ge hr.le
    change inner ℂ (V.GNS.plant i) (spotR V p (t r))= _; rw [stamp V _ hr, V.GNS.measure,← invariance H.toSimpleK H_d w]; change pointMoment S (reflect (reflect (carry v w) a) a ++ [(t r,p)])=_; rw[reflect_twice a (H.adj_flip _),hh]; congr 1; simp [carry]
  by_cases ha:b=a
  · subst b; exact advancing V p y s hp
  have ht:0<y a:=by simpa [t,inc,Ne.symm ha] using hp
  exact cared V H p y ht ha s
omit V H
-- multilinearity in one v all counting
lemma addOne(l r:Cluster F)(x:E4)(u v:F.W): pointMoment S (l++(x,u+v)::r)=pointMoment S (l++(x,u)::r)+pointMoment S (l++(x,v)::r):=by
  let i : Fin (l.length + (r.length+1)):= ⟨l.length,by omega⟩
  let q: Points (l.length+(r.length+1)):= points (Fin.append (positions l).ofLp (Points.cons x (positions r)).ofLp)
  let z : Fin (l.length+(r.length+1)) → F.W:= Fin.append (tokens l) (Fin.cons 0 (tokens r))
  have e (v:F.W): l++(x,v)::r = realize (update z i v) q:=by
    rw [realize]
    let j := Fin.append l.get ((x,v)::r).get
    have hh : (fun k=> (q k,update z i v k))=j:=by
      funext k
      refine Fin.addCases (fun k=>?_) (fun k=>?_) k
      · have he: k.castAdd _ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_castAdd] at HH; omega
        rw [update_of_ne he,show j (Fin.castAdd (r.length+1) k)=l.get k from Fin.append_left l.get ((x,v)::r).get k]; simp only [Fin.append_left,q,z,points_apply]; rfl
      refine Fin.cases ?_ ?_ k
      · rw [show Fin.natAdd _ 0=i from Fin.ext (by simp [i]),update_self]; change (q (Fin.natAdd l.length 0),v)= j (Fin.natAdd l.length 0); simp [j,q,Points.cons]
      intro a
      have he: Fin.natAdd l.length a.succ ≠ i:=by intro h; have HH:=congr_arg Fin.val h; simp only [i,Fin.val_natAdd,Fin.val_succ] at HH; omega
      rw [update_of_ne he, show j _=r.get a from (Fin.append_right ..).trans (by change ((x,v)::r).get a.succ=r.get a;rfl)]
      simp only [Fin.append_right,q,z,Points.cons,Fin.cons_succ,points_apply]; rfl
    rw [hh]; unfold j
    rw [List.ofFn_fin_append,List.ofFn_get,List.ofFn_get]
  rw [e,e u,e v,readAt,readAt,readAt,MultilinearMap.map_update_add]
include V H
lemma mild(x:F.W):∃ p q:F.W,p+q=x∧ F.homogeneous false p∧F.homogeneous true q:=by
     let c:ℂ:=2⁻¹; have h:= H.parity₂ x
     refine ⟨c • (x+F.parity x),c • (x-F.parity x),?_,?_,?_⟩
     · rw[← smul_add,show x+F.parity x+(x-F.parity x)= (2:ℂ) • x from by rw[two_smul]; abel,smul_smul]; norm_num [c]
     · change F.parity _=_; rw[map_smul,map_add,h,add_comm]
     change F.parity _= -_; rw [map_smul,map_sub,h,←smul_neg, neg_sub]
lemma ports(x:E4)(b:Axis)(l r:Cluster F)(p:F.W)(q:Bool)(hq:F.homogeneous q p)(s:ℝ)(hx:distinct (l++r))(h:∀ y∈l++r,y.1 a< inc b x s a): AnalyticAt ℝ (fun t=> pointMoment S (l++(inc b x t,p)::r)) s:=by
     induction r generalizing l with
     | nil=> exact happ V H x b l p (by simpa using hx) s (by simpa using h)
     | cons i r ih=>
          obtain ⟨y,v⟩:=i; let f(t:E4 × F.W):E4:=t.1
          have he(i:F.W)(c:Bool)(hc:F.homogeneous c i):AnalyticAt ℝ (fun t=> pointMoment S (l++(inc b x t,p)::(y,i)::r)) s:=by
                 have hx' : distinct ((l++[(y,i)])++r):=by rw[locations] at *; simpa [List.append_assoc] using hx
                 have hh :∀ z∈ (l++[(y,i)])++r,z.1 a< inc b x s a:=by
                        intro z hz; simp only[List.append_assoc,List.cons_append,List.nil_append,List.mem_append,List.mem_cons] at hz; rcases hz with hz|he|hz
                        · exact h z (List.mem_append_left _ hz)
                        · subst z; exact h (y,v) (by simp)
                        exact h z (by simp [hz])
                 refine ((show AnalyticAt ℝ (fun t:ℝ=> if q && c then (-1:ℂ) else 1) s from analyticAt_const).mul (ih (l++[(y,i)]) hx' hh)).congr (g:=fun t=>pointMoment S (l++(inc b x t,p)::(y,i)::r)) ?_
                 have ht (k: E4 × F.W)(hk:k∈(l++[(y,i)])++r): ∀ᶠ r:ℝ in 𝓝 s,k.1 a< inc b x r a :=by
                       have hw:Continuous fun u:ℝ=> inc b x u a:= (EuclideanSpace.proj (𝕜:=ℝ) a).continuous.comp (continuous_const.add (continuous_id.smul (continuous_const (y:=basis b)))); exact hw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (hh _ hk))
                 filter_upwards [(eventually_all_finset (((l++[(y,i)])++r).toFinset)).mpr (fun i hi=> ht i (by simpa only[List.mem_toFinset] using hi))] with t hT
                 have H' : distinct (l++(inc b x t,p)::(y,i)::r):=by
                           rw [locations]; have hp:List.Perm (l++(inc b x t,p)::(y,i)::r) ((inc b x t,p)::((l++[(y,i)])++r)):=by
                                      rw[List.append_assoc,List.cons_append,List.nil_append]; apply List.perm_middle -- signature
                           apply (hp.symm.map Prod.fst).nodup; rw [List.map_cons,List.nodup_cons]; refine ⟨?_,locations.mp hx'⟩; simp only[List.mem_map]; rintro ⟨z,hz,hh⟩; have hh' := hT z (by simpa only[List.mem_toFinset] using hz); rw[hh] at hh'; exact lt_irrefl _ hh'
                 simpa only[List.append_assoc,List.cons_append,List.nil_append,Pi.mul_apply] using (H.swap l r _ _ H' _ _ hq hc).symm
          obtain ⟨u,w,H₀,H₁,H₂⟩:= mild V H v
          apply ((he u false H₁).add (he w true H₂)).congr
          refine Eventually.of_forall fun t=>?_ ; dsimp only [Pi.add_apply]
          let z:Plant F:= (inc b x t,p); have hv(i:F.W):l++z::(y,i)::r=(l++[z])++(y,i)::r:=by simp
          rw [← H₀]; simp_rw [show ∀ i:F.W,l++(inc b x t,p)::(y,i)::r=(l++[z])++(y,i)::r from hv, addOne (S:=S) (l++[z])]
lemma whole(x:E4)(b:Axis)(l r:Cluster F)(p:F.W)(s:ℝ)(hx:distinct (l++r))(h:∀ y∈l++r,y.1 a< inc b x s a): AnalyticAt ℝ (fun t=> pointMoment S (l++(inc b x t,p)::r)) s:=by
     obtain ⟨v,w,hv,h₁,h₂⟩:=mild V H p; refine ((ports V H _ _ _ _ _ _ h₁ _ hx h).add (ports V H _ _ _ _ _ _ h₂ _ hx h)).congr ?_; exact Eventually.of_forall (fun t=>by dsimp only[Pi.add_apply]; rw[←hv, addOne])
end YM.Massive.Siro
#print axioms YM.Massive.Siro.whole
