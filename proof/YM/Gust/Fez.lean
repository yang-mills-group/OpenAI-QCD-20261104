import YM.Gust.Opu
set_option maxHeartbeats 590000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n:ℕ}(a:Axis)
structure Marque (T:Pollens P K) where
    x:E4
    p:K.W
    q:Bool
    h:p∈Col T q
namespace Marque
variable (p: List (Marque T))
abbrev lands :Strip K:=p.map fun i=>(i.x,i.p)
abbrev grades: ℂ:= (p.map fun i=>tauMod i.q).prod
abbrev Visible(p:Gala T n):=∀ i:Fin n,tone (wall p i.succ) ≠ 0
lemma grades_plus (u:List (Marque T)): grades (p++u)=grades p*grades u:=by simp [grades]
lemma discover (hg:grades p= -1): ∃ x:Marque T,∃ u v,p=u++x::v ∧ x.q=true ∧ grades (u++v)=1:=by
       induction p with
       | nil=>simp[grades] at hg; norm_num at hg
       | cons t l ih=> cases h:t.q
                       · obtain ⟨x,u,v,h1,hq,h2⟩:= ih (by simpa [grades,h,tauMod] using hg); refine ⟨x,t::u,v,by rw[h1,List.cons_append],hq,?_⟩; rw[List.cons_append,grades]; simp only[List.map_cons,List.prod_cons,h, show tauMod false=1 from rfl,one_mul]; exact h2
                       · refine ⟨t,[],l,(List.nil_append _).symm,h,?_⟩; change tauMod t.q*grades l= -1 at hg; rw [h,show tauMod true= -1 from rfl,neg_one_mul, neg_inj] at hg; exact hg
lemma organized {p q: Strip K} (l:Gala T n)(h:wall l 0=p++q):∃ V W:Gala T n,l=V++W∧wall V 0=p∧wall W 0=q:=by
       let V := l.take p.length; let W:= l.drop p.length; have he: V.length=p.length:=by dsimp[V]; rw [List.length_take]; have hx:= congr_arg List.length h; simp [wall] at hx; omega
       have hh:l=V++W:= (List.take_append_drop ..).symm; have hP:wall V 0++wall W 0=p++q:=by rw [←h, hh]; unfold wall; rw[List.map_append] -- List.map_append
       have hz:p.length=(wall V 0).length:=by simp [wall,he]
       exact ⟨V,W,hh,List.append_inj_left hP hz.symm,List.append_inj_right hP hz.symm⟩
-- extend pair separated.Sturdy. poly Ep.Phys.
variable {b:Bool}(x y:Marque T) (U W:List (Marque T)) (L V: Gala T n)
include hK hf
lemma pairsR (hh:x.q=true)(ht:y.q=true)(h:Strip.distinct (lands (x::(U++y::W))))(hp:∃ u,x.x=pet a u)(hz:∃ u,y.x=pet a u)(hn:x.p≠0)(hL:wall L 0=lands U)(hV:wall V 0=lands W)(he_old:Visible (L++V)) : ∃ R: Gala T (n+1), wall R 0=lands (x::(U++y::W))∧Visible R:=by
       have hx:x.x≠y.x:=by
              intro he; have hx:= (spots _).1 h; simp only[lands,List.map_cons,List.map_append,List.nodup_cons] at hx; exact hx.1 (by simp[he])
       obtain ⟨i,hi⟩:=hp; obtain ⟨j,hj⟩:=hz
       let t:=x.p; have ht0:t∈ Col T true:= hh ▸ x.h; obtain ⟨u,hu,w,hw,hz⟩:= hero hK hf a t ht0 hn _ _ _ _ hi hj hx
       let E:= occupy hf n t u ht0 hu; let D:= occupy hf n y.p w (ht ▸ y.h) hw; let L':= pour hf L; let V':=pour hf V; let R:Gala T (n+1):= (x.x,E):: (L'++ (y.x,D)::V'); have hℓ: wall R 0=lands (x::(U++y::W)) :=by
              have h0: wall L' 0=lands U:=by unfold L'; rw[pour_seed,hL] -- rw local zeta
              have h1: wall V' 0=lands W:=by unfold V'; rw[pour_seed,hV]
              unfold R lands; rw[List.map_cons,List.map_append,List.map_cons, show wall ((x.x,E):: _) _=(x.x,x.p):: (wall L' 0++ (y.x,y.p)::wall V' 0) from ?_,h0,h1]
              unfold wall; rw[List.map_cons,List.map_append,List.map_cons]; rfl
       refine ⟨R,hℓ,fun i=>?_⟩; have hr: Piers R:=by rw[←hℓ] at h; simpa only[wall,Piers,List.map_map,Function.comp_def] using (spots _).1 h
       induction i using Fin.cases with
       | zero=>
             let i:= (0:Fin (n+1)).succ; have hR:= length_ok R hr i; let P':=wall L' i; let Q':=wall V' i; have hh: wall R i= [(x.x,u)]++ (P' ++ [(y.x,w)])++Q':=by unfold R wall; rw[List.map_cons,List.map_append,List.map_cons]; rw[List.append_assoc,List.append_assoc]; rfl -- `P'++[(y)]` ..
             change tone (wall R i)≠0; rw [hh] at hR; simp only[List.append_assoc,List.append_nil,List.cons_append,List.nil_append] at hR; obtain ⟨hs,H⟩:= throwU hK hf [(x.x,u)] P' ((y.x,w)::Q') (pour_unit hf L) hR; obtain ⟨-,hB⟩:=throwU hK hf [(x.x,u),(y.x,w)] Q' [] (pour_unit hf V) (by simp; exact hs)
             have heq:tone (wall R i)=tone [(x.x,u),(y.x,w)]:=by rw [hh,List.append_assoc,List.append_assoc]; refine H.trans ?_; simpa only[List.cons_append,List.nil_append,List.append_nil] using hB
             exact heq ▸ hz
       | succ i=>
             let j:=i.succ.succ; have he : wall R j=(x.x,lampU P K)::(wall L i.succ ++ (y.x,lampU P K)::wall V i.succ):=by
                    rw[← pour_grown hf L i,← pour_grown hf V i]; unfold R wall; rw[List.map_cons,List.map_append,List.map_cons]; rfl
             have hp:=length_ok R hr j; rw [he] at hp
             change tone (wall R j)≠0; rw[he,unit_first hf _ _ hp,unit_point hK hf _ _ _ ((Tarn.Choir.Strip.fresh _ hp))]; have hz:= he_old i; unfold wall at *; rwa[List.map_append] at hz

end Marque
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Marque.pairsR
