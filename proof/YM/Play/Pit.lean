import YM.Play.Perlite
import YM.Play.Trill
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I K A B G E: Type}
namespace Chamber
local notation "H"=> Finset I
section foray
variable [CommRing K](f:Finset I→K) -- replace explicit
lemma fieldH {p:H}(X Y:H) (hp:Disjoint X Y)(hz:(∀ i⊆p,¬i⊆ X → ¬i⊆ Y →f i=0))(h:p⊆ X∪Y): parties f p= parties f (p∩X)*parties f (p∩Y):=by
   let U:=p∩X; let V:=p∩Y; have hU:U⊆ X:=inter_subset_right; have hV:V⊆ Y:=inter_subset_right
   have he:Disjoint U V:= hp.mono hU hV; have ht: U∪V=p:=by rw [show U∪V=p∩(X∪Y) from (inter_union_distrib_left ..).symm,inter_eq_left.mpr h]
   let u:=registry U; let v:=registry V; let C:= u×ˢ v; let g(i: Finset H × Finset H):=i.1∪i.2
   have h₁ i (hi:i∈C): Disjoint i.1 i.2:=by
       obtain ⟨h1,h2⟩:=mem_product.mp hi; apply Finset.disjoint_left.mpr; intro k hk hk₁; obtain ⟨w,hw⟩:=(member h1 hk).1; exact Finset.disjoint_left.mp he ((member h1 hk).2 hw) ((member h2 hk₁).2 hw)
   have h₂(i)(hi:i∈C): g i∈registry p:=by
       obtain ⟨u,v⟩:=i; obtain ⟨hu,hv⟩:=mem_product.mp hi; obtain ⟨h1,h2,h3,h4⟩:=mem_filter.mp hu; obtain ⟨h5,h6,h7,h8⟩:=mem_filter.mp hv
       refine mem_filter.mpr ⟨?_,fun h=> mem_union.mp h |>.elim h2 h6,?_ ,?_⟩
       · apply mem_powerset.mpr; intro i hi; rcases mem_union.mp hi with h|h; exact mem_powerset.mpr ((member hu h).2.trans inter_subset_left); exact mem_powerset.mpr ((member hv h).2.trans inter_subset_left)
       · change (u∪v).biUnion id=p; rw [Finset.union_biUnion,h3,h7,ht]
       intro i hi j hj hh; rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
       · exact h4 hi hj hh
       · exact he.mono (member hu hi).2 (member hv hj).2
       · exact he.symm.mono (member hv hi).2 (member hu hj).2
       exact h8 hi hj hh
   have hf {u v:H}{p q:Finset H}(hU:p∈registry u)(hV:q∈registry v)(h:Disjoint u v): p=(p∪q).filter fun i=> i⊆u:=by
       ext i; constructor
       · intro hi; exact mem_filter.mpr ⟨mem_union_left _ hi, (member hU hi).2⟩
       intro hi; obtain ⟨hx,hp⟩:= mem_filter.mp hi; rcases mem_union.mp hx with he|he; exact he
       obtain ⟨x,hx⟩:=(member hV he).1; exact False.elim (Finset.disjoint_left.mp h (hp hx) ((member hV he).2 hx))
   have hg : Set.InjOn g C:=by
       rintro ⟨b,c⟩ hh ⟨d,e⟩ he' ht
       change b∪c=d∪e at ht; obtain ⟨hb,hc⟩:=mem_product.mp hh; obtain ⟨hd,hh⟩:=mem_product.mp he'; exact Prod.ext ((hf hb hc he).trans ((congr_arg (filter (fun i:H=> i ⊆ U)) ht).trans (hf hd hh he).symm)) ( (hf hc hb he.symm).trans ((congr_arg (filter (fun i:H=> i⊆ V)) (show c∪b=e∪d from (union_comm ..).trans (ht.trans (union_comm ..)))).trans (hf hh hd he.symm).symm))
   have hJ (i:Finset H)(hi:i∈registry p)(hx:∏ j∈i,f j ≠0): i∈ C.image g:=by
       have h' j (hj:j∈i): j⊆ X ∨ j⊆ Y:= by by_contra! h; exact hx (prod_eq_zero hj (hz j (member hi hj).2 h.1 h.2))
       let a (U:H):= i.filter fun j=> j ⊆ p∩U
       have hK {X' Y':H} (hD:Disjoint X' Y')(hk:∀ j∈i,j⊆X' ∨ j⊆Y'): a X'∈registry (p∩ X'):=by
          let v:=p∩X'; let P:=a X'; obtain ⟨h1,h2,h3,h4⟩:=mem_filter.mp hi; refine mem_filter.mpr ⟨mem_powerset.mpr (fun j hj=> mem_powerset.mpr (mem_filter.mp hj).2),fun h=>h2 (mem_filter.mp h).1, Finset.ext fun j=>?_,?_⟩
          · constructor
            · intro ht; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp ht; exact (mem_filter.mp hk).2 hj
            intro hh; obtain ⟨k,hk',hj⟩:= mem_biUnion.mp (h3.symm ▸ (mem_inter.mp hh).1); rcases hk k hk' with h|h; · exact mem_biUnion.mpr ⟨k,mem_filter.mpr ⟨hk', subset_inter (member hi hk').2 h⟩,hj⟩
            exact False.elim (Finset.disjoint_left.mp hD (mem_inter.mp hh).2 (h hj))
          exact Set.Pairwise.mono (coe_subset.mpr (filter_subset _ _)) h4
       refine mem_image.mpr ⟨(a X,a Y),mem_product.mpr ⟨hK hp h', hK hp.symm (fun j hj=> (h' j hj).symm)⟩,?_⟩; ext j; refine ⟨fun h=> mem_union.mp h |>.elim (fun hi=> (mem_filter.mp hi).1) (fun hi=>(mem_filter.mp hi).1),fun hh=>?_⟩; rcases h' j hh with he|he; exact mem_union_left _ (mem_filter.mpr ⟨hh,subset_inter (member hi hh).2 he⟩); exact mem_union_right _ (mem_filter.mpr ⟨hh,subset_inter (member hi hh).2 he⟩)
   unfold parties; conv_lhs=> rw [← sum_subset (show C.image g⊆registry p from (image_subset_iff.mpr (fun i hi=> h₂ i hi))) (fun i hi h=>by_contra (fun h'=> h (hJ i hi h'))), Finset.sum_image hg]
   rw [Finset.sum_mul_sum, show C=u×ˢv from rfl, Finset.sum_product]; apply sum_congr rfl; intro i hi; refine sum_congr rfl fun j hj => prod_union (f:=f) (h₁ (i,j) (mem_product.mpr ⟨hi,hj⟩))
lemma quietV {p:H}(X Y:H) (h:p⊆ X∪ Y)(hp:Disjoint X Y)(hz:∀ i⊆p,f i=f (i ∩ X)*f (i∩Y))(hF:f ∅=1) (hX:¬p⊆X)(hY:¬p⊆Y): cetacea f p=0:=by
   let g i:= if i⊆X ∨ i⊆Y then cetacea f i else 0; have hh : g ∅=0:=by rw [show g ∅=_ from if_pos (show ∅⊆X ∨ ∅⊆ Y from Or.inl (empty_subset _)),cet]; simp
   have hA (i) (hv: i⊆X ∨ i⊆Y):parties g i=parties (cetacea f) i:= sum_congr rfl fun j hj=>prod_congr rfl fun k hk=>if_pos (hv.imp (fun h=> (member hj hk).2.trans h) (fun h=> (member hj hk).2.trans h))
   have hv v (hi:v⊆p): parties g v=f v:=by rw [fieldH g X Y hp (fun j hj hz hw=> if_neg (not_or.mpr ⟨hz,hw⟩)) (hi.trans h), hA _ (Or.inl inter_subset_right),hA _ (Or.inr inter_subset_right), carries f _ hF,carries f _ hF]; exact (hz v hi).symm
   exact Eq.trans (only f g p hv hh p (Subset.refl _)).symm (if_neg (not_or.mpr ⟨hX,hY⟩))
end foray
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.quietV
