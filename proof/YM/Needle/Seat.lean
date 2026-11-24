import YM.ValeK.Harmony
import YM.Infer.Trinity
import YM.Alum.Fables
import YM.Alum.Arbor
/-!
  A budget envelope invariant for arbitrary parities. Always in terms of
  authentic lattice measurements on the same branch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub
open Finset
open scoped Topology ContDiff BigOperators Classical
variable {n : Side}(R:Regulator n 6) (T:Tiling n) (p:T.Cell)
abbrev Gold (X:Insertion n 6)(c:ℝ):Prop:=∃ (k:ℕ)(f:Fin k→Insertion n 6), ∑ i,f i = X ∧ (∀ i,Fence (T.chamber p) (f i) ∧ Potion (f i)) ∧ ∑ i,topH T R (f i) p ≤ c
variable {T R p}
lemma coin {x:Insertion n 6}(h:Fence (T.chamber p) x)(hx:Potion x):Gold R T p x (topH T R x p):=by refine ⟨1,fun _=>x,by simp,fun _=>⟨h,hx⟩,by simp⟩
namespace Gold
variable {K C:ℝ}{x y:Insertion n 6}(h:Gold R T p x K)
include h
lemma mono (he:K≤ C): Gold R T p x C:=by obtain ⟨_,_,h',he',hX⟩:=h; exact ⟨_,_,h',he',hX.trans he⟩
lemma nonneg : 0 ≤ K:=by obtain ⟨_,_,_,_,he⟩:=h; exact (sum_nonneg (fun i _=>top_nn ..)).trans he
lemma together (h':Gold R T p y C):Gold R T p (x+y) (K+C):=by
   obtain ⟨l,f,rfl,h1,h2⟩:= h; obtain ⟨k,g,rfl,h3,h4⟩:=h'; let F:= Fin.append f g
   refine ⟨l+k,F,?_,?_,?_⟩
   · rw [Fin.sum_univ_add]; simp [F]
   · intro i; induction i using Fin.addCases <;> simp only [F, Fin.append_left,Fin.append_right] <;> first|apply h1 | apply h3
   rw [Fin.sum_univ_add]; simp only [F,Fin.append_left,Fin.append_right]; exact add_le_add h2 h4
lemma minted (a:ℂ): Gold R T p (a • x) (‖a‖*K):=by
   obtain ⟨k,f,rfl,hx,hV⟩:=h; let g(i: Fin k):=a • f i
   refine ⟨k,g,(smul_sum ..).symm, fun i=>⟨(hx i).1.mass _,potscaling (hx i).2 _⟩,?_⟩
   simp_rw [show ∀ i,topH T R (g i) p=‖a‖*topH T R (f i) p from fun i=> top_spin T R p (f i) a]
   rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hV (norm_nonneg _)
omit h
lemma nil : Gold R T p 0 0:=by exact ⟨0,0,by simp,fun i=> Fin.elim0 i,by simp⟩
lemma sack {I:Type*}(s:Finset I)(x:I→Insertion n 6)(v:I→ℝ)(hp:∀ i∈s,Gold R T p (x i) (v i)):Gold R T p (∑ i∈s,x i) (∑ i∈s,v i):=by
    induction s using Finset.induction_on with |empty=>simp only [sum_empty]; exact nil| insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact together (hp a (mem_insert_self ..)) (ih fun i h=>hp i (mem_insert_of_mem h))
set_option maxHeartbeats 400000 in
lemma value {k:ℕ}(p:Fin k→T.Cell)(hp:Injective p)(f:Fin k→Insertion n 6)(v:Fin k→ℝ)(hX:∀ i,Gold R T (p i) (f i) (v i))(ht:T.kind=.link)(hr:R.t=0)(hb:0≤ R.β)(hP:4≤ n.val)(hZ:R.Z≠0): ‖R.average (List.ofFn f).prod‖ ≤ ∏ i,v i:=by
   choose N g hf hg h using hX; let G:=MultilinearMap.mkPiAlgebraFin ℂ k (Insertion n 6); let W(i:Fin k)(j:Fin (N i)):=topH T R (g i j) (p i)
   let F(a:(i:Fin k)→Fin (N i))(i:Fin k):=g i (a i)
   have he :(List.ofFn f).prod= ∑ a:(i:Fin k)→Fin (N i), (List.ofFn (F a)).prod:=by
       rw [←MultilinearMap.mkPiAlgebraFin_apply (R:=ℂ)]; change G f= ∑ a, G (F a); conv_lhs=>rw [show f=(fun i=>∑ j,g i j) from funext fun _=> (hf _).symm]; exact G.map_sum g
   have hm(a:(i:Fin k)→Fin (N i)): ‖R.average (List.ofFn (F a)).prod‖ ≤ ∏ i,W i (a i):=by
       rw[List.ofFn_eq_map, Goblet.knownV]; let X(i:Fin k): Stud n 6:=↑(F a i);
       have he(l:List (Fin k)): ⇑(l.map (F a)).prod=(l.map X).prod:=by induction l with | nil=>rfl| cons i l ih=> simp only [List.map_cons,List.prod_cons, ContinuousMap.coe_mul]; rw [ih]
       rw [he]; exact wardsP T R ht X p hp (List.finRange k) (List.nodup_finRange k) List.mem_finRange (fun i=> hg i (a i)) hr hb hP hZ
   rw [he,map_sum]
   exact (norm_sum_le ..).trans ((sum_le_sum (fun a _=>hm a)).trans ((Fintype.prod_sum _).symm.le.trans (prod_le_prod (fun _ _=> sum_nonneg (fun _ _=>top_nn ..)) (fun i _=>h i))))
end Gold
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Gold.value
