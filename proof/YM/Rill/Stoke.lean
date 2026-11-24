import YM.Rill.Panel
/-! Word in centre slots all elevated, external lists.Favourable pitches. No order or shapes assumed beyond actual measurements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir} {β e:ℝ} {φ:ℕ→ℕ}(hp:C.Path β e) (H:Q.Harmony P φ) (hφ:Tendsto φ atTop atTop)
abbrev TileV(Q: Choir):= E4 × Q.W
abbrev gap (l: Strip Q)(r:ℝ):= l.Pairwise (fun x y:TileV Q=> r < dist x.1 y.1)
variable {I J:Type}[Fintype I][Fintype J]
include hp H hφ
private lemma solo (l:List (Bool × TileV Q))(r:Bool→ℝ)(x:I→ E4)(z:J→E4)(j ℓ:ℕ)(hj:j+1≤ℓ)(hC:Fintype.card I*8< (C.S.step j).L.val)(hb:Fintype.card J*6<(C.S.step ℓ).L.val)(hg: l.Pairwise (fun t s=> (4*C.S.spacing ℓ<dist t.2.1 s.2.1)∧ (t.1||s.1→4*C.S.spacing j<dist t.2.1 s.2.1)))(hk:∀ i∈l,i.1=true→∃ t:I,Scan C j (x t) i.2.1)(ht:∀ i∈l,i.1=false→∃ u:J,i.2.1=z u)(hv:∀ i∈l,Privilege P Q (if i.1 then j else ℓ) i.2.2 (r i.1)):‖Strip.tone (l.map Prod.snd)‖≤ (l.map fun k=>r k.1).prod:=by
    rw [show Strip.tone (l.map Prod.snd) = _ from (introduces (Q:=Q) (x:=fun i:Bool× TileV Q=> i.2.1) (s:=fun i=> i.2.2) l)]
    let p:=fun i=> l.get i; let c(i):= r (p i).1; let b(i):=(p i).1; have h:(l.map fun k=>r k.1).prod= ∏ i,c i:=by
        rw [← List.prod_ofFn,show c=(fun v:Bool×TileV Q=>r v.1) ∘l.get from rfl,←List.map_ofFn,List.ofFn_get]
    rw[h]; let U(i):= (p i).2.1; have h(i i':Fin l.length)(hi:i≠i'): 4*C.S.spacing ℓ<dist (U i) (U i')∧ ((b i||b i')→ 4*C.S.spacing j<dist (U i) (U i')):=by
        rcases lt_or_gt_of_ne hi with h|h; exact hg.rel_get_of_lt h
        rw [dist_comm,Bool.or_comm]; exact hg.rel_get_of_lt h
    exact campuses hp H hφ x z (points U) b _ c j ℓ hj (fun i hi=>hk _ (List.get_mem ..) hi) (fun i hi=>ht _ (List.get_mem ..) hi) (fun i j hi=> (h i j hi).1) (fun i j hi hk=> (h i j hi).2 (by simp[hk])) (fun i=>hv (p i) (List.get_mem ..)) hC hb
-- trifold
variable (l m p:Strip Q)(j ℓ:ℕ) (R K:ℝ) (x:I→ E4)
set_option quotPrecheck false
local notation "s₀" j:arg=> (4*C.S.spacing j)
omit hp H hφ in
lemma sumCost (x:Strip Q) {c:ℝ} : (x.map (fun _=> c)).prod=c^x.length:=by induction x with|nil=>simp| cons a l ih=> rw [List.map_cons,List.prod_cons,List.length_cons,ih,pow_succ']
set_option maxHeartbeats 380000 in
lemma plaza (hj:j+1≤ℓ)(hC:Fintype.card I*8< (C.S.step j).L.val) (ht:(l.length+p.length)*6< (C.S.step ℓ).L.val)(hu:gap m (4*C.S.spacing j))(he:gap (l++p) (4*C.S.spacing ℓ))(hv:∀ z∈l++p,∀ y∈m,4*C.S.spacing j<dist z.1 y.1)(hw:∀ z∈l++p,Privilege P Q ℓ z.2 K)(hM:∀ z∈m,(∃ i, Scan C j (x i) z.1) ∧ Privilege P Q j z.2 R): ‖Strip.tone (l++m++p)‖ ≤ K^(l.length+p.length) * R^m.length:=by
    let A(b:Bool): TileV Q → Bool × TileV Q:=fun v=>(b,v); let L:= l.map (A false); let V:= m.map (A true); let U:=p.map (A false); let X:=L++V++U; let W(i:Bool):ℝ:= if i then R else K; let B:=l++p; let z(i:Fin B.length):=(B.get i).1
    have hp' : X.map Prod.snd=l++m++p:=by simp[X,L,U,V,A,List.map_map,comp_def]
    have hx:(X.map fun i=>W i.1).prod=K^(l.length+p.length)*R^m.length:=by simp only [X,L,V,U,A,List.map_map, List.map_append, List.prod_append,comp_def,W,Bool.false_eq_true,↓reduceIte,sumCost,pow_add]; ring
    let E(y u: Bool × TileV Q):Prop:= (4*C.S.spacing ℓ<dist y.2.1 u.2.1)∧(y.1||u.1→4*C.S.spacing j<dist y.2.1 u.2.1)
    have hc: s₀ ℓ ≤ s₀ j:= mul_le_mul_of_nonneg_left (spacing_antitone _ (by omega)) (by norm_num)
    have hpq:(L++U).Pairwise E:=by rw [show L++U=B.map (A false) from List.map_append.symm]; exact he.map (A false) fun x y h=> ⟨h,by simp [A]⟩
    obtain ⟨hL,h1,hT⟩:= List.pairwise_append.mp hpq; have hV:V.Pairwise E:=hu.map _ fun _ _ h=> ⟨hc.trans_lt h,fun _=>h⟩
    have hq(y): y∈L++U→ ∀ q∈V, E y q∧E q y:=by -- syntax
         intro hi q hh; rw [show L++U=B.map (A false) from List.map_append.symm] at hi; rcases List.mem_map.mp hi with ⟨i,hG,rfl⟩; rcases List.mem_map.mp hh with ⟨q,h',rfl⟩; have h:= hv i hG q h'; have hl: s₀ j<dist q.1 i.1:= (by rwa [dist_comm]); exact ⟨⟨hc.trans_lt h,fun _=>h⟩,⟨hc.trans_lt hl,fun _=>hl⟩⟩
    have Hm:X.Pairwise E:=by refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hL,hV,fun x hh y hy=>(hq x (List.mem_append_left _ hh) y hy).1⟩,h1,?_⟩; intro x hh y hy; rcases List.mem_append.mp hh with he'|he'; exact hT x he' y hy; exact (hq y (List.mem_append_right _ hy) x he').2
    have hK(i : Bool×TileV Q)(hi:i∈X): i∈V ∨ i∈ B.map (A false):=by unfold X at hi; rw [List.mem_append,List.mem_append] at hi; rw [show B.map (A false)= L++U from List.map_append, List.mem_append]; tauto
    have hy(i : Bool×TileV Q)(hi:i∈X)(h:i.1=true):i.1=true∧ Privilege P Q j i.2.2 R ∧ ∃ p,Scan C j (x p) i.2.1:=by
        rcases hK i hi with h|hr; · obtain ⟨z,hz,rfl⟩:= List.mem_map.mp h; exact ⟨rfl,(hM z hz).2,(hM z hz).1⟩
        obtain ⟨s,ht,hp⟩:= List.mem_map.mp hr; rw [←hp] at h; cases h
    have hf(i :Bool×TileV Q)(hi:i∈X)(h:i.1=false): i.1=false∧Privilege P Q ℓ i.2.2 K∧∃ u,i.2.1=z u:=by
        rcases hK i hi with hz|hr; · obtain ⟨s,ht,H⟩:= List.mem_map.mp hz; rw [←H] at h; cases h
        obtain ⟨t,hT,rfl⟩:= List.mem_map.mp hr; refine ⟨rfl, hw _ hT,?_⟩; obtain ⟨j,hj⟩:=List.mem_iff_get.mp hT; exact ⟨_, congr_arg Prod.fst hj.symm⟩
    have hh:= solo hp H hφ X W x z j ℓ hj hC (by simpa [B] using ht) Hm (fun i hi hl=>(hy i hi hl).2.2) (fun i hi hl=>(hf i hi hl).2.2) (fun i hi=>by
         unfold W; cases h:i.1
         · simp only [Bool.false_eq_true,↓reduceIte]; exact (hf i hi h).2.1
         simp only [↓reduceIte]; exact (hy i hi h).2.1)
    rwa [hp',hx] at hh
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.plaza
