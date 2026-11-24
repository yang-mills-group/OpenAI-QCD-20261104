import YM.Rill.Hill
/-! Glue two layers for heterogeneous spatial placements. Product estimate for any cellwise assignment using authenticated grants at different pitches in the *same* origin frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet
namespace Quilt
-- unified roster. external grouping assigned by sets. arbitrary flags central Bool. represent typed `Pricing` roles either left small with image in big, or big cell exclusive; use point value through parity expansion for both.
variable {n:Side} (T W:Tiling n)(R:Regulator n 6) (p:T.Cell) {I:Type} [Fintype I] {w:Finset I}
variable (v:I→ T.Cell) (f:I→ Insertion n 6)(B:I→ℝ)
lemma opus (l:List I):⇑((l.map f).prod)= (l.map (fun i=> (⇑(f i):Stud n 6))).prod:=by induction l with|nil=>rfl|cons a l ih=>simp only [List.map_cons,List.prod_cons, ContinuousMap.coe_mul]; rw[ih]
variable (ht:T.kind=.link)(hh:W.kind=.link)(L:Ladder T W)(hk:∀ i,(W.chamber i).Nonempty)(hp:R.t=0)(hx:0 ≤R.β)(hP:4 ≤ n.val)(hR:R.Z≠0)
variable (z:I→W.Cell)(k:I→Bool)
-- parity homogeneous symbols. throughout proof.L actual. use branch if k decides.big. Assign all fields at distinct small cells for each big v; singleton for true branch. also margin. Need nested proof ANY small cell to one big: geometry using station formula see next.
noncomputable abbrev stageFee (i:I):ℝ:= if k i then topH T R (f i) (v i) else topH W R (f i) (z i)
structure Enclave (i:I): Prop where
    pot:Potion (f i)
    house:k i=true→Fence (T.chamber (v i)) (f i)
    hut: k i=false→ Fence (W.chamber (z i)) (f i)
structure Unity : Prop where
    privateBox (i j:I): v i=v j→ k i=true→ i=j
    view (i:I): k i=false → W.chamber (z i) ⊆ T.chamber (v i)
    night (i j:I): k i=false → k j=false→ z i=z j→ i=j
include L hh hp hx ht hP hR hk -- replace
variable (V:Unity T W v z k) (H:∀ i,Enclave T W v f z k i)
include V H
set_option quotPrecheck false
local notation "F"=> stageFee T W R v f z k
local notation "X" i:arg=> (⇑(f i): Stud n 6)
private abbrev blockI (p:T.Cell):= {i:I// v i=p}
lemma gathered (p:T.Cell)(l: List (blockI T v p))(hl:l.Nodup)(he:∀ i,i∈l): let Y(i:blockI T v p):= ⇑(f i.val); topH T R (l.map Y).prod p ≤ ∏ i:blockI T v p,F i.val:=by
   intro Y; by_cases h:∃ i:blockI T v p,k i.val=true
   · obtain ⟨i,hi⟩:=h; have h':∀ j:blockI T v p,i=j:= fun j=>Subtype.ext (V.privateBox _ _ (i.property.trans j.property.symm) hi); letI:Unique (blockI T v p):= { default:=i,uniq:=fun j=>(h' j).symm }; have he:l=[i]:=by
         cases l with|nil=>simp_all|cons a s=> rw [← h' a]; simp; cases s; rfl; rename_i b s; subst_vars; exfalso; exact (List.nodup_cons.mp hl).1 (List.mem_cons.mpr (Or.inl (Subsingleton.elim ..)))
     rw [he]; simp only[List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Fintype.prod_unique]; change _ ≤ F i.val; rw [stageFee,if_pos hi,i.property]
   push Not at h
   have h1(i:blockI T v p):k i.val=false:= (by simpa using h i)
   apply (Ladder.ticks L R p l (fun i=>z i.val) (fun i=>X i.val) hl he (fun i j hh=> Subtype.ext (V.night i.val j.val (h1 _) (h1 _) hh)) (fun i=>by have h:= V.view i.val (h1 i); rw [i.property] at h; exact h) (fun i=>⟨(H _).hut (h1 _),(H _).pot⟩) hp hh hk hx hP hR).trans_eq; apply prod_congr rfl; intro i _; rw[stageFee,if_neg (by simp [h i])]
lemma spherical(l:List I)(hL:l.Nodup)(hl:∀ i,i∈l): ‖R.average (l.map f).prod‖ ≤ ∏ i,F i:=by
    -- order by actual big cells.A
    let α a:=blockI T v a; let Λ(p:T.Cell):List (α p):= Finset.univ.toList; let U:List T.Cell:= Finset.univ.toList; let r(p:T.Cell):= (Λ p).map Subtype.val; let X'(p:T.Cell): Stud n 6:= ((r p).map (fun i=>X i)).prod; let W':= U.flatMap r; have hQ: Folio.Muster v r:=by
        refine ⟨fun i=>List.Nodup.map Subtype.val_injective (nodup_toList _),fun i j=>?_⟩; unfold r; rw[List.mem_map]; constructor; · rintro ⟨x,h,rfl⟩; exact x.property
        intro h; exact ⟨⟨_,h⟩,mem_toList.mpr (mem_univ _),rfl⟩
    have hS : l.Perm W':=(List.perm_ext_iff_of_nodup hL (Folio.named v r hQ U (nodup_toList _))).mpr fun i=>⟨fun _=> List.mem_flatMap.mpr ⟨v i,mem_toList.mpr (mem_univ _),(hQ.address ..).2 rfl⟩,fun _=>hl i⟩ -- hQ filler.
    have hX: Chess.SignedEq (l.map (fun i=> X i)).prod (loom T X'):=by
        have h: (W'.map (fun i=> X i)).prod= loom T X':=by
            unfold W' loom; change _=(U.map X').prod; clear hS hl hL; generalize U=t; induction t with| nil=>rfl |cons a t ih=> simp only[List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,ih]; rfl
        rw[←h]; exact signed_rearr _ _ hS _ fun i=>(H i).pot
    have hq: (∏ i:T.Cell,∏ j:α i,F j.val)=∏ i,F i:=by
        let e : (Σ a:T.Cell,α a)≃ I:={ toFun:=fun a=>a.2.val, invFun:=fun i=>⟨v i,i,rfl⟩,left_inv:=fun ⟨a,j,hj⟩=>by subst a; rfl,right_inv:=fun i=>rfl }
        exact (Fintype.prod_sigma' (M:=ℝ) (fun i => fun j:α i =>F j.val)).symm.trans (Equiv.prod_comp e F)
    have hw(p:T.Cell): Fence (T.chamber p) (X' p):=by
        have he(i):i∈r p →Fence (T.chamber p) (X i):=by
             intro h; rw[← (hQ.address ..).1 h]; cases ht:k i; exact ((H i).hut ht).high (V.view i ht); exact (H i).house ht
        unfold X'; generalize r p=t at he ⊢; clear hS; induction t with| nil=>exact Fence.one|cons a t ih=> exact (he a (by simp)).mult (ih fun i h=>he i (by simp [h]))
    rw [Goblet.knownV, opus, signsV R hX,← hq]; refine (manyH T R ht X' (fun i=> ⟨hw i, potProd _ _ (fun a _=>(H a).pot)⟩) hp hx hP).trans ?_ -- replace
    apply prod_le_prod (fun i _=>top_nn ..); intro i _; unfold X' r; rw[List.map_map]; exact gathered _ _ _ v f ht hh L hk hp hx hP hR _ _ V H i _ (nodup_toList _) fun j=>mem_toList.mpr (mem_univ _)
omit H
omit hx ht hh L hk hp hR hP V
abbrev flight (i:I):= if k i then Gold R T (v i) (f i) (B i) else Gold R W (z i) (f i) (B i)
include hx ht hh L hk hp hR hP
variable {N:ℕ}
set_option maxHeartbeats 480000 in
-- Fin arrays enough
lemma package (f:Fin N→ Insertion n 6)(b:Fin N→ℝ)(v:Fin N→T.Cell)(z:Fin N→ W.Cell)(k:Fin N→Bool)(hV:Unity T W v z k)(h:∀ i, flight T W R v f b z k i): ‖R.average (List.ofFn f).prod‖ ≤∏ i,b i:=by
    -- scope V older remove
    have he(i):∃ N:ℕ,∃ G:Fin N→Insertion n 6,f i= ∑ j,G j∧(∀ j: Fin N, Enclave T W v (fun _=> G j) z k i) ∧ ∑ j:Fin N,stageFee T W R v (fun _=> G j) z k i≤ b i:=by
         specialize h i; unfold flight at h; split at h
         next hx=> obtain ⟨l,g,hf,hp,H⟩:=h; refine ⟨_,g,hf.symm,fun j=>⟨(hp j).2,(fun _=>(hp j).1),fun hz=>False.elim (by simp_all)⟩,?_⟩; simpa only [stageFee,hx,↓reduceIte] using H -- simplifies match in proof?
         next hx=> obtain ⟨l,g,hf,hp,H⟩:=h; refine ⟨_,g,hf.symm,fun j=>⟨(hp j).2,(fun h=>False.elim (hx h)),fun _=>(hp j).1⟩,?_⟩; simpa only [stageFee, hx,Bool.false_eq_true,↓reduceIte] using H
    choose D g H hE hX using he; let I:=Fin N; let A:= (i:Fin N)→Fin (D i); let G(s:A)(i:Fin N):=g i (s i); let C (i:Fin N)(j:Fin (D i)):= stageFee T W R v (fun _=>g i j) z k i; let V:=(MultilinearMap.mkPiAlgebraFin ℂ N (Insertion n 6)); have ht': (List.ofFn f).prod=∑ s:A,(List.ofFn (G s)).prod:=by
        change V f=∑ s,V (G s); rw [funext H]; exact V.map_sum _
    have hz(s:A): ‖R.average (List.ofFn (G s)).prod‖ ≤ ∏ i:Fin N,C i (s i):=by
        rw [List.ofFn_eq_map]; have hu(i:Fin N): Enclave T W v (G s) z k i:= ⟨(hE _ (s i)).1,(hE _ (s i)).2,(hE _ (s i)).3⟩ -- field projection
        exact spherical T W R v (G s) ht hh L hk hp hx hP hR z k hV hu _ (List.nodup_finRange N) List.mem_finRange
    rw [ht',map_sum]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=>hz i).trans ((Fintype.prod_sum C).symm.le.trans ?_)); refine prod_le_prod (fun i _=> sum_nonneg fun j _=>?_) (fun i _=>hX i); unfold C stageFee; split <;> exact top_nn ..
end Quilt
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Quilt.package
#check YM.Massive.Tarn.Quilt.package
