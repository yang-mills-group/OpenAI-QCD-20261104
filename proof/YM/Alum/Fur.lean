import YM.Alum.Wreath
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
-- economical telescopes. list of differences.pay orientation exactly.
namespace Earing
variable {D I:Type}[Ring D] (x y:Fin F→ D)
noncomputable def skeinH (i j:Fin F) := if j < i then y j else if j=i then x j-y j else x j
noncomputable def bump (i:Fin F): D:=(List.ofFn (skeinH x y i)).prod
lemma subProd : (List.ofFn x).prod-(List.ofFn y).prod= ∑ i: Fin F,bump x y i:=by
      induction F with
      | zero=> simp
      | succ k ih=>
          let u:=x∘Fin.succ; let v:=y∘Fin.succ; let f r:= bump x y r; have h(r:Fin k):bump x y r.succ=y 0*bump u v r:=by
               unfold bump; rw [List.ofFn_succ,List.prod_cons]; congr 1
               rw [show (fun j :Fin k=>skeinH x y r.succ j.succ)=skeinH u v r from funext fun j=>by simp [skeinH,u,v]] -- succ
          have ht:bump x y 0=(x 0-y 0)*(List.ofFn u).prod:=by
               unfold bump; rw [List.ofFn_succ,List.prod_cons,show skeinH x y 0 0 = x 0-y 0 from (by simp [skeinH]), show (fun j:Fin k=>skeinH x y 0 j.succ)=u from (by funext i;simp [skeinH,u])]
          rw[List.ofFn_succ,List.ofFn_succ,List.prod_cons,List.prod_cons,Fin.sum_univ_succ,ht]; simp_rw [h]; rw [← mul_sum, ← ih u v]; change x 0*(List.ofFn u).prod-y 0*(List.ofFn v).prod=_; rw[sub_mul,mul_sub]; abel
end Earing
open Earing
variable {k:ℕ}(R:Regulator n F)(U:Tiling n)
-- Binder license held even if facts only.H.B.Use.
structure Smoke (T:Tiling n) (R:Regulator n F):Prop where
  seam : T.kind=.link
  cycle : 4 ≤ n.val
  real : R.t=0
  pos : 0 ≤ R.β
  energy : R.Z≠0
lemma bills_si {A:Type*}(P:U.Cell)(s:Finset A)(x:A→Stud n F)(hx:∀ i∈s,Fence (U.chamber P) (x i) ∧ Potion (x i))(hk:Smoke U R):topH U R (∑ i∈s,x i) P ≤ ∑ i∈s,topH U R (x i) P:=by
      classical
      let f(i:s):= x i.val; have h:=bills U R P f (fun i=>(hx i i.2).1) (fun i=>(hx i i.2).2) hk.real hk.seam hk.pos hk.cycle; unfold f at h; rw [Finset.sum_coe_sort, show (∑ i:s,topH U R (x i.val) P)= _ from (Finset.sum_coe_sort (s:=s) (f:=fun i=> topH U R (x i) P))] at h; exact h
lemma bills_plus (P:U.Cell)(x y:Stud n F)(hx:Fence (U.chamber P) x)(hy:Fence (U.chamber P) y)(hp:Potion x)(he:Potion y)(hk:Smoke U R): topH U R (x+y) P ≤ topH U R x P+topH U R y P:=by
      let f: Bool→Stud n F:= fun b=> if b then x else y; have hx':∀ i,Fence (U.chamber P) (f i):=fun i=>by cases i; exact hy; exact hx; -- syntax
      have hh:∀ i,Potion (f i):=fun i=>by cases i; exact he; exact hp
      have hz:= bills U R P f hx' hh hk.real hk.seam hk.pos hk.cycle; simpa [Fintype.sum_bool,f] using hz
lemma postsNeg {C:Set (Site n)}{x:Stud n F}(h:Fence C x): Fence C (-x):= neg_one_smul ℂ x ▸ h.mass (-1)
variable {I:Type}(k:ℕ)(X Y:Fin k→Stud n F) (q : Fin k→ Bool)(T W:Tiling n)(E:Ladder T W) (P:T.Cell)(v:Fin k→W.Cell)
lemma homNeg {x:Stud n F}{p:Bool}{V:Grid n}(hp:Grass.Hom p (x V)): Grass.Hom p ((-x) V):= by change Grass.Hom _ (-_); simpa using hp.smul (-1:ℂ)
lemma batchHom (q: I→ Bool)(X:I→Stud n F)(hq:∀ i V,Hom (q i) (X i V))(L:List I)(U:Grid n):Hom ((L.map q).foldr (fun i j => i ^^ j) false) ((L.map X).prod U):=by
    induction L with| nil=> change Hom false 1; simp [Hom,Plus]| cons a L ih=>exact (hq a _).mul ih
lemma alignedSubP (hq:∀ i V, Hom (q i) (X i V))(hB:∀ i V,Hom (q i) (Y i V)): Potion ((List.ofFn X).prod-(List.ofFn Y).prod):=by
    let L:=List.ofFn (fun j:Fin k=>j); have h(y :Fin k→Stud n F):List.ofFn y=L.map y:=by unfold L; rw [List.map_ofFn]; exact congr_arg _ (funext fun _=>rfl)
    rw[h X,h Y,sub_eq_add_neg]; exact ⟨(L.map q).foldr (fun i j=>i ^^ j) false, fun V=>(batchHom q X hq L V).add (homNeg (batchHom q Y hB L V))⟩
lemma fenceL {I:Type*}(l:List I)(u:I→Stud n F)(B:Set (Site n))(hp:∀ i∈ l,Fence B (u i)):Fence B (l.map u).prod:=by
      induction l with|nil=>exact Fence.one | cons i l ih=> exact (hp i (by simp)).mult (ih fun j he=> hp j (List.mem_cons_of_mem _ he))
lemma fenceV {k:ℕ}(u: Fin k→Stud n F)(B:Set (Site n))(hp:∀ i,Fence B (u i)):Fence B (List.ofFn u).prod:=by
     let l:=List.ofFn (fun i:Fin k=>i); have ht:l.map u=List.ofFn u:=by unfold l; rw[List.map_ofFn]; rfl
     rw [← ht]; exact fenceL l _ _ fun _ _=> hp _
lemma pow_cap (v:Fin k→ ℝ) (C E:ℝ)(hE:0 ≤ E)(i:Fin k)(hx:1≤C)(ht:∀ i,0 ≤ v i)(hu:∀ j,j≠i→ v j ≤ C)(he:v i ≤E): (∏ i: Fin k,v i)≤ E * C^ k:=by
      let s:Finset (Fin k):=univ
      have hA:(∏ j∈s.erase i,v j) ≤ C^k:=calc
          _ ≤ ∏ j∈s.erase i,C:= prod_le_prod (fun _ _=> ht _) fun j hj=> hu j (ne_of_mem_erase hj)
          _ = C^(s.erase i).card:=prod_const C
          _ ≤ _ := pow_le_pow_right₀ hx (le_trans (Finset.card_le_card (Finset.erase_subset i s)) (by simp [s]))
      rw [← Finset.mul_prod_erase _ _ (mem_univ i)]; exact mul_le_mul he hA (prod_nonneg fun _ _=> ht _) hE
-- sublattice price interpolation of calibrated fields.
variable (hX:∀ i,Fence (W.chamber (v i)) (X i))(hY:∀ i,Fence (W.chamber (v i)) (Y i)) (hP:∀ i V, Hom (q i) (X i V)∧ Hom (q i) (Y i V))
variable (hv:Injective v)(hw:∀ i,W.chamber (v i) ⊆ T.chamber P)(hW:Smoke W R)(hT:Smoke T R)(hn:∀ j,(W.chamber j).Nonempty)
variable (e C:ℝ)(he:0 ≤ e)(hC:1 ≤ C) (hp:∀ i,topH W R (X i) (v i) ≤ C ∧topH W R (Y i) (v i) ≤C ∧topH W R (X i-Y i) (v i) ≤ e)
set_option quotPrecheck false
local notation "ζ" i:arg j:arg => skeinH X Y i j
include hP hX hY
lemma comfy (i:Fin k) (j:Fin k): Fence (W.chamber (v j)) (skeinH X Y i j) ∧ Potion (skeinH X Y i j):=by
      have hx:{V:Grid n}→ Hom (q j) (X j V):= fun {V}=>(hP j V).1; have hy:{V:Grid n}→ Hom (q j) (Y j V):=fun {V}=>(hP j V).2
      unfold skeinH; split_ifs with h' hD; · exact ⟨hY j,q j,fun _=>hy⟩
      · rw [sub_eq_add_neg]; exact ⟨(hX j).add (postsNeg (hY j)), q j,fun U=> Grass.Hom.add (@hx U) (homNeg (x:= Y j) (@hy U))⟩
      exact ⟨hX j,q j,fun _=>hx⟩ -- warning implicit V
include E hv hw hW hT hn he hC hp
lemma factor (i:Fin k) : topH T R (bump X Y i) P ≤ e*C^k:=by
     have h(i:Fin k)(j:Fin k):= comfy _ X Y q W v hX hY hP i j; -- sig
     let x(j):=skeinH X Y i j
     have ht:=(Ladder.ticks (W:=W) E R P (List.ofFn (id:Fin k→ Fin k)) v x (List.nodup_ofFn.mpr injective_id) (fun i=> List.mem_ofFn.mpr ⟨i,rfl⟩) hv hw (h i) hW.real hW.seam hn hW.pos hW.cycle hW.energy); rw [List.map_ofFn] at ht; refine ht.trans (pow_cap _ _ _ _ he i hC (fun _=> top_nn ..) (fun j hj=> ?_) (?_))
     · unfold x skeinH; split_ifs with h' ; exact (hp j).2.1; exact (hp j).1
     unfold x skeinH; rw [if_neg (lt_irrefl _), if_pos rfl]; exact (hp _).2.2
set_option maxHeartbeats 460000
lemma subs : let z:=(List.ofFn X).prod-(List.ofFn Y).prod; Fence (T.chamber P) z ∧ Potion z ∧ topH T R z P ≤ k*(e*C^k):=by
      intro z; have h0:=fenceV X _ fun i=> (hX i).high (hw i); have h1:=fenceV Y _ fun i=> (hY i).high (hw i); have hu:=h0.add (postsNeg h1); refine ⟨by unfold z; rw [sub_eq_add_neg]; exact hu, alignedSubP _ X Y q (fun i V=>(hP i V).1) (fun i V=>(hP i V).2),?_⟩
      unfold z; rw[Earing.subProd]; refine (bills T R P (bump X Y) (fun i=> fenceV _ _ fun j=> (comfy _ X Y q W v hX hY hP i j).1.high (hw j)) (?_) hT.real hT.seam hT.pos hT.cycle).trans (le_trans (sum_le_sum fun i _=> factor R k X Y q T W E P v hX hY hP hv hw hW hT hn e C he hC hp i) (le_of_eq (by simp))) -- duplicated shadow. edit
      intro i; unfold bump; let U:=List.ofFn (fun i:Fin k=>i); rw [← (show U.map (skeinH X Y i) =List.ofFn (skeinH X Y i) from List.map_ofFn ..)]; exact potProd _ _ (fun j _ => (comfy k X Y q W v hX hY hP i j).2)
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.subs
#print axioms YM.Massive.Lyre.Goblet.bills_si
#print axioms YM.Massive.Lyre.Goblet.bills_plus
