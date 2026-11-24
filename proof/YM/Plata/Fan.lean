import YM.Plata.Fennel
/-! # At finite tower. All products in their stated order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Filter Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum QCD.Grass Chess Cells
open Cylinder Patria Patria.Depth Patria.Hub Patria.Exposure
open UV
open scoped Topology BigOperators Classical ComplexOrder
variable {F n:ℕ}{c:Side}
variable {I J:Type*} [Fintype I]
/-- Expansion for noncommutative cluster polynomials. -/
lemma planes {R:Type*}[Semiring R][Algebra ℂ R](x:Fin n→ I→ R)(z:Fin n→ I→ℂ):
    (List.ofFn fun i:Fin n=> ∑ j:I,z i j • x i j).prod=∑ f:Fin n→ I,(∏ i,z i (f i)) • (List.ofFn fun i:Fin n=> x i (f i)).prod:=by
    change MultilinearMap.mkPiAlgebraFin ℂ n R (fun i=> ∑ j:I,z i j • x i j)=_; rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _=>MultilinearMap.map_smul_univ _ _ _ -- args
omit [Fintype I] in
lemma leaves (L:List I)(N:List J)(X:I × J→Stud c F) : let f:= L.flatMap (fun i=> N.map (Prod.mk i)); (f.map X).prod= (L.map fun i=> (N.map (fun j=> X (i,j))).prod).prod:=by
    induction L with
    | nil=> rfl
    | cons a L ih=>simp only[List.flatMap_cons,List.map_append,List.map_map,List.prod_append,List.map_cons,List.prod_cons]; exact congr_arg₂ (·*·) rfl ih
omit [Fintype I] in
lemma hearty {S:Type*}[Semiring S](V: List (List S)): V.flatten.prod=(V.map List.prod).prod:=by induction V with| nil=>rfl| cons a l ih=> rw[List.flatten_cons,List.prod_append,ih,List.map_cons,List.prod_cons]
variable (T:Tiling c)(R:Regulator c F)
variable (u:I→ TapeWalk c T)(X:J→ Stud c F)(L:List I)(N:List J)(v:J→T.Cell)(hX:∀ j,Fence (T.chamber (v j)) (X j) ∧ Potion (X j)) (hT:T.kind=.link)
noncomputable abbrev wend (x:Stud c F)(i:I): Stud c F:= road (pathT T (u i)) x
variable (ht:R.t=0)(hv:0 ≤ R.β)(hN:4 ≤ c.val)(hz:R.Z≠0)
include hX ht hv hN hz hT
variable [Fintype J]
lemma spoils (hc:L.Nodup)(hn:N.Nodup)(hm:∀ i,i∈L)(h:∀ j,j∈N)(hd:Injective (fun p:I× J=>finish T (v p.2) (u p.1))): ‖valueH R (L.map (wend T u (N.map X).prod)).prod‖ ≤ (∏ i:J, topH T R (X i) (v i)) ^ Fintype.card I:=by
    let p:I× J→ T.Cell:= fun i=> finish T (v i.2) (u i.1); let E(i:I× J):=wend T u (X i.2) i.1; let l:=L.flatMap (fun i=> N.map (Prod.mk i)); have hh: SignedEq (L.map (wend T u (N.map X).prod)).prod (l.map E).prod:=by rw [show (l.map E).prod= _ from leaves L N E]; exact signsList L _ _ fun i=> royalties N X T _ fun j=> (hX j).2
    have hp:l.Nodup:=by
        apply List.nodup_flatMap.mpr; refine ⟨fun x hx=> hn.map (fun j k e=> Prod.mk.inj e|>.2),?_⟩ -- definition check ordering
        apply hc.pairwise_of_forall_ne; intro i hi j hj h z hz hy; obtain ⟨x,-,rfl⟩:=List.mem_map.mp hz; obtain ⟨w,hw,he⟩:= List.mem_map.mp hy; exact h ((Prod.mk.inj he).1.symm)
    have hf(i:I× J): i∈l:=List.mem_flatMap.mpr ⟨i.1,hm _,List.mem_map.mpr ⟨i.2,h _,rfl⟩⟩
    have hu(i:I × J): Potion (E i):= potW _ _ (hX i.2).2
    rw [signsV R hh]; apply (wardsP T R hT E p hd l hp hf (fun i=> ⟨roadF _ _ (v i.2) T.chamber (Romance.chamber T) (hX i.2).1,hu i⟩) ht hv hN hz).trans_eq
    have he(i:I × J):topH T R (E i) (p i)=topH T R (X i.2) (v i.2):=(earn_eq T hT R (v i.2) _ (hX i.2).2 _ (p i) rfl (E i) (hu i) (show SignedEq (road (pathT T (u i.1)) _) _ from SignedEq.refl _)).symm -- orientation
    simp_rw [he,Fintype.prod_prod_type]; simp
omit ht hv hN hz hT hX
variable {C:Sequence}{P:Calibration C}{k:ℕ}
local notation "c'"=> C.S.side (C.R k) (C.N k)
variable (Y:Fin n→ I→ List Stem)(z:Fin n→I→ ℂ)
lemma taskJoin (Y:Fin n→ List Stem): task P k (List.ofFn Y).flatten= (List.ofFn fun i:Fin n=> task P k (Y i)).prod:=by
    unfold task; rw [List.map_flatten,hearty,List.map_ofFn,List.map_ofFn]; rfl
lemma moneyJoin: (List.ofFn fun i:Fin n=> cash P k (Y i) (z i)).prod=cash P k (fun f:Fin n→I=> (List.ofFn fun i:Fin n=>Y i (f i)).flatten) (fun f=> ∏ i,z i (f i)):=by
    unfold cash; rw [planes]; exact Finset.sum_congr rfl fun f _=> congr_arg (fun y=> (∏ i,z i (f i)) • y) (taskJoin _).symm -- syntax
omit [Fintype J] in
lemma coed (F:J→ Insertion (C.S.side (C.R k) (C.N k)) 6) (L:List J): ⇑((L.map F).prod)=(L.map fun i=> ⇑(F i)).prod:=by induction L with| nil=>rfl| cons a L ih=>simp only[List.map_cons,List.prod_cons,ContinuousMap.coe_mul,ih]
end YM.Plata
namespace YM.Plata
open Function Filter Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum QCD.Grass Chess Cells
open Cylinder Patria Patria.Depth Patria.Hub Patria.Exposure
open UV
open scoped Topology BigOperators Classical ComplexOrder

variable {I:Type*} [Fintype I] {C:Sequence}{P:Calibration C}{k n:ℕ}
variable (Y:I→List Stem)(z:I→ℂ)(hP:P.System)(T:Tiling (C.S.side (C.R k) (C.N k)))(p:T.Cell)(g: Fin n→ℕ)(a:Axis)(s:Fin n→Bool)
noncomputable abbrev gand (i:Fin n) (j:I) := passes P (s i) a (y T p a) (hail T p a (g i)) (Y j)
noncomputable abbrev wealth (s:Fin n→Bool)(z:I→ℂ)(f:Fin n→I):= ∏ i, turns (s i) (z (f i))
noncomputable abbrev plane (f:Fin n→I) := (List.ofFn fun i:Fin n=> gand (P:=P) Y T p g a s i (f i)).flatten
include hP
lemma loads (hp:T.kind=.link)(hr:((C.A k).regulator).t=0)(hx:Potion (⇑(cash P k Y z)))(hz:∀ i,∀ j∈Y i,P.Mixing j.d k): let f:= fun i:Fin n=> trace T p a (g i) (s i); let F:=wend T f (cash P k Y z); SignedEq ((List.finRange n).map F).prod (⇑(cash P k (plane (P:=P) Y T p g a s) (wealth s z))):=by
    intro f F; let G(i:Fin n):= cash P k (gand (P:=P) Y T p g a s i) (fun j=>turns (s i) (z j)); have hf(i:Fin n): SignedEq (F i) (⇑(G i)):= debts hP T p (g i) Y z hz a (s i) hp hr hx
    have hp' : (List.ofFn G).prod= _ := moneyJoin (P:=P) (k:=k) (fun i=>gand (P:=P) Y T p g a s i) (fun i j=> turns (s i) (z j))
    rw [show cash P k _ _=(List.ofFn G).prod from hp'.symm,List.ofFn_eq_map,coed]; exact signsList _ _ _ hf
end YM.Plata
#print axioms YM.Plata.spoils
#print axioms YM.Plata.loads
