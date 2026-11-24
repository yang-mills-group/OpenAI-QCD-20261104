import YM.Lyre.Price
/-! Price seminorm.Cov signature.TH -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter QCD QCD.Lat QCD.Tide QCD.Grass Lattice Wilson NormedSpace
open Chess Cells Romance Plum Finset
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {A:Type*}{F:ℕ}{n:Side} (T:Cells.Tiling n)(R:Regulator n F) (p:T.Cell)(x y:Stud n F)(t:ℂ)
noncomputable def tintV (l:List (Band n))(t:ℂ):= (((star:ℂ→ℂ))^[l.length]) t
lemma tinted (l:List (Band n)): road l (t • x) = tintV l t • road l x ∧ ‖tintV l t‖=‖t‖:=by
    induction l with
    | nil=> exact ⟨rfl,rfl⟩
    | cons C l ih=> simp only [road,ih.1,smog, tintV,List.length_cons,iterate_succ_apply']; exact ⟨trivial,(norm_star _).trans ih.2⟩
open Lyre.Array
lemma top_spin : topH T R (t • x) p=‖t‖*topH T R x p:=by
    let X v:=pathT T (Romance.tag T p v); let q(v:T.Cell):ℂ:=tintV (X v) t
    let L:= (univ:Finset T.Cell).toList; let H:=palmH T x p
    have h(l:List T.Cell): (l.map (palmH T (t • x) p)).prod=(l.map q).prod • (l.map H).prod∧ ‖(l.map q).prod‖=‖t‖^l.length:=by
        induction l with
        | nil=> exact ⟨(one_smul ℂ _).symm, by simp⟩
        | cons a l ih=> rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,List.map_cons,List.prod_cons, (show palmH T (t • x) p a=q a • H a from (tinted x t (X a)).1), ih.1]; rw [smul_mul_assoc,mul_smul_comm,norm_mul,show ‖q a‖=‖t‖ from (tinted x t (X a)).2,ih.2,List.length_cons,pow_succ']; exact ⟨(mul_smul ..).symm,rfl⟩
    apply (pow_left_inj₀ (top_nn T R _ p) (mul_nonneg (norm_nonneg _) (top_nn T R _ p)) T.cells_positive.ne').1
    rw [top_power,mul_pow,top_power]; unfold loom; change ‖valueH R (L.map _).prod‖=_; rw [ (h L).1, Lyre.spend, norm_smul,(show ‖(L.map q).prod‖=_ from (h L).2)]; simp [L]; exact Or.inl rfl
-- noncommutative disjoint readings.M.L.
lemma wearP {A B V:Type*}[Fintype A][DecidableEq A][Fintype B][Ring V][Algebra ℂ V] (s:List A)(hs:s.Nodup)(hx:∀ i:A,i∈s) (X:A→B→V):
     (s.map (fun i=>∑ j:B, X i j)).prod = ∑ i: A→B, (s.map (fun v=>X v (i v))).prod:=by
    classical
    let p:=s.get; have he : Bijective p:= ⟨(List.nodup_iff_injective_get.mp hs),fun a=>by obtain ⟨i,hi,hr⟩:= List.mem_iff_getElem.mp (hx a); exact ⟨⟨i,hi⟩,hr⟩⟩ -- names
    let E:= Equiv.ofBijective _ he; let L : (A→B) ≃ (Fin s.length→B):= Equiv.arrowCongr E.symm (Equiv.refl _)
    let W (i: Fin s.length)(j:B):= X (s.get i) j
    have hZ (F:A→V): (s.map F).prod=(List.ofFn fun i=> F (s.get i)).prod:=by change _=(List.ofFn (F ∘ s.get)).prod; rw [← List.map_ofFn (f:=s.get),List.ofFn_get]; -- names
    rw [hZ]; simp_rw [hZ]
    rw [← Equiv.sum_comp L.symm]
    let G:= MultilinearMap.mkPiAlgebraFin ℂ s.length V
    have hp: (List.ofFn (fun i=> ∑ j:B,W i j)).prod = ∑ j: Fin s.length→ B, (List.ofFn fun i=> W i (j i)).prod:=by simp_rw [← MultilinearMap.mkPiAlgebraFin_apply (R:=ℂ)]; exact G.map_sum W
    refine Eq.trans hp (sum_congr rfl (fun i _=>?_)); congr 1; apply congr_arg (fun f : Fin s.length→V=> List.ofFn f); funext k; change X _ _= X (E k) (i (E.symm (E k))); rw [Equiv.symm_apply_apply]; rfl

lemma sumsA {I:Type*}(g:Finset I)(x:I→Stud n F)(hp:∀ i∈g,Stays (x i)):Stays (∑ i∈g,x i):=by
   classical
   induction g using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact stays continuous_const
   | insert a s hs ih=> rw [sum_insert hs]; exact ((hp a (mem_insert_self ..)).both (ih fun i h=>hp i (mem_insert_of_mem h))).flows continuous_add
lemma sumsV {I:Type*}(g:Finset I)(x:I→Stud n F)(hp:∀ i∈g,Stays (x i)):valueH R (∑ i∈g,x i)=∑ i∈g,valueH R (x i):=by
   classical
   induction g using Finset.induction_on with
   | empty=>simp [valueH,rawK,joint]
   | insert a s hs ih=> rw [sum_insert hs,sum_insert hs,spentA R (hp a (mem_insert_self ..)) (sumsA s x (fun i h=> hp i (mem_insert_of_mem h))),ih (fun i h=>hp i (mem_insert_of_mem h))]
lemma bills {A:Type*}[Fintype A](x:A→Stud n F)(hp:∀ i,Fence (T.chamber p) (x i))(hv:∀ i,Potion (x i))(ht':R.t=0)(hk : T.kind = .link)(hβ : 0 ≤ R.β) (hn : 4 ≤ n.val): topH T R (∑ i:A,x i) p ≤ ∑ i:A, topH T R (x i) p:=by
    let B:=T.Cell; let P:= univ (α:=B); let Y (i : A) v:= palmH T (x i) p v
    let V(a:B→ A):= Lyre.Array.use T univ.toList Y a; let K (i:A):= topH T R (x i) p
    apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (sum_nonneg (fun i _=>top_nn ..)); rw [top_power]
    have ht:= booked T R hk (fun _=>p) x hp hv
    have hu (s:Finset A)(i:T.Cell): palmH T (∑ j∈s,x j) p i=∑ j∈s,Y j i:=by
        induction s using Finset.induction_on with
        | empty=> simp only [sum_empty,palmH]; suffices h: ∀ l:List (Band n),road l (0:Stud n F)=0 from h _; intro l; induction l with | nil=>rfl| cons a l ih=> rw [road,ih]; funext i; simp [huesT]
        | insert a s ha ih=> rw [sum_insert ha,sum_insert ha, palmH,road_add]; change _+palmH T _ _ _=Y a i+_; rw [ih]; rfl
    have hy:loom T (palmH T (∑ i:A,x i) p)=∑ a:T.Cell→A,V a:=by
       unfold loom; rw [show palmH T (∑ i:A,x i) p=(fun v=>∑ i:A,Y i v) from funext fun _=>hu _ _]; exact wearP _ (nodup_toList _) (fun i=>mem_toList.mpr (mem_univ i)) (fun i j=> Y j i)
    have hZ (a:T.Cell→A) (l:List T.Cell): Stays (Lyre.Array.use T l Y a):=by
       induction l with| nil=>exact (Plum.Fence.one (A:=T.chamber p)).hp| cons i l ih=>exact (ht.floors (a i) i).hp.mult ih
    rw [hy,sumsV R _ _ (fun i _=> hZ i _)]
    apply (norm_sum_le ..).trans; change _ ≤ (∑ i:A,K i)^_; have hJ : (∑ i:A,K i)^Fintype.card T.Cell= ∑ a:T.Cell→A, ∏ i:T.Cell,K (a i):=by rw [← card_univ, ← prod_const]; exact Fintype.prod_sum _
    rw [hJ]; exact sum_le_sum fun i _=>Lyre.Array.tiles i ht ht' hk hβ hn
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.top_spin
#print axioms YM.Massive.Lyre.bills
