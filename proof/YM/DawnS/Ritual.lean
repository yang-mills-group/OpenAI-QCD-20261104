import YM.Arise.Star
import YM.DawnS.Groom

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical
variable {A:Type}[Fintype A](Q:Matrix A A ℂ)
open Arise.Pair Arise Creek Cove Matrix
-- bilinear.PF charge
noncomputable def unionB : Seed A→ₗ[ℂ]Seed A→ₗ[ℂ]ℂ:= (thetaBasis A).constr ℂ fun i=> (thetaBasis A).constr ℂ fun j=> Q i j-Q j i
local notation "spB"=> unionB Q
lemma skyZ(i j:A): unionB Q (thetaBasis _ i) (thetaBasis _ j)= Q i j-Q j i:=by unfold unionB; rw[Module.Basis.constr_basis,Module.Basis.constr_basis]
lemma velT(i:A)(x:Seed A)(w: Alg A): Arise.Pair.dif Q i (line x*w)= unionB Q (thetaBasis _ i) x • w- line x * Arise.Pair.dif Q i w:=by
     have he(a:A): Arise.Pair.dif Q i (atom a*w)=(Q i a-Q a i) • w-atom a*Arise.Pair.dif Q i w:=by
             unfold Arise.Pair.dif; simp only [ContinuousLinearMap.sum_apply]; change ∑ j,(Q i j-Q j i) • vary j (atom a*w)= _ - atom a*∑ j,(Q i j-Q j i) • vary j w; simp_rw [vary_head, smul_sub,Finset.sum_sub_distrib,Finset.mul_sum]; rw [sum_eq_single a]; simp [Grass.probe,mul_smul_comm]
             intro j _ ht; simp [Grass.probe,ht,Ne.symm ht]; simp
     rw [← (thetaBasis A).sum_repr x]; simp only [map_sum,map_smul, sum_mul,Finset.sum_smul,← Finset.sum_sub_distrib,_root_.smul_mul_assoc]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [skyZ Q, show line ((thetaBasis A) j)=atom j from rfl,he]; simp only[_root_.smul_sub]; congr 1; rw [smul_smul,mul_sub]; rfl
noncomputable def pwn (l:List (Seed A)): Alg A:=(l.map ⇑line).prod
lemma collector(i:A)(l:List (Seed A)): Arise.Pair.dif Q i (pwn l)=∑ j:Fin l.length, ((-1:ℂ)^j.val*(unionB Q (thetaBasis _ i) (l.get j))) • pwn (l.eraseIdx j.val):=by
     induction l with
     | nil=> haveI : IsEmpty (Fin ([]:List (Seed A)).length):=(inferInstance : IsEmpty (Fin 0)); rw [sum_of_isEmpty]; unfold Arise.Pair.dif; simp only [pwn,ContinuousLinearMap.sum_apply, List.map_nil,List.prod_nil]; refine sum_eq_zero fun j _=>?_ ; change (Q i j-Q j i) • vary j 1=0; rw [vary_one,smul_zero]
     | cons a l ih=>
        rw [show pwn (a::l)=line a*pwn l from rfl,velT,ih]; let f(j:Fin (l.length+1)):= ((-1:ℂ)^j.val*(unionB Q (thetaBasis _ i) ((a::l).get j))) • pwn ((a::l).eraseIdx j.val)
        change _=∑ j,f j; rw [Fin.sum_univ_succ f]; unfold f
        simp only [Fin.val_zero,List.get_eq_getElem,List.getElem_cons_zero, List.eraseIdx_zero,pow_zero,one_mul, Fin.val_succ,List.getElem_cons_succ,List.eraseIdx_cons_succ,pwn,List.map_cons,List.prod_cons]; rw [Finset.mul_sum]; rw [sub_eq_add_neg,← Finset.sum_neg_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun j _=> ?_; rw [mul_smul_comm, pow_succ',neg_one_mul,neg_mul,neg_smul]
noncomputable def lease : Alg A→ₗ[ℂ]ℂ:= (Grass.coef ∅).comp ((offP A Unit).toLinearMap.comp ((QCD.Creek.birth (Anomaly.Wand Q)).toLinearMap))
lemma veil(x:Seed A)(l:List (Seed A)): lease Q (line x*pwn l)=∑ j:Fin l.length, ((-1:ℂ)^j.val*(unionB Q x (l.get j))) * lease Q (pwn (l.eraseIdx j.val)):=by
    have h(i:A) :lease Q (atom i*pwn l)=∑ j:Fin l.length, ((-1:ℂ)^j.val*(unionB Q (thetaBasis _ i) (l.get j))) * lease Q (pwn (l.eraseIdx j.val)):=by
             unfold lease; simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe, AlgHom.toLinearMap_apply]; rw [ravels,collector]; have hv: offP A Unit (atom i)=0:=by simp only [offP,change_atom]; simp
             simp only [map_sum,map_smul,map_add,map_mul,hv, zero_mul,zero_add,smul_eq_mul]
    rw [← (thetaBasis A).sum_repr x]; simp only [map_sum,map_smul,LinearMap.sum_apply, sum_mul,_root_.smul_mul_assoc,map_sum, map_smul,LinearMap.smul_apply, mul_sum,smul_eq_mul]; change ∑ i,(thetaBasis A).repr _ i * lease Q (atom i*pwn l) = _
    simp_rw[h, mul_sum]; rw [sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; apply Finset.sum_congr rfl; intro j _; ring
lemma clean1:lease Q 1=1:=by unfold lease; rw [LinearMap.comp_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,emptyW,AlgHom.toLinearMap_apply,map_one]; rw [← mono_empty (A:=Unit),Grass.read] -- type
end YM.DawnS
#print axioms YM.DawnS.veil
