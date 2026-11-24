import YM.Arise.Site
import YM.Play.Joints
/-! # Full spin contraction including odd. Wick sign-tested on Generator list. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Pair
open Function Lattice Finset Wilson Filter MeasureTheory Tensor
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Matrix
open Massive UV UV.Free Analysis QCD QCD.Creek QCD.Grass QCD.Anomaly Matrix Cove
variable {n m k i j d:ℕ}
-- no norm.S immediate momentum.
variable {A B U: Type}[Fintype A][Fintype B][Fintype U]
variable (Q:Matrix A A ℂ) (F:B→A)
noncomputable def dif (i:A) : EndA A:=∑ j,(Q i j-Q j i) • QCD.Creek.v j
lemma veer (i:A): Wand Q * Creek.l i-Creek.l i*Wand Q=dif Q i:=by
    unfold Wand; simp only [sum_mul,mul_sum, spins, spinner,← sum_sub_distrib]; simp_rw [show ∀ j k:A,Q j k • (Creek.v k * Creek.v j* Creek.l i)- Q j k • (Creek.l i*(Creek.v k*Creek.v j))=_ from fun j k=>((smul_sub ..).symm.trans (congr_arg (fun z:EndA A=> Q j k • z) (whittle k j i 0)))]; unfold dif; simp only [smul_sub,sum_sub_distrib,smul_ite,smul_zero]; simp [Finset.sum_ite_eq']; rw [← sum_sub_distrib]; exact sum_congr rfl fun i _=> (sub_smul ..).symm -- orientation sign check
lemma living (i:A): Commute (dif Q i) (Wand Q):=by
    have he(j:A): Commute (Creek.v j) (Wand Q):=by unfold Wand; exact Commute.sum_right _ _ _ (fun k _=> Commute.sum_right _ _ _ (fun b _=>by unfold Commute SemiconjBy; rw [spinner,spins,(swapsV j b k)]))
    unfold dif; exact Commute.sum_left _ _ _ fun j _=>by unfold Commute SemiconjBy; rw [spins,spinner,(he j).eq]
lemma ravels (i:A)(x:Alg A): birth (Wand Q) (atom i*x)=atom i*birth (Wand Q) x+ birth (Wand Q) (dif Q i x):=by
    have hg:= living Q i; have he:= swerve _ _ _ (veer Q i) hg
    have hv : Commute (dif Q i) (birth (Wand Q)):=by
       unfold birth; exact hg.exp_right -- edit
    have hx:= DFunLike.congr_fun he x; rw [add_mul, hv.eq] at hx; exact hx
lemma gathers (i: A) (l:List A) : dif Q i (l.map atom).prod=∑ j:Fin l.length, ((-1:ℂ)^j.val*(Q i (l.get j)-Q (l.get j) i)) • ((l.eraseIdx j.val).map atom).prod:=by
    induction l with
    | nil=> change _= ∑ j:Fin 0,_; unfold dif; simp only [ContinuousLinearMap.sum_apply, List.map_nil,List.prod_nil]; rw [sum_eq_zero]; simp
            intro j _; change (Q i j-Q j i) • vary j 1=0; rw [vary_one,smul_zero]
    | cons a l ih=>
        have he(x: Alg A): dif Q i (atom a*x)=(Q i a-Q a i) • x-atom a*dif Q i x:=by
             unfold dif; simp only [ContinuousLinearMap.sum_apply]; change ∑ j,(Q i j-Q j i) • vary j (atom a*x)= _ - atom a*∑ j,(Q i j-Q j i) • vary j x; simp_rw [vary_head, smul_sub,Finset.sum_sub_distrib,Finset.mul_sum]; rw [sum_eq_single a]; simp [probe,mul_smul_comm]
             intro j _ ht; simp [probe,ht,Ne.symm ht]; simp -- layout
        rw [List.map_cons,List.prod_cons,he,ih]; let f(j:Fin (l.length+1)):= ((-1:ℂ)^j.val*(Q i ((a::l).get j)-Q ((a::l).get j) i)) • (((a::l).eraseIdx j.val).map atom).prod
        change _=∑ j,f j; rw [Fin.sum_univ_succ f]; unfold f
        simp only [Fin.val_zero,List.get_eq_getElem,List.getElem_cons_zero, List.eraseIdx_zero,pow_zero,one_mul, Fin.val_succ,List.getElem_cons_succ,List.eraseIdx_cons_succ,List.map_cons,List.prod_cons]; rw [mul_sum]; rw [sub_eq_add_neg,← Finset.sum_neg_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun j _=> ?_; rw [mul_smul_comm, pow_succ',neg_one_mul,neg_mul,neg_smul] -- edit
lemma emptyW : birth (Wand Q) 1=1:=by apply powers; unfold Wand; simp only [ContinuousLinearMap.sum_apply]; apply sum_eq_zero; intro j _; refine sum_eq_zero fun i _=> ?_; change (Q j i) • vary i (vary j 1)=0; rw [vary_one,map_zero,smul_zero]
noncomputable def offP (A B: Type)[Fintype A][Fintype B] :Alg A→ₐ[ℂ] Alg B:= changeVars 0
lemma pfee (i : A) (l:List A) : offP A U (birth (Wand Q) (atom i * (l.map atom).prod))=∑ j: Fin l.length,((-1:ℂ)^j.val*(Q i (l.get j)-Q (l.get j) i)) • offP A U (birth (Wand Q) ((l.eraseIdx j.val).map atom).prod):=by
    rw [ravels,gathers]; simp only [map_sum,map_smul,map_add,map_mul,offP,change_atom]; simp -- maybe geom
lemma seal0 (t:ℕ)(l:List A)(h:l.length ≤ t): offP A U (birth (Wand Q) (l.map atom).prod)= pf (fun i j=>Q i j-Q j i) t l • (1:Alg U):=by
    induction t generalizing l with
    | zero=> cases l with|nil=> rw [show (List.map (atom (A:=A)) []).prod=1 from rfl,emptyW,map_one]; simp [pf]|cons i l=>simp at h
    | succ t ih=> cases l with
        | nil=> rw [show (List.map (atom (A:=A)) []).prod=1 from rfl, emptyW,map_one]; simp [pf]
        | cons a l=> rw [List.map_cons,List.prod_cons,pfee,pf,Finset.sum_smul]; refine Finset.sum_congr rfl fun i _=> ?_ ;  rw [ih]; rw [smul_smul]; rw [List.length_cons,Nat.add_le_add_iff_right] at h; exact (List.length_eraseIdx_le ..).trans h
-- pf change occ
lemma clefts (f:B→A)(C:B→B→ℂ)(L:A→ A→ℂ)(h:∀ i j:B,C i j=L (f i) (f j))(t:ℕ)(l:List B): pf L t (l.map f)=pf C t l:=by
    induction t generalizing l with
    | zero=> cases l <;>rfl
    | succ t ih=> cases l with
       | nil=>rfl
       | cons a l=>
          rw [List.map_cons,pf,pf]; let H:=finCongr (show (List.map f l).length=l.length from List.length_map f); refine Fintype.sum_equiv H _ _ ?_
          intro i; have hx:i.val=(H i).val:=rfl; have hl (i): (l.map f).get i=f (l.get (H i)):=by simp [List.get_eq_getElem,H]
          rw [hl,show i.val=(H i).val from rfl,List.eraseIdx_map, ih,h] -- lemma
end YM.Arise.Pair
#print axioms YM.Arise.Pair.seal0
