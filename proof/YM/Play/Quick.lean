import YM.Play.Dukes
/-! # contraction and conditional Wick identities (exactly oriented counting), all complex, no positivity.
 Matrix coefficients `Q i j` on left leg i of applied contraction v j v i, arbitrary (if doubled provide compensation in the matrix, not Wand). -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*}[Fintype A][Fintype B][Fintype T]{X U V:Finset A}{Z :Finset B}{n m i k:ℕ}
section
variable (P Q: Matrix A A ℂ)
lemma capV (i:A) : Commute (Creek.v i) (Wand Q) := finiteComm _ _ fun a _=> finiteComm _ _ fun b _=> timesComm (swapsV ..) _
lemma wander : Commute (Wand P) (Wand Q):=by
    have hv i j : Commute (Wand Q) (P i j • (Creek.v j * Creek.v i)) := timesComm ((capV Q j).symm.mul_right (capV Q i).symm) _
    refine (finiteComm _ _ (fun i _=> finiteComm _ _ (fun j _=> hv i j))).symm
lemma addition : Wand P+Wand Q=Wand (P+Q):=by
   apply ContinuousLinearMap.ext; intro i
   unfold Wand; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,← Finset.sum_add_distrib]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; exact (add_smul (P j k) (Q j k) (Creek.v k (Creek.v j i))).symm
lemma relay : birth (Wand (P+Q))=birth (Wand P)*birth (Wand Q):=by
   letI: NormedAlgebra ℚ (EndA A):= .restrictScalars ℚ ℂ _; rw [←addition]; exact NormedSpace.exp_add_of_commute (wander P Q)
end
lemma billChain (M:Matrix A B ℂ)(j:B)(x:Alg A) : Creek.v j (changeVars M x)= changeVars M (∑ i,M i j • Creek.v i x):=by
     have h (L:List A): Creek.v j (changeVars M (L.map atom).prod)=changeVars M (∑ i,M i j • Creek.v i (L.map atom).prod):=by
          induction L with
          | nil=> simp [v,vary_one]
          | cons a L ih =>
            let y:=(L.map atom).prod; rw [List.map_cons,List.prod_cons,map_mul]; change vary j _=_
            have ht a : Creek.v j (changeVars M (atom a))= M a j • 1:=by
                rw [change_atom,map_sum,sum_eq_single j,map_smul,show Creek.v j (atom j)=1 from vary_self j]; intro i _ h; rw [map_smul,show Creek.v j (atom i)=0 from vary_off j i h.symm,smul_zero]
                simp
            rw [vary_mul, show vary j _=M a j • _ from ht a] 
            have hm (x:Alg A):changeVars M (grade x)=grade (changeVars M x):=(exterior_parity _ _).symm
            rw [←hm]; change (M a j • 1)* _ + _ * Creek.v j (changeVars M y)=changeVars M (∑ i,M i j • Creek.v i (atom a*y)) -- syntax undo simp
            simp_rw [show ∀ i:A,Creek.v i (atom a*y)= Creek.v i (atom a)*y+grade (atom a)*Creek.v i y from fun i=>vary_mul ..,smul_add,sum_add_distrib,map_add]
            congr 1
            · rw [sum_eq_single a]; change _= changeVars M ( M a j • (vary a (atom a)*y)); rw [vary_self,one_mul,map_smul,smul_mul_assoc,one_mul]; -- check
              intro i _ h; rw [show Creek.v i (atom a)=0 from vary_off i a h,zero_mul,smul_zero]; simp
            · rw [show Creek.v j (changeVars M y)=_ from ih,map_sum,mul_sum,map_sum]; apply sum_congr rfl; intro k _; rw [map_smul,map_smul,map_mul, mul_smul_comm]
     have hz i : Creek.v j (changeVars M (mono i)) = changeVars M (∑ a,M a j • Creek.v a (mono i)):=by
         obtain ⟨f,-,-,hf⟩:=expression i; rw [hf]; simpa only [List.map_ofFn] using h (List.ofFn f)
     rw [← write x]; calc
       _ = ∑ i,coef i x • Creek.v j (changeVars M (mono i)) := by simp only [map_sum,map_smul]
       _ = _ := by
        simp only [hz,map_sum,map_smul,smul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> smul_comm ..
lemma erosion (M:Matrix A B ℂ)(Q:Matrix B B ℂ)(x:Alg A): Wand Q (changeVars M x)=changeVars M (Wand (M * Q * M.transpose) x):=by
    have hx i j : Creek.v j (Creek.v i (changeVars M x))= changeVars M (∑ a,∑ b,(M a i * M b j) • Creek.v b (Creek.v a x)):=by
         rw [billChain,billChain]; apply congr_arg; simp_rw [map_sum,map_smul,smul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [smul_smul,mul_comm]
    unfold Wand; simp_rw [ContinuousLinearMap.sum_apply,map_sum,ContinuousLinearMap.smul_apply]; let Z i j := (changeVars M) (Creek.v j (Creek.v i x))
    change ∑ i:B,∑ j:B,Q i j • (Creek.v j (Creek.v i (changeVars M x)))=∑ i:A,∑ j:A,changeVars M ((M*Q*M.transpose) i j • Creek.v j (Creek.v i x))
    simp_rw [hx,map_sum,map_smul,smul_sum,smul_smul, Matrix.mul_apply,transpose_apply,Finset.sum_mul,sum_smul]
    let R (a b:B) (i j:A):= (Q a b*(M i a*M j b)) • Z i j
    calc
     _ = ∑ i,∑ a,∑ b,∑ j,R a b i j := by change (∑ a,∑ b,∑ i,∑ j,R a b i j)=_; refine Eq.trans (sum_congr rfl (g:=fun a =>∑ i,∑ b,∑ j,R a b i j) (fun i _=> sum_comm)) sum_comm -- edit
     _ = _:=by
      apply sum_congr rfl; intro i _; refine Eq.trans (sum_congr rfl (g:=fun a=> ∑ j,∑ b,R a b i j) (fun _ _=>sum_comm)) ?_; rw [sum_comm]; refine sum_congr rfl fun b _=> ?_; rw [sum_comm]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro a _; unfold R; rw [show Q a x * _=M i a * Q a x * M b x from (by ring)]; -- edit
      -- actually ∑ a:B ∑ b:B ∑ j:A = ∑ j:A ∑ b:B ∑ a:B; simp
lemma transfer (M: Matrix A B ℂ) (Q: Matrix B B ℂ)(x: Alg A) : birth (Wand Q) (changeVars M x)= changeVars M (birth (Wand (M*Q*M.transpose)) x):=by
    let Y:=Wand (M*Q*M.transpose); let T:=Wand Q; have he n : (T^n:EndA B) (changeVars M x)=changeVars M ((Y^n:EndA A) x):=by
         induction n with | zero=>simp | succ n h=> rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,h]; exact erosion M Q _
    let A':=(changeVars M).toLinearMap.toContinuousLinearMap; refine (Stays.birther T _).unique ((A'.hasSum (Stays.birther Y x)).congr_fun (fun i=>?_))
    change (i.factorial:ℂ)⁻¹ • (((T^i): EndA B) _) = changeVars M ((i.factorial:ℂ)⁻¹ • ((Y^i): EndA A) x); rw [he,map_smul]
-- exact cumulative
open Cove
lemma stitches (M:Matrix A B ℂ)(N:Matrix B T ℂ)(P:Matrix A A ℂ)(Q:Matrix B B ℂ)(x:Patio A): splash N Q (splash M P x)= splash (M*N) (M*Q*M.transpose+P) x:=by
    apply Subtype.ext; change changeVars N (birth (Wand Q) (changeVars M _))= changeVars _ (birth (Wand _) x.val); rw [transfer, change_mul,relay]; rfl
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.stitches
