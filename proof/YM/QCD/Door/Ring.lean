import YM.QCD.Bay.Lotus
/-! # Moving both levels of innovations. Covariance not assumed of evaluation tags. Exact.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Grass Creek Ledge Function NormedSpace Finset Lat Kit
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
variable {A B C D: Type*}[Fintype A][Fintype B][Fintype C]

lemma dont (i:A) (j:A): vary i (atom j)=if i=j then 1 else 0:=by
  split
  next h=>subst i; exact vary_self _
  next h=> exact vary_off _ _ h -- syntax
lemma chain (V:Matrix A B ℂ)(i:B)(x:Alg A): vary i (changeVars V x)=∑ j: A,V j i • changeVars V (vary j x):=by
   let F:= changeVars V; have hf (j:A): vary i (F (atom j))= V j i • 1:=by
      dsimp only [F]; rw [change_atom,map_sum,sum_eq_single i]; · simp
      · intro b _ h; rw [map_smul,dont,if_neg (Ne.symm h),smul_zero]
      simp
   have hp (y:List A): vary i (F (y.map atom).prod)=∑ j: A,V j i • F (vary j (y.map atom).prod):=by induction y with
      | nil=> simp only [List.map_nil,List.prod_nil,map_one,vary_one,map_zero,smul_zero,sum_const_zero]
      | cons j y ih=>
        have he:grade (F (atom j))= -F (atom j):=by dsimp only [F]; rw [changeVars,exterior_parity,grade_atom,map_neg]
        simp only [List.map_cons,List.prod_cons,map_mul,vary_mul, hf,he,grade_atom,dont,ih,map_add,map_neg,map_mul, smul_add,sum_add_distrib]; simp only [mul_sum, mul_smul_comm]; apply congr_arg₂ (·+·) _ rfl
        rw [sum_eq_single j]; · simp
        · intro a _ h; rw [if_neg h,map_zero,zero_mul,smul_zero]
        simp
   have hm (s:Finset A): vary i (F (mono s))=∑ j:A,V j i • F (vary j (mono s)):=by obtain ⟨w,-,-,he⟩:=expression s; rw [he]; simpa only [List.map_ofFn] using hp (List.ofFn w)
   change vary i (F x)=_; rw [← write x]; change _=∑ j:A,_ • F (vary _ (∑ s:Finset A,coef s x • mono s)); simp only [map_sum,map_smul,smul_sum,hm]; rw [sum_comm]; refine sum_congr rfl fun j _=>?_ ; apply sum_congr rfl; intro i _; rw [smul_comm]

lemma wharfP (U : Matrix A A ℂ) (W : Matrix B B ℂ) (i:A)(x:Dirac (A⊕B)): vary (pet (head A B) i) (disguise (whole U W) x)=∑ j:A,U j i • disguise (whole U W) (vary (pet (head A B) j) x):=by
   unfold disguise adapter; rw [chain]; simp only [pet,Fintype.sum_sum_type]; -- brands map; simp
   simp [Fintype.sum_sum_type, whole]
lemma wharfM (U:Matrix A A ℂ)(W:Matrix B B ℂ)(i:A)(x:Dirac (A⊕B)): vary (met (head A B) i) (disguise (whole U W) x)=∑ j:A,(star U) i j • disguise (whole U W) (vary (met (head A B) j) x):=by
   unfold disguise adapter; rw [chain]; simp only [met,Fintype.sum_sum_type]; -- brands map; simp
   simp [Fintype.sum_sum_type, whole_star,whole]

-- tagged representation. Gamma-5 coincidental name.
lemma suitP (H:Matrix A A ℂ)(x:Dirac (A⊕B)): pond (head A B) H x = ∑ i,∑ j,H i j • (vary (met (head A B) j) (vary (pet (head A B) i) x)):=by
 simp only [pond,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]; rfl

-- source map g.U; transforms M.Source=U M.Dest U*.
lemma gust (R: Matrix A A ℂ)(W:Matrix B B ℂ)(H:Matrix A A ℂ)(x:Dirac (A⊕B)):
    disguise (whole R W) (pond (head A B) (R*H*star R) x)=pond (head A B) H (disguise (whole R W) x):=by
    let U := disguise (whole R W); let G i j := U (vary (met (head A B) j) (vary (pet (head A B) i) x)); rw [suitP,suitP]; simp_rw [map_sum,map_smul,Matrix.mul_apply,sum_smul, sum_mul, sum_smul,wharfP,map_sum,map_smul,wharfM,smul_sum]; change _ = _
    conv_lhs=>
      enter [2,a,2,b]; rw [sum_comm]
    -- a b i j -> i j a b
    conv_lhs=>
      enter [2,a]
      rw [sum_comm]
    rw [sum_comm]; apply sum_congr rfl; intro k _
    conv_lhs=>
      enter [2,a]; rw [sum_comm]
    rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro q _
    rw [smul_smul,smul_smul]; congr 1; ring
end YM.QCD.Sway
