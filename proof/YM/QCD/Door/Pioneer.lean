import YM.QCD.Door.Ring
/-! # Tilt is preserved on pressure. anti-linear exchange before rotation by J. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Grass Creek Ledge Function NormedSpace Finset Lat Kit
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
variable {A B C D: Type*}[Fintype A][Fintype B][Fintype C]

-- atom generator semilin; squares to grade. exact for all n.
def tide (A: Type*) [Fintype A] : Matrix (Pairs A) (Pairs A) ℂ := Matrix.fromBlocks (0:Matrix A A ℂ) (1:Matrix A A ℂ) (-1:Matrix A A ℂ) 0

def surf (A:Type*) [Fintype A]: Dirac A→ₛₗ[starRingEnd ℂ] Dirac A:= (changeVars (tide A)).toLinearMap.comp cc
lemma surf_mul (x y : Dirac A): surf A (x*y)=surf A x*surf A y:=by unfold surf; simp [cc_mul]
lemma surf_P (i:A): surf A (psi i)=bar i:=by unfold surf; rw [LinearMap.comp_apply,cc_atom]; erw [change_atom]; simp [tide, Fintype.sum_sum_type,Matrix.one_apply, ite_smul]
lemma surf_M (i:A): surf A (bar i)= -psi i:=by unfold surf; rw [LinearMap.comp_apply,cc_atom]; erw [change_atom]; simp [tide,Fintype.sum_sum_type, Matrix.one_apply,ite_smul] -- Pieces
lemma surf_one : surf A 1=1:=by unfold surf; rw [LinearMap.comp_apply,cc_one]; exact map_one (changeVars (tide A))
lemma scud (x:Dirac A): surf A (surf A x)=grade x:=by
   have hp (u:List (Pairs A)): surf A (surf A (u.map atom).prod)=grade (u.map atom).prod:=by induction u with
    | nil=> simp [surf_one]
    | cons j u ih=> rw [List.map_cons,List.prod_cons, surf_mul,surf_mul,ih,map_mul]; congr 1; cases j
                    next j=> exact (congr_arg _ (surf_P j)).trans ((surf_M _).trans (grade_atom _).symm)
                    next j=> change surf A (surf A (bar j))= _; rw [surf_M,map_neg,surf_P,grade_atom]
   have he s: surf A (surf A (mono s)) = grade (mono s):=by obtain ⟨w,-,-,hw⟩:= expression s; rw [hw]; simpa only [List.map_ofFn] using hp (List.ofFn w)
   rw [← write x]; simp only [map_sum,map_smul,map_smulₛₗ,he,starRingEnd_apply,star_star]
lemma virgin_v (i:A)(x:Alg A): cc (vary i x)=vary i (cc x):=by
   have he (L: List A):cc (vary i (L.map atom).prod)=vary i (cc (L.map atom).prod):=by
      induction L with
      | nil=> simp [vary_one]
      | cons j L ih=> simp only [List.map_cons,List.prod_cons,vary_mul,dont,map_add,cc_mul, grade_atom, map_neg,cc_atom,ih, apply_ite cc, cc_one, map_zero]
   have h s: cc (vary i (mono s))=vary i (cc (mono s)):=by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa only [List.map_ofFn] using he (List.ofFn w)
   rw [← write x]; simp only [map_sum,map_smul,map_smulₛₗ,h]
lemma sea_p (i:A)(x:Dirac A): vary (.inl i) (surf A x) = -(surf A (vary (.inr i) x)):=by
   change vary (.inl i) (changeVars (tide A) (cc x))= _; rw [chain]; change _= -(changeVars _ (cc _)); simp [Pairs, Fintype.sum_sum_type, tide, Matrix.one_apply, ite_smul, virgin_v]
lemma sea_m (i:A)(x:Dirac A): vary (.inr i) (surf A x)=surf A (vary (.inl i) x):=by
   change vary (.inr i) (changeVars (tide A) (cc x))= _; rw [chain]; change _=changeVars _ (cc _); simp [Pairs,Fintype.sum_sum_type,tide, Matrix.one_apply,ite_smul,virgin_v]
lemma current (H:Matrix A A ℂ)(x:Dirac (A⊕B)): surf _ (pond (head A B) H x)=pond (head A B) (star H) (surf _ x):=by
   rw [suitP,suitP]; simp only [map_sum,map_smulₛₗ,starRingEnd_apply,Matrix.star_eq_conjTranspose]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; refine congr_arg (_ • ·) ?_
   -- exchange
   change surf (A⊕ B) (vary (.inr (.inl i)) (vary (.inl (.inl j)) x))=vary (.inr (.inl j)) (vary (.inl (.inl i)) (surf _ x)); rw [sea_p,map_neg,sea_m]; rw [show vary (.inl (.inl j)) (vary (.inr (.inl i)) x)=_ from CliffordAlgebra.contractLeft_comm _ _ x]; rw [map_neg,neg_neg]; rfl

end YM.QCD.Sway
