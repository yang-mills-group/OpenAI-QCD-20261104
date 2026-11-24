import YM.QCD.Estimate.Gram
import YM.QCD.Kites.Bake
import YM.QCD.Oasis.Floss
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Finset Filter MeasureTheory RG ConnectedActivityE6 Pressure Lat Grass Cost Cove Creek
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff Classical
variable {I:Type*}[Fintype I][DecidableEq I]{c:Side}{N:ℕ}{w:ℝ}
lemma sliding (P:List I)(J:I): bar J * (List.map psi P).prod=(-1:ℂ)^P.length • ((P.map psi).prod*bar J):=by
   induction P with
   | nil=> simp
   | cons i l ih=> simp only [List.length_cons,List.map_cons,List.prod_cons]; rw [← mul_assoc,atom_flip (Sum.inr J) (Sum.inl i)]; change -(psi i*bar J)*_= _; rw [neg_mul,mul_assoc,ih,mul_smul_comm,pow_succ]; rw [mul_assoc]; simp
lemma splits (P:List (Pairs I)) :∃ (L R:List I)(u:ℂ),‖u‖=1∧L.length+R.length=P.length ∧ (P.map atom).prod=u • ((L.map psi).prod*(R.map bar).prod):=by
    induction P with
    | nil=> exact ⟨[],[],1,by simp, rfl,by simp⟩
    | cons i l ih=>
        obtain ⟨L,R,u,hU,hp,h⟩:=ih; simp only [List.map_cons,List.prod_cons,h,List.length_cons]; cases i with
        | inl i=> refine ⟨i::L,R,u,hU,(by rw [← hp]; simp only [List.length_cons]; omega),?_⟩; simp only [List.map_cons,List.prod_cons,mul_smul_comm,mul_assoc]
        | inr i=> refine ⟨L,i::R,u*(-1)^L.length,(by simp [hU]),(by simp [← hp,Nat.add_assoc]),?_⟩; change bar i*_= _; rw [mul_smul_comm,mul_smul,← mul_assoc (bar i),sliding,smul_mul_assoc]; simp only [List.map_cons,List.prod_cons,mul_assoc]
noncomputable def shot (i :I):I→ℂ:=fun j=>if i=j then 1 else 0
lemma paidμ (i:I): ‖(WithLp.toLp 2 (shot i):Vec I)‖=1:=by
    rw [← sq_eq_sq₀ (by positivity) (by norm_num), EuclideanSpace.norm_sq_eq]; rw [sum_eq_single i]; · simp [shot]
    · intro j _ hj; simp [shot,hj.symm]
    simp
lemma plot (P:List I): ∃ U : Fin P.length→I, (P.map psi).prod=bundle (fun i=> shot (U i))∧ (P.reverse.map bar).prod=twigs (fun i=>shot (U i)):=by
    induction P with
    | nil=> exact ⟨Fin.elim0, by simp [bundle],by simp [twigs]⟩
    | cons i l ih=>
        rw [List.length_cons]; obtain ⟨U,hp,h⟩:= ih
        refine ⟨Fin.cons i U,?_,?_⟩
        · rw [next_b]; simp [List.prod_cons,shot,straw,hp]
        rw [next_t]; simp only [List.reverse_cons,List.map_append,List.prod_append,h]; simp [brin,shot]
lemma plotI (P:List I) :∃ U:Fin P.length →I, (P.map bar).prod=twigs (fun i =>shot (U i)):=by
     obtain ⟨U,hV,h⟩:=plot P.reverse; simp only [List.reverse_reverse] at h
     have he(k m:ℕ)(hp:k=m)(U:Fin k→I)(h:(P.map bar).prod=twigs (fun i:Fin k=>shot (U i))) :∃ V:Fin m→I,(P.map bar).prod=twigs (fun i=> shot (V i)):=by subst k; exact ⟨U,h⟩
     exact he P.reverse.length _ (List.length_reverse) U h
 
lemma purseμ (M:Mx I)(h:IsUnit M.det)(hp:0<w)(hz:‖M⁻¹‖≤w^2)(p:Finset (Pairs I)): ‖seen M (mono p)‖ ≤ w^p.card:=by
    obtain ⟨f,hf,hV,hm⟩:=expression p
    rw [hm, ← List.map_ofFn]; obtain ⟨L,R,u,hU,ht,hK⟩:= splits (List.ofFn f); rw [hK,map_smul,norm_smul,hU,one_mul]
    obtain ⟨U,hL,-⟩:= plot L; obtain ⟨V,hR⟩:=plotI R;
    rw [hL,hR]; rw [List.length_ofFn] at ht; rw [← ht]; -- dependency
    have he(n m:ℕ)(U:Fin n→I)(V:Fin m→I): ‖seen M (bundle (fun i=> shot (U i))*twigs (fun i=> shot (V i)))‖≤w^(n+m):=by
        by_cases hh:n=m
        · subst m
          apply (price_wick M h (Matrix.of fun i=> shot (U i)) (Matrix.of fun i=> shot (V i))).trans; change (∏ i, ‖(WithLp.toLp 2 (shot (U i)):Vec I)‖)*(∏ i, (‖M⁻¹‖ *‖(WithLp.toLp 2 (shot (V i)):Vec I)‖)) ≤ _; simp only [paidμ,prod_const,card_univ,Fintype.card_fin,mul_one,one_pow,one_mul]; rw [show n+n=2*n by omega,pow_mul]; gcongr
        rw [charged M hh]; rw [norm_zero]; positivity
    exact he _ _ U V
lemma seeing (M:Mx I)(h:IsUnit M.det)(hp:0<w)(hz:‖M⁻¹‖≤w^2)(x:Dirac I): ‖seen M x‖ ≤ load (fun _=>w) x :=by
     rw [dry _ (fun _=>hp)]
     nth_rw 1 [← write x]; rw [map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_)
     rw [map_smul,norm_smul,mul_comm,prod_const]; exact mul_le_mul_of_nonneg_right (purseμ M h hp hz i) (norm_nonneg _)
end YM.QCD.Rain
