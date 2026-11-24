import YM.Massive.PCAC.Mark
/-! Ward on Gaussian. `gauss` uses psi then bar. Lap produces BOTH form(D W D) and the contact `-tr(W D)` with our signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
lemma mark_forms (k:Bool)(W D:Sour A): applyMark k W (form D)=form (if k then W*D else D*W):=by
    cases k with
    | false =>
         simp only [Grass.form, Bool.false_eq_true,↓reduceIte,map_sum, map_smul,LMark,leftP,passB,mul_zero,add_zero,sum_mul,smul_mul_assoc,smul_sum, Matrix.mul_apply,sum_smul,mul_smul]; apply sum_congr rfl; intro u _; rw [sum_comm]
    | true=>
         simp only [Grass.form,↓reduceIte,map_sum,map_smul,LMark,passP,leftB,zero_mul,zero_add,mul_sum,mul_smul_comm,smul_sum,Matrix.mul_apply,sum_smul,mul_smul]
         let f(i j k:A):= W k i • (D i j • (psi j*bar k)); have he : ∀ i j k : A,D i j • (W k i • (psi j*bar k))=f i j k:=fun _ _ _ => smul_comm ..; simp_rw [he]; change (∑ i,∑ j,∑ k,f i j k)=∑ k,∑ j,∑ i,f i j k; rw [sum_comm]; apply Eq.trans _ (sum_comm (f:=fun j k=>∑ i,f i j k)); apply sum_congr rfl; intro i _; rw [sum_comm]
lemma genExp (i j:A)(x:Alg A)(h:Plus x): gen i j (exp x)=exp x * gen i j x:=by
    change atom _ * vary _ (exp x)= _*(atom _* _); rw [varies_exp _ _ h,← mul_assoc,(show atom j * exp x=exp x*atom j from (show Plus (exp x) from (map_weight _ _).trans (congr_arg exp h)).central _),mul_assoc]
lemma mark_gauss (k:Bool)(W D:Sour A): applyMark k W (gauss D)=gauss D*form (if k then W*D else D*W):=by rw [← mark_forms]; unfold gauss; have hv (i j:Pairs A) := genExp i j (form D) (form_plus D); cases k<;> simp [applyMark,hv,mul_sum]

def lobby (D:Sour A)(i:A):Dirac A:= ∑ u:A,D u i • bar u
def station (D:Sour A)(i:A): Dirac A:= ∑ u:A,D i u • psi u
lemma varyP(i:A)(D:Sour A) : vary (Sum.inl i) (form D)=lobby D i:=by
    unfold form lobby; simp only [map_sum,map_smul]; apply sum_congr rfl; intro u _
    have h(j): vary (Sum.inl i) (psi j*bar u)= (if i=j then bar u else 0):=by
         rw [vary_head,vary_off (Sum.inl i) (Sum.inr u) (by simp),mul_zero,sub_zero]; split_ifs with he <;> simp_all [probe]
    simp_rw [h]; simp
lemma varyP'(i:A)(D:Sour A): vary (Sum.inl i) (gauss D)=gauss D*lobby D i:=by unfold gauss; rw [varies_exp _ _ (form_plus D), varyP i]
lemma varyB'(i:A)(D:Sour A): vary (Sum.inr i) (gauss D)= -(gauss D*station D i):=by unfold gauss station; rw [varies_exp _ _ (form_plus D), form_row,mul_neg]
lemma station_hit (D:Sour A)(i j:A) : vary (Sum.inl i) (station D j)=D j i • 1:=by
    unfold station; rw [map_sum, sum_eq_single i];
    · rw [map_smul,vary_self]
    · intro a _ h; rw [map_smul, vary_off (Sum.inl i) (Sum.inl a) (by simp [Ne.symm h]),smul_zero]
    simp
lemma pair_form (D:Sour A)(i j:A): pairD i j (gauss D)= gauss D * ((∑ k:A, ∑ l:A, (D k i * D j l) • (psi l*bar k))- D j i • 1):=by
    change vary _ (vary _ (gauss D))= _; rw [varyB',map_neg,vary_mul,varyP',station_hit,show grade (gauss D)=_ from gauss_plus _,mul_assoc, mul_sub];
    have hv : lobby D i * station D j= -(∑ k:A,∑ l:A,(D k i * D j l) • (psi l*bar k)):=by
         unfold lobby station; simp_rw [sum_mul,mul_sum,smul_mul_assoc,mul_smul_comm, show ∀ p q:A, bar p * psi q= -(psi q * bar p) from fun i j=> atom_flip (A:=Pairs A) (Sum.inr i) (Sum.inl j), smul_neg,sum_neg_distrib, smul_smul]
    rw [hv,mul_neg]; abel
lemma lap_gauss (D W:Sour A) : lap W (gauss D)= gauss D*(form (D*W*D) - (W*D).trace • 1):=by
    unfold lap; have he (i j:A) : W i j • pairD i j (gauss D)= gauss D*(W i j • ((∑ k:A,∑ l:A,(D k i* D j l) • (psi l*bar k))- D j i • 1)):=by rw [pair_form,mul_smul_comm];
    simp_rw [LinearMap.sum_apply,LinearMap.smul_apply, he, ←mul_sum]; apply congr_arg (gauss D*·); unfold form Matrix.trace; simp only [smul_sub,sum_sub_distrib]; congr 1
    · simp_rw [Matrix.mul_apply,smul_sum,sum_mul,sum_smul, smul_smul];
      let f(i j k l:A):=(W i j * (D k i * D j l)) • (psi l*bar k); have hp(k i j l):=(show (D k i* W i j* D j l) • (psi l*bar k)=f i j k l from (by unfold f; ring_nf)); simp_rw [hp]; change (∑ i,∑ j,∑ k,∑ l,f i j k l)= ∑ k,∑ l,∑ j,∑ i,f i j k l; rw [sum_comm]; have hg:= sum_comm (s:=univ) (t:=univ) (f:=fun (x y:A × A)=> f x.2 x.1 y.1 y.2); simpa only [Fintype.sum_prod_type] using hg
    simp only [smul_smul,sum_smul,Matrix.diag_apply,Matrix.mul_apply]
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.lap_gauss
