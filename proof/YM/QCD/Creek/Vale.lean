import YM.QCD.Creek.Bark
/-! # Budget-priced evaluator skeleton at pinned H
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Grass NormedSpace Function Finset
open scoped Topology BigOperators Matrix
variable {A B M:Type*} [Fintype A][Fintype B][Fintype M]
variable (f:Pairs A ↪ M) (z:B ↪ M) (hZ : ∀ i j,f i ≠ z j) (V:Matrix A A ℂ)
def rightM (x: Alg M): EndA M:= (LinearMap.mulRight ℂ x).toContinuousLinearMap
lemma commuting (X:List B) (i:A)(q:Pairs A) (h: ∀ j,f q≠z j) : Commute (v (f q)) (rightM ((X.map (atom∘z)).prod)):=by
    let u:= (X.map (atom∘z)).prod
    have he (i' : A)(p:List B): vary (f q) ((p.map (atom∘z)).prod)=0:=by
      induction p with
      | nil=> rw [List.map_nil,List.prod_nil,vary_one]
      | cons i p ih=> rw [List.map_cons,List.prod_cons,vary_mul,comp_apply,show vary (f q) _=0 from vary_off _ _ (h i),zero_mul,ih,mul_zero,add_zero]
    refine ContinuousLinearMap.ext (fun y=> ?_); change vary _ (y*u)= _ * u; rw [vary_mul,he i,mul_zero, add_zero]; rfl
include hZ
lemma ranger (i:Pairs A)(a: A)(y:Alg B)(H:Alg M): vary (f i) (embed z y)=0:=by
    have hx (L : List B): vary (f i) ((L.map (atom∘⇑z)).prod)=0:=by
      induction L with
      | nil=> simp [vary_one]
      | cons j L ih=> simp only [List.map_cons,List.prod_cons, vary_mul]; rw [show vary (f i) ((atom ∘ ⇑z) j)=0 from vary_off (f i) (z j) (hZ i j), ih,mul_zero,zero_mul,add_zero]
    have hh (s:Finset B): vary (f i) (embed z (mono s))=0:=by
      obtain ⟨t,-,-,he⟩:= expression s; rw [he,map_list_prod, List.map_ofFn]; simpa only [List.map_ofFn,Function.comp_def, embed_atom] using hx (List.ofFn t)
    rw [← write y,map_sum,map_sum]; simp_rw [map_smul,hh,smul_zero,sum_const_zero]
lemma brightV (i:Pairs A)(a:A)(y:Alg B): Commute (rightM (embed z y)) (v (f i)):= Commute.symm (show Commute (v (f i)) _ from ContinuousLinearMap.ext (fun x=> by change vary _ (x*_)= _ * embed z y; rw [vary_mul,ranger f z hZ i a y x,mul_zero, add_zero]; rfl))
lemma accum (y:Alg B): Commute (pond f V) (rightM (embed z y)):= Commute.symm (finiteComm _ _ fun i _=> finiteComm _ _ fun j _=>timesComm (Commute.mul_right (brightV f z hZ (.inr j) i y) (brightV f z hZ (.inl i) i y)) _)
end YM.QCD.Creek
