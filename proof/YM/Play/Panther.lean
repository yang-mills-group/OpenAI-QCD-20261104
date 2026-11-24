import YM.Play.Pond
/-! # multiple contours real operator estimates. Maps on anchors encounter labels.Stem. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera.Oce
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly ProbabilityTheory ConnectedActivityE6.Poll Cove
open scoped BigOperators Topology ContDiff Classical Matrix InnerProductSpace NNReal ENNReal
variable {ι A B J T:Type}[Fintype A][Fintype B][Fintype J][Fintype T] {x y:A→ℝ} {U:Finset A}{m n:ℕ}
-- deterministic point evaluation
abbrev rose (J:Type)[Fintype J](x:A→ℝ) : Papers A (Patio J)→ₐ[Patio J] Patio J:= aeval fun i=>(x i:ℂ) • (1: Patio J)
lemma antiquity (q:poly A)(x:A→ℝ)(i: Patio J) : rose J x (outer q i)= (eve x q) • i:=by
    let P:= Patio J; let f:= (MvPolynomial.map (σ:=A) (algebraMap ℂ P)); let g:= (algebraMap ℂ P).comp ((eve x).toRingHom)
    have he : (rose J x).toRingHom.comp f=g:=by
       ext1 -- ideally names
       · ext i; simp [f,g,rose,eve]
       simp [g,f,rose,eve, Algebra.algebraMap_eq_smul_one]
    rw [outP,map_mul,show rose J x (C i)=i from ?_,show rose J x (f q)=_ from RingHom.congr_fun he q,mul_comm,Algebra.smul_def]; rfl; change aeval _ (C i)=_; simp
lemma passage {F:Submodule ℂ (Patio J)}(x:A→ℝ){p:Papers A (Patio J)}(hp:p∈vault F): rose J x p∈F := by
    rw [p.as_sum,map_sum]; apply Submodule.sum_mem; intro i hi; rw [show monomial _ (coeff i p)=outer (monomial i 1) _ from ?_,antiquity]; exact F.smul_mem _ (hp i); rw [outmono,one_smul]
lemma cylindrical (x:A→ℝ)(a:A) : eve x (MvPolynomial.X a)=(x a:ℂ):= aeval_X ..
-- budget independent of this alphabet card
variable {u v c ε κ:ℝ}
def bill (x:A→ℝ)(X:Finset A)(v:ℝ):Prop:= ∀ i∈ X,‖x i‖≤v
lemma tenderWild (L:List A)(h:∀ i∈L,i∈U)(he:bill x U v)(hc:1≤v): ‖eve x (winks L)‖≤ v^L.length:=by
    induction L with
    | nil=> rw [show eve x (winks [])=1 from map_one _,norm_one,List.length_nil,pow_zero]
    | cons a L ih=>
      specialize ih (fun i hi=>h i (List.mem_cons_of_mem _ hi)); change ‖eve x (_*winks L)‖≤ _; rw [map_mul,norm_mul,cylindrical,Complex.norm_real,List.length_cons,pow_succ']; exact mul_le_mul (he _ (h _ (List.mem_cons_self ..))) ih (norm_nonneg _) (zero_le_one.trans hc)
lemma tender (p:poly A)(h:p∈Camp U n)(he:bill x U v)(hc:1≤v): ‖eve x p‖ ≤ v^n * cents p:=by
    conv_lhs=>rw [p.as_sum,map_sum]
    unfold cents; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro i hi; obtain ⟨L,hL,hv,hp⟩:= sprout _ (coeff i p) (stampC h _ hi).points
    rw [hp,C_mul',map_smul,norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_right ((tenderWild L hL he hc).trans (pow_le_pow_right₀ hc (hv.trans_le (stampC h i hi).size))) (norm_nonneg _)
lemma torn (x y:A →ℝ)(p:poly A)(h:p∈Camp U n)(he:bill x U v)(hf:bill y U v)(hc:1≤v)(ht:∀ i∈U,‖x i-y i‖≤c)(hy:0 ≤c): ‖eve x p-eve y p‖ ≤ (n*c*v^n)*cents p :=by
   have hp':0≤ v:=zero_le_one.trans hc
   have hh L (h:∀ i∈L,i∈U): ‖eve x (winks L)-eve y (winks L)‖≤ L.length*c*v^L.length:=by induction L with
   | nil=> unfold winks; simp
   | cons a L ih=>
      have hi (j) (hi:j∈L):j∈U:= h j (List.mem_cons_of_mem _ hi); have hv:=h _ (List.mem_cons_self ..); let A:= winks (F:=ℂ) L; let b:ℂ:=x a; let d:ℂ:=y a
      change ‖eve x (_*A)-eve y (_*A)‖≤_; rw [map_mul,map_mul,cylindrical,cylindrical,List.length_cons,pow_succ']
      have h1:‖b*eve x A - b*eve y A‖ ≤ v*(L.length*c*v^L.length):=by rw [← mul_sub,norm_mul]; exact mul_le_mul (by unfold b; rw [Complex.norm_real]; exact he _ hv) (ih hi) (norm_nonneg _) hp'
      have h2: ‖b*eve y A-d*eve y A‖≤ c*v^L.length:=by rw [← sub_mul,norm_mul,show b-d=((x a-y a:ℝ):ℂ) from (Complex.ofReal_sub ..).symm,Complex.norm_real]; exact mul_le_mul (ht _ hv) (tenderWild _ hi hf hc) (norm_nonneg _) hy
      have hp:= le_mul_of_one_le_left (mul_nonneg hy (pow_nonneg hp' L.length)) hc; refine (norm_sub_le_norm_sub_add_norm_sub _ (b*eve y A) _).trans ((add_le_add h1 h2).trans (?_)); push_cast; linarith only [hp]
   conv_lhs=> rw [p.as_sum,map_sum,map_sum,← Finset.sum_sub_distrib]
   unfold cents; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro i hi; obtain ⟨L,he,hx,hz⟩:=sprout _ (coeff i p) (stampC h i hi).points; rw [hz,C_mul',map_smul,map_smul,← smul_sub,norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_right ((hh L he).trans (by have h:=hx.trans_le (stampC h i hi).size; gcongr)) (norm_nonneg _)
lemma cares {p:Papers A (Patio J)}(h:p∈Camp U n)(he:bill x U v)(hc:1≤v): ‖rose J x p‖ ≤ v^n *cents p:=by
    conv_lhs=> rw [p.as_sum,map_sum]
    unfold cents; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro i hi
    rw [show monomial _ (coeff i p)=outer (monomial i 1) (coeff i p) from (by rw [outmono,one_smul]),antiquity,norm_smul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simpa only [solely,norm_one,mul_one] using tender _ (sparks (1:ℂ) (stampC h i hi)) he hc
lemma tang (x y:A →ℝ) (p:Papers A (Patio J))(h:p∈Camp U n)(he:bill x U v)(hf:bill y U v)(hc:1≤v)(ht:∀ i∈U,‖x i-y i‖≤c)(hy:0 ≤c): ‖rose J x p-rose J y p‖ ≤ (n*c*v^n)*cents p:=by
   conv_lhs=> rw [p.as_sum,map_sum,map_sum,← Finset.sum_sub_distrib]
   unfold cents; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro i hi; rw [show monomial _ (coeff i p)=outer (monomial i 1) (coeff i p) from (by rw [outmono,one_smul]),antiquity,antiquity,← sub_smul,norm_smul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); simpa only [solely,norm_one,mul_one] using torn x y _ (sparks (1:ℂ) (stampC h i hi)) he hf hc ht hy
end YM.QCD.Bera.Oce
#print axioms YM.QCD.Bera.Oce.cares
#print axioms YM.QCD.Bera.Oce.tang
