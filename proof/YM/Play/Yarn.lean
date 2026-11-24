import YM.Play.Thirst
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*} {U W:Finset A}{V:Finset B}{n i m k:ℕ}{c d x y:ℝ}
variable {Q:Next.Rank.Normal.Symmetric A}
-- factor. Calm cross; no tiling state.Y
lemma slit_n (b:A→ℂ)(h:∀ i∈U,b i=0){p:poly A}(hp:p∈Camp U n): slit b p=0:=by
   have hg (L:List A)(ht:∀ i∈L,i∈U): slit b (winks L) = 0:=by
       induction L with
       | nil=>exact (slit b).map_one_eq_zero
       | cons i L ih=>
         change slit b (X i*winks L)=_; rw [slit_prod,ih (fun a ha=>ht a (List.mem_cons_of_mem _ ha)), h _ (ht _ (List.mem_cons_self ..))]; simp
   rw [p.as_sum,map_sum]; apply sum_eq_zero; intro i hi; obtain ⟨l,hL,hv,r⟩:=sprout i (coeff i p) (stampC hp i hi).points; rw [r,C_mul',(slit b).map_smul,hg l hL,smul_zero]
lemma stills (h:∀ i∈U,∀ j∈W,Q.cov i j=0){p s:poly A}(hp:p∈Camp U n)(hs:s∈Camp W m): milk Q (p*s)=milk Q p*milk Q s:=by
   have ht (L:List A)(he:∀ i∈L,i∈U): milk Q (winks L*s)=milk Q (winks L)*milk Q s:=by
       induction L with
       | nil=> unfold winks; simp
       | cons i L ih=>
         let x:=winks (F:=ℂ) L; change milk Q (_*x*s)= milk Q (X i*x)*milk Q s; rw [mul_assoc,feeds,ih (fun a ha=>he a (List.mem_cons_of_mem _ ha)),Derivation.leibniz,feeds,slit_n _ (h _ (he i (List.mem_cons_self ..))) (milky Q s hs)]; simp only [smul_eq_mul]; ring
   rw [p.as_sum,sum_mul,map_sum,map_sum,Finset.sum_mul]; apply sum_congr rfl; intro i hi; obtain ⟨l,hL,hv,r⟩:=sprout i (coeff i p) (stampC hp i hi).points; rw [r,mul_assoc,drink,drink,ht l hL,mul_assoc]
section
variable [Fintype A][Fintype B]
def spool (M:Matrix A B ℂ)(i:A) :B→₀ℂ:= Finsupp.equivFunOnFinite.symm (M i)
variable (M N:Matrix A B ℂ)
lemma wool (a:A): exchange (spool M) (X a)=∑ j:B,M a j • X j:=by
   rw [exchange_x,glyph,Finsupp.linearCombination_apply]; change (∑ i∈ (spool M a).support,_) =_
   have he(i:B):spool M a i=M a i:= congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply _) i; simp_rw [he]; apply sum_subset (subset_univ _); intro i hi hk; rw [← he]; rw [Finsupp.notMem_support_iff.mp hk]; exact zero_smul ℂ _
lemma pricing (a:A)(h:a∈U)(hp:bills M U c): cents (exchange (spool M) (X a))≤c:= by
    rw [wool]; exact (money _ _).trans (by simpa only [smul_cent,lipid,mul_one] using hp _ h)
lemma arising (a:A) (h:∀ j,M a j≠0 → j∈V): exchange (spool M) (X a)∈ Camp V 1:=by
    rw [wool]; apply Submodule.sum_mem; intro i _; by_cases he:M a i=0; · rw [he,zero_smul]; exact Submodule.zero_mem _
    exact Submodule.smul_mem _ _ (xrise _ (h i he))
lemma horoscope {p:poly A}(hp:p∈Camp U n)(h:∀ i∈U,∀ j,M i j≠0→ j∈V): exchange (spool M) p ∈ Camp V n:=by
   have hx (L:List A)(hr:∀ i∈L,i∈U):exchange (spool M) (winks L) ∈ Camp V L.length:=by
       induction L with
       | nil=>rw [show exchange (spool M) (winks [])=1 from map_one _]; exact genesis
       | cons i L ih=> change exchange (spool M) (X i*winks L)∈_; rw [map_mul,List.length_cons,Nat.add_comm _ 1]; exact manufacture (arising _ i (h i (hr _ (List.mem_cons_self ..)))) (ih fun j hj=> hr j (List.mem_cons_of_mem _ hj))
   rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ fun i hi=> ?_; obtain ⟨l,he,hv,r⟩:=sprout i (coeff i p) (stampC hp i hi).points; rw [r,C_mul',map_smul]; exact Submodule.smul_mem _ _ (shadeC (hx l he) (Subset.refl _) (hv.trans_le (stampC hp i hi).size))
lemma balm (L:List A)(hr:∀ i∈L,i∈U)(h:bills M U c)(hc:1 ≤c): cents (exchange (spool M) (winks L)) ≤ c^L.length:=by
    induction L with
    | nil=> rw [show exchange (spool M) (winks [])=1 from map_one _, ← map_one (MvPolynomial.C:ℂ→+*poly B),coinride]; simp
    | cons i L ih=> change cents (exchange (spool M) (X i*winks L)) ≤ _; rw [map_mul,List.length_cons,pow_succ']; exact (bag _ _).trans (mul_le_mul (pricing M _ (hr _ (List.mem_cons_self ..)) h) (ih fun i hi=>hr _ (List.mem_cons_of_mem _ hi)) (cent _) (zero_le_one.trans hc)) -- cent vs Rise
lemma gusto {p:poly A}(hp:p∈Camp U n)(h:bills M U c)(hc:1≤c): cents (exchange (spool M) p)≤ c^n*cents p:=by
     apply centP (L:=(exchange (spool M)).toLinearMap) ?_ hp; intro i hi a; obtain ⟨l,he,hv,r⟩:=sprout _ a hi.points; rw [r,C_mul',map_smul,smul_cent,mul_comm]; exact mul_le_mul_of_nonneg_right ((balm M l he h hc).trans (pow_le_pow_right₀ hc (hv.trans_le hi.size))) (norm_nonneg _)
lemma gape (a:A)(h:a∈U)(he:bills (M-N) U d): cents (exchange (spool M) (X a)-exchange (spool N) (X a))≤d:=by
   rw [show exchange (spool M) (X a)-exchange (spool N) (X a)=exchange (spool (M-N)) (X a) from ?_]; exact pricing (M-N) a h he; rw [wool,wool,wool,← sum_sub_distrib]; exact sum_congr rfl fun j _=> (sub_smul ..).symm
lemma virtue {p:poly A}(hp:p∈Camp U n)(h:bills M U c)(ht:bills N U c)(hc:1 ≤ c)(hh:bills (M-N) U d)(hd:0 ≤d): cents (exchange (spool M) p-exchange (spool N) p) ≤ n*d*c^n*cents p:=by
     have hL (L:List A)(he:∀ i∈L,i∈ U):cents (exchange (spool M) (winks L)- exchange (spool N) (winks L))≤ L.length*d*c^L.length:=by
          induction L with
          | nil=>change cents (exchange _ 1-exchange _ 1)≤_; simp
          | cons i L ih=>
             let a:= exchange (spool M) (X i); let b:=exchange (spool N) (X i); let x:=exchange (spool M) (winks L); let y:=exchange (spool N) (winks L); have hi:=he i (List.mem_cons_self ..); have hp j (hj:j∈L):j∈U:=he _ (List.mem_cons_of_mem _ hj)
             change cents (exchange (spool M) (X i*winks L)-exchange (spool N) (X i*winks L))≤ _; rw [map_mul,map_mul]; change cents (a*x-b*y)≤_; rw [show a*x-b*y=(a-b)*x+b*(x-y) from by ring]
             have he:= mul_le_mul (gape M N _ hi hh) (balm M L hp h hc) (cent _) hd; have hv:=mul_le_mul (pricing N _ hi ht) (ih hp) (cent _) (zero_le_one.trans hc); refine (wealth _ _).trans ((add_le_add ((bag _ _).trans he) ((bag _ _).trans hv)).trans ?_)
             rw [List.length_cons,pow_succ']; push_cast; have h:=le_mul_of_one_le_left (mul_nonneg hd (pow_nonneg (zero_le_one.trans hc) L.length)) hc; linarith only [h]
     refine centP (L:= (exchange (spool M)).toLinearMap-(exchange (spool N)).toLinearMap) (?_) hp; intro i hi a; obtain ⟨l,he,hz,r⟩:=sprout _ a hi.points; rw [r,C_mul',map_smul,smul_cent,mul_comm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (hL l he).trans (by have ht:=hz.trans_le hi.size; have hx:0 ≤c:=zero_le_one.trans hc; gcongr)
end
end YM.QCD.Bera
#print axioms YM.QCD.Bera.virtue
