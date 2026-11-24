import YM.Play.Cider
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*} {U:Finset A}{V:Finset B}{n i k:ℕ}{c d x y:ℝ}
lemma centP {L:poly A→ₗ[ℂ]poly B} (h:∀ i:A→₀ℕ,tags U n i→∀ b:ℂ,cents (L (monomial i b))≤ c*‖b‖){p:poly A}(hp:p∈Camp U n): cents (L p) ≤ c*cents p:=by
   nth_rw 1 [p.as_sum]; rw [map_sum]; refine (money _ _).trans ?_; unfold cents; rw [mul_sum]; exact sum_le_sum fun i hi=> h i (stampC hp i hi) _
lemma scar (L: List A)(h:∀ i∈L,i∈U): winks (F:=ℂ) L∈Camp U L.length:=by
    induction L with
    | nil=>simp only [winks,List.map_nil,List.prod_nil]; exact genesis
    | cons a L ih=> rw [List.length_cons,Nat.add_comm _ 1]; exact manufacture (xrise a (h _ (List.mem_cons_self ..))) (ih fun i hi=>h i (List.mem_cons_of_mem _ hi))
lemma lipid (i:A) : cents (MvPolynomial.X i:Papers A ℂ)=1:= by rw [MvPolynomial.X,solely]; simp
lemma slim (l: List A): cents (winks l (F:=ℂ)) ≤ 1:=by induction l with
   | nil=> unfold winks; simp only [List.map_nil,List.prod_nil]; rw [← map_one (MvPolynomial.C : ℂ →+* poly A),coinride]; simp
   | cons a l ih=> refine (bag (MvPolynomial.X a) (winks l)).trans (?_); rw [lipid,one_mul]; exact ih
-- ∥slit∥
lemma prices (b:A→ℂ)(hx:∀ i∈U,‖b i‖≤ c)(hc:0 ≤ c) (p:poly A)(h:p∈Camp U n): cents (slit b p) ≤ n*c*cents p:=by
    have hh l (hl:∀ i∈l,i∈U): cents (slit b (winks l)) ≤ l.length*c:=by
        induction l with
        | nil=> rw [show slit b (winks [])=0 from (slit b).map_one_eq_zero, zero_cent]; simp
        | cons a l ih=>
           have hz:∀ i∈ l,i∈ U:=fun i hi=> hl i (List.mem_cons_of_mem _ hi); let y:=winks (F:=ℂ) l; change cents (slit b (MvPolynomial.X a *y)) ≤ _
           rw [slit_prod]; have ht:= (bag (X a) (slit b y)).trans (by simpa only [lipid,one_mul] using ih hz); have he : cents (C (b a)*y) ≤ c:=by rw [C_mul',smul_cent]; exact (mul_le_of_le_one_right (norm_nonneg _) (slim l)).trans (hx _ (hl _ (List.mem_cons_self ..)))
           refine (wealth _ _).trans ((add_le_add ht he).trans (le_of_eq ?_)); rw [List.length_cons]; push_cast; ring
    refine centP (L:=(slit b).toLinearMap) (fun i hi a=>?_) h; obtain ⟨l,he,hx,hp⟩:= sprout _ a hi.points; rw [hp,C_mul',map_smul,smul_cent]; have ht: l.length≤n:=hx.trans_le hi.size; exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right ((hh l he).trans (by gcongr)) (norm_nonneg _))
lemma dental (b:A→ℂ) {p:poly A} (h:p∈Camp U n): slit b p ∈ Camp U n:=by
    have hh (l:List A)(hl:∀ i∈l,i∈U): slit b (winks l) ∈ Camp U l.length:=by
      induction l with
      | nil=> rw [show slit b (winks [])=0 from (slit b).map_one_eq_zero]; exact Submodule.zero_mem _
      | cons a l ih=>
        have h:∀ i∈l,i∈U:= fun i hi=>hl i (List.mem_cons_of_mem _ hi); change slit b (MvPolynomial.X a * winks l) ∈ _; rw [slit_prod, List.length_cons, Nat.add_comm _ 1]; exact Submodule.add_mem _ (manufacture (xrise _ (hl _ (List.mem_cons_self ..))) (ih h)) (manufacture (token (n:=1) _) (scar _ h))
    rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ fun i hi=>?_ ; obtain ⟨l,he,hx,hL⟩:=sprout _ (coeff i p) (stampC h _ hi).points; rw [hL,C_mul',(slit b).map_smul]; exact Submodule.smul_mem _ _ (shadeC (hh l he) (Finset.Subset.refl _) (hx.trans_le (stampC h _ hi).size))
lemma milky (Q: Next.Rank.Normal.Symmetric A)(p:poly A)(h:p∈Camp U n): milk Q p∈Camp U n:=by
    have h l (hl:∀ i∈l,i∈U): milk Q (winks l) ∈ Camp U l.length:=by induction l with
       | nil=> rw [show milk Q (winks [])=1 from Next.Rank.Normal.pure Q]; exact genesis
       | cons a l ih=>
         specialize ih (fun i hi=>hl i (List.mem_cons_of_mem _ hi)); change milk Q (MvPolynomial.X a*winks l)∈_; rw [feeds,List.length_cons,Nat.add_comm _ 1]; exact Submodule.add_mem _ (manufacture (xrise _ (hl _ (List.mem_cons_self ..))) ih) (shadeC (dental _ ih) (Finset.Subset.refl _) (by omega))
    rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ (fun i hi=>?_); have hv:= stampC ‹p∈Camp U n› _ hi; obtain ⟨l,hh,hz,hL⟩:= sprout _ (coeff i p) hv.points; rw [hL,C_mul',map_smul]; exact Submodule.smul_mem _ _ (shadeC (h l hh) (Subset.refl _) (hz.trans_le hv.size))
def Pane (Q: Next.Rank.Normal.Symmetric A)(U:Finset A)(c:ℝ):Prop:=∀ i∈U,∀ j∈U,‖Q.cov i j‖≤c
variable (Q R:Next.Rank.Normal.Symmetric A)
def tumbler (n:ℕ)(c:ℝ):ℝ:= (n*c+1)^n
lemma oatmeal (p: List A)(hp:∀ i∈p,i∈U)(h:Pane Q U c)(he:0≤ c)(hz:p.length≤n): cents (milk Q (winks p))≤ (n*c+1)^p.length:=by
    induction p with
    | nil=> rw [show milk Q (winks [])=1 from Next.Rank.Normal.pure Q,← map_one (MvPolynomial.C:ℂ→+* poly A),coinride]; simp
    | cons a L ih=>
      have hh:L.length≤n := by rw [List.length_cons] at hz; omega
      have hL i (hi:i∈L):i∈U:=hp _ (List.mem_cons_of_mem _ hi); have hx:= milky Q _ (shadeC (scar L hL) (Finset.Subset.refl _) hh)
      let p:= (n:ℝ)*c; have hc:0 ≤ p:=by unfold p; positivity
      have hm := ih hL hh; have hy:= (prices _ (h a (hp _ (List.mem_cons_self ..))) he _ hx).trans (mul_le_mul_of_nonneg_left hm hc)
      let x:= winks (F:=ℂ) L; change cents (milk Q (MvPolynomial.X a*x))≤ _; rw [feeds,List.length_cons,pow_succ']; refine (wealth _ _).trans ((add_le_add ((bag _ _).trans (c:=(n*c+1)^L.length) (by rw [lipid,one_mul]; exact hm)) hy).trans (le_of_eq ?_)); ring
lemma calculate (p:poly A)(hp:p∈Camp U n)(h:Pane Q U c)(he:0 ≤ c): cents (milk Q p) ≤ tumbler n c*cents p:=by
    apply centP (L:=milk Q) (fun i hi b=>?_) hp; obtain ⟨l,hL,hl,hp⟩:=sprout _ b hi.points; rw [hp,C_mul',map_smul,smul_cent]
    have hv:=hl.trans_le hi.size; have hc:1 ≤ (n:ℝ)*c+1:=by have h:=mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) he; linarith
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right ((oatmeal Q l hL h he hv).trans (pow_le_pow_right₀ hc hv)) (norm_nonneg _)
lemma floss (b c:A→ℂ)(p:poly A): slit b p-slit c p=slit (b-c) p:=by
    suffices he: slit (b-c) p+slit c p=slit b p by rw [← he]; abel
    rw [← slit_linear,sub_add_cancel]
lemma settle (Q R:poly A)(c :ℂ): MvPolynomial.C c*Q-MvPolynomial.C c*R=c • (Q-R):=by rw [C_mul',C_mul',smul_sub]
def steely (n:ℕ)(c:ℝ):ℝ:= n*n*tumbler n c -- n*n implicits?
lemma riseCost (p:poly A)(hp:p∈Camp U n)(hQ:Pane Q U c)(hr:Pane R U c)(hy:Pane (Q+-R) U d)(hc:0≤ c)(hd:0≤d):
    cents (milk Q p - milk R p) ≤ steely n c*d*cents p:=by
    let k:ℝ:=(n:ℝ)*c+1; have hk:1 ≤ k:=le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hc)
    have hm l (h:l.length≤n) (hh:∀ i∈l,i∈U): cents (milk Q (winks l)-milk R (winks l))≤ l.length*n*d*k^l.length:=by
        induction l with
        | nil=> change cents (milk Q 1 - milk R 1) ≤ _; simp
        | cons a L ih=>
          let p:= winks (F:=ℂ) L; let pQ:= milk Q p; let pR:=milk R p; have ht:L.length≤n:= by rw [List.length_cons] at h; omega
          have hi:∀ i∈L,i∈U:= fun i hi=>hh i (List.mem_cons_of_mem _ hi); let v:= cents (pQ-pR); have hz:v ≤ _:= ih ht hi
          let y:= Q.cov a; let x:= R.cov a
          have hp':p∈ Camp U n:= shadeC (scar _ hi) (Subset.refl _) ht; have hP:pR∈ Camp U n:=milky R p hp'; have hr':pQ-pR∈Camp U n:=Submodule.sub_mem _ (milky Q _ hp') hP; have ha:= hh a (List.mem_cons_self ..)
          have h1 : cents (slit (y-x) pR) ≤ ((n:ℝ)*d)*k^L.length:=by
             refine (prices _ (?_) hd pR hP).trans (mul_le_mul_of_nonneg_left (oatmeal R _ hi hr hc ht) (mul_nonneg (Nat.cast_nonneg _) hd)); intro i hi; unfold y x; rw [Pi.sub_apply,sub_eq_add_neg]; exact hy a ha i hi
          have h2:= prices _ (hQ _ ha) hc _ hr'; change cents (milk Q (X a*p)-milk R (X a*p)) ≤ _; rw [feeds,feeds,List.length_cons,pow_succ']
          change cents (X a*pQ+slit y pQ-(X a*pR+slit x pR)) ≤ _; rw [show X a*pQ+slit y pQ-(X a*pR+slit x pR)=(X a*(pQ-pR)+slit y (pQ-pR))+slit (y-x) pR from ?xp]; swap
          case xp=> rw [← floss, map_sub,mul_sub]; change MvPolynomial.X a*pQ+_-(MvPolynomial.X a*pR+_)=_; abel
          refine (wealth _ _).trans ((add_le_add ((wealth _ _).trans (add_le_add (bag _ _) h2)) h1).trans (?_))
          rw [lipid, one_mul]; change v+(n:ℝ)*c*v+((n:ℝ)*d)*k^_ ≤ _
          have hv:= mul_le_mul_of_nonneg_left hz (zero_le_one.trans hk); have hm:= le_mul_of_one_le_left (show 0 ≤ ((n:ℝ)*d)*k^L.length from mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (pow_nonneg (zero_le_one.trans hk) _)) hk
          push_cast at *; unfold k at *; linarith only [hm,hv]
    refine centP (L:=milk Q-milk R) (?_) hp; intro i hi a; obtain ⟨l,he,hp',hL⟩:=sprout _ a hi.points; rw [hL]; change cents (milk Q (C _ * winks l)-milk R _ ) ≤ _
    rw [drink,drink,settle,smul_cent,mul_comm]; have hv:= hp'.trans_le hi.size
    refine mul_le_mul_of_nonneg_right ((hm l hv he).trans (le_trans (b:=(n:ℝ)*n*d*k^n) ?_ (le_of_eq ?_))) (norm_nonneg _)
    · push_cast; gcongr
    unfold steely tumbler k; try push_cast
    ring
end YM.QCD.Bera
#print axioms YM.QCD.Bera.riseCost
