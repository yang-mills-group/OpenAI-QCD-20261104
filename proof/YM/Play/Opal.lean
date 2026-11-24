import YM.Play.Ember
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera.Oce
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly ProbabilityTheory ConnectedActivityE6.Poll
open scoped BigOperators Topology ContDiff Classical Matrix
variable {α:Type*}[MeasurableSpace α]{μ:Measure α}{A B:Type*}[Fintype A]
-- m real.Cov written complex symmetric through Gauge.S
variable (b:A→ℝ)
def eve (z:A→ℝ) : poly A→ₐ[ℂ] ℂ:= aeval fun i=>(z i:ℂ)
def baron (z:A→ℝ):poly A:= ∑ i, (z i:ℂ) • X i
def foo (g:A→ℝ):= ∑ i,b i*g i
def vie (Q: Next.Rank.Normal.Symmetric A)(b:A→ℝ):ℂ:=∑ i,∑ j,(b i:ℂ)*(b j:ℂ)*Q.cov i j
lemma mast (f:A→ℝ) : eve f (baron b)= ↑(foo b f):=by unfold eve baron foo; rw [map_sum]; simp only [map_smul,aeval_X,smul_eq_mul, Complex.ofReal_sum,Complex.ofReal_mul]
lemma sli (f:A→ℂ): slit f (baron b)= C (∑ j,(b j:ℂ)*f j):=by unfold baron; simp only [map_sum, (slit f).map_smul, slit_X, map_mul,C_mul']
lemma stir {F: A→ℂ} (n:ℕ) : slit F ((baron b)^(n+1))= ((n:ℂ)+1) • ((baron b)^n*slit F (baron b)):=by
   induction n with
   | zero=> simp
   | succ i ih=> rw [pow_succ',Derivation.leibniz,ih]; push_cast; change baron b * _+ (_^(i+1))*_= _; simp_rw [← C_mul', pow_succ',map_add,map_one]; ring
lemma perk (m:A→ℝ)(Q:Next.Rank.Normal.Symmetric A)(p:poly A) : blend Q (fun i=>(m i:ℂ)) (baron b*p)= (foo b m:ℂ)*blend Q (fun i=>(m i:ℂ)) p+ ∑ i,(b i:ℂ)* blend Q (fun i=>(m i:ℂ)) (slit (Q.cov i) p):=by
   unfold baron; simp_rw [sum_mul, smul_mul_assoc,map_sum,map_smul,blended,smul_eq_mul,mul_add]; rw [sum_add_distrib]; apply congr_arg (·+_); unfold foo; push_cast; rw [sum_mul]; apply sum_congr rfl; intro i _; ring
lemma prince (m:A→ℝ)(Q:Next.Rank.Normal.Symmetric A) (n:ℕ):
   let B:= blend Q (fun i=>(m i:ℂ)); B ((baron b)^(n+2))= vie Q b*(n+1) * B ((baron b)^n)+ (foo b m:ℂ)*B ((baron b)^(n+1)):=by
    intro B; rw [show n+2=n+1+1 by omega,pow_succ',show B _= _ from perk b m Q ((baron b)^(n+1)), add_comm]; apply congr_arg (·+_)
    unfold vie; rw [sum_mul,sum_mul]; refine sum_congr rfl (fun i _=>?_); rw [stir,sli]
    conv_lhs=> rw [mul_comm ((baron b)^n), C_mul',map_smul,map_smul]
    simp only [smul_eq_mul]; rw [sum_mul,Finset.mul_sum,Finset.mul_sum]; rw [sum_mul,sum_mul]; apply Finset.sum_congr rfl; intro j _; unfold B; ring
variable (μ)
structure Corolla (u:α→A→ℝ)(m:A→ℝ)(Q: Next.Rank.Normal.Symmetric A):Prop where
    ray (b:A→ℝ) :∃ k:ℝ, k= (vie Q b).re ∧ (k:ℂ)=vie Q b ∧ mgf (fun z=>foo b (u z)) μ = fun t=> Real.exp (t*foo b m+k*t^2/2)
-- derive pol Gaussian law
variable (u:α→A→ℝ)(m:A→ℝ)(Q:Next.Rank.Normal.Symmetric A)
structure Petal (p:poly A):Prop where
   nice : Integrable (fun z=> eve (u z) p) μ
   meet : (∫ z,eve (u z) p ∂μ)=blend Q (fun i=> (m i:ℂ)) p
variable {μ u m Q}
namespace Petal
lemma plus {p q:poly A}(h:Petal μ u m Q p)(g:Petal μ u m Q q): Petal μ u m Q (p+q):=by constructor; simp_rw [map_add]; exact h.nice.add g.nice; simp_rw [map_add]; rw [MeasureTheory.integral_add h.nice g.nice,h.meet,g.meet]
lemma titled {p:poly A} (h:Petal μ u m Q p)(c:ℂ) : Petal μ u m Q (c • p):=by constructor; simp_rw [map_smul]; exact h.nice.smul c; simp_rw [map_smul]; rw [integral_smul,h.meet]
end Petal
variable [IsProbabilityMeasure μ] (hc : Corolla μ u m Q)
def estate (μ:Measure α) [IsProbabilityMeasure μ] (u:α→A→ℝ)(m:A→ℝ)(Q:Next.Rank.Normal.Symmetric A): Submodule ℂ (poly A) where
   carrier := {p|Petal μ u m Q p}
   zero_mem' :=⟨by simp,by simp⟩
   add_mem' := fun h g=> Petal.plus h g
   smul_mem' := fun i _ h=> Petal.titled h i
include hc
lemma rye (n:ℕ): Petal μ u m Q (baron b^n):=by
   obtain ⟨k,_,hz,hX⟩:= hc.ray b; let m' :=foo b m; let f z := foo b (u z); let V:=blend Q (fun i=>(m i:ℂ))
   have hp (n:ℕ)(z:α): eve (u z) (baron b^n)=(f z^n:ℝ):=by rw [map_pow,mast]; exact (Complex.ofReal_pow ..).symm
   have he n:V (baron b^n) = ((∫ z,f z^n ∂μ):ℝ):=by
         induction n using Nat.twoStepInduction with
         | zero=> simp [V]
         | one=> simp only [pow_one]; rw [← mul_one (baron b),show V _=_ from perk b m Q 1, lead _ _ _ hX]; simp [f] -- h instance derivative
         | more i hi he=> rw [show V (baron b^(i+2))=_ from prince b m Q i]; change _*_*V _+_ *V _=_; rw [hi,he,lends f m' k hX]; push_cast; rw [hz]
   constructor
   · simp_rw [hp]; exact Complex.ofRealCLM.integrable_comp (locus f m' k hX n)
   simp_rw [hp]; change _=V _; rw [he n]; exact integral_complex_ofReal ..
lemma sow (p:poly A): Petal μ u m Q p:=by
    -- monomial presentation by occurrences
    let P:= estate μ u m Q
    change p∈P; rw [p.as_sum]; refine Submodule.sum_mem _ (fun i hi=>?_); obtain ⟨l,h,hx,hr⟩:=sprout i (coeff i p) (subset_univ _); rw [hr,C_mul']; apply Submodule.smul_mem; unfold winks; let W (i:Fin l.length):poly A:=X l[i]; have hz: ∏ i:Fin l.length,W i=(l.map (MvPolynomial.X (R:=ℂ))).prod :=by rw [← List.prod_ofFn]; congr 1; simpa [List.map_ofFn,W] using (congr_arg (List.map (MvPolynomial.X (σ:=A) (R:=ℂ))) (List.ofFn_get l))
    rw [← hz]; let n:=l.length; let H:=(univ:Finset (Fin l.length))
    have hh (s:Finset (Fin l.length)):∑ i∈s,W i=baron (∑ i∈s,Pi.single l[i] (1:ℝ)):=by
        induction s using Finset.induction_on with
        | empty=> simp [baron]
        | insert i s hi ih=>
          have hf(g):baron (Pi.single l[i] (1:ℝ)+g)=baron (Pi.single l[i] 1)+baron g:=by unfold baron; simp only [Pi.add_apply,Complex.ofReal_add,add_smul,sum_add_distrib]
          have he:baron (Pi.single l[i] (1:ℝ))=W i:=by unfold baron; simp [Pi.single_apply,W,ite_smul]
          rw [sum_insert hi,sum_insert hi,ih,hf,he]
    have hr : Oce.rise W H n ∈ P:=by apply Submodule.sum_mem; intro i hi; rw [hh,show (-1:poly A)^(H.card-i.card)=C ((-1:ℂ)^(H.card-i.card)) from (by rw [map_pow,map_neg,map_one]), C_mul']; exact P.smul_mem _ (rye _ hc n)
    have hm:H.card=n:=Fintype.card_fin _; rw [Oce.going _ H _ hm.ge,if_pos hm.symm,show (↑n.factorial:poly A)=C (n.factorial:ℂ) from (map_natCast ..).symm,C_mul'] at hr
    let g:ℂ:=n.factorial; have hV: g≠0:= Nat.cast_ne_zero.mpr n.factorial_pos.ne'
    exact (Submodule.smul_mem_iff P hV).1 hr
    -- slot prod order
end YM.QCD.Bera.Oce
#print axioms YM.QCD.Bera.Oce.sow
