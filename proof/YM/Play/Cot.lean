import YM.Play.Panther
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera.Oce
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly ProbabilityTheory ConnectedActivityE6.Poll Cove
open scoped BigOperators Topology ContDiff Classical Matrix InnerProductSpace NNReal ENNReal
variable {α:Type*}[MeasurableSpace α]{A B D E:Type}[Fintype A][Fintype B][Fintype D][Fintype E]{μ:Measure α} [IsProbabilityMeasure μ]
variable {u:α→ A→ℝ}{m:A→ℝ}{Q:Next.Rank.Normal.Symmetric A} (h:Corolla μ u m Q)
-- pay Shift K.F: all moments.eval true.
variable (P:Matrix A B ℂ)(L: Patio D →ₗ[ℂ] Patio E)
variable (φ:Papers A (Patio D))(b:B→ℝ)
set_option quotPrecheck false
local notation "Gf"=> Bera.ferry (Next.Rank.Normal.pipe (spool P) Q) L
local notation "readU" z=> L (rose D (u z) φ)
-- 
include h
lemma offering : Integrable (fun z => L (rose D (u z) φ)) μ :=by
    rw [φ.as_sum]; simp_rw [map_sum]; refine MeasureTheory.integrable_finset_sum _ fun i hi=>?_ ; rw [show monomial i (coeff i φ)= outer (monomial i 1) (coeff i φ) by rw [outmono,one_smul]]; simp_rw [antiquity,map_smul]; exact ((sow h _).nice).smul_const _ -- name.
lemma comingV (hp:∀ i, (m i:ℂ)= ∑ j,P i j*(b j:ℂ)) :
    ∫ z,L (rose D (u z) φ) ∂μ= rose E b (Gf φ):=by
    have he i (x:Finset A): (m i:ℂ)=reads (spool P) (fun j=>(b j:ℂ)) i:=by rw [← reads_at,wool,map_sum]; rw [hp]; exact sum_congr rfl fun j _=> by rw [map_smul,aeval_X,smul_eq_mul] -- x unused
    rw [φ.as_sum]; simp_rw [map_sum]; rw [MeasureTheory.integral_finset_sum]; refine sum_congr rfl fun i hi=>?_
    · rw [show monomial i (coeff i φ)=outer (monomial i 1) (coeff i φ) by rw [outmono,one_smul],covert]; simp_rw [antiquity,map_smul]; rw [integral_smul_const,(sow h _).meet]; apply congr_arg (fun x:ℂ=> x • L (coeff i φ)); rw [blend_components]; unfold eve Next.Rank.Normal.pipe; change _=aeval _ (exchange _ _); rw [reads_val]; apply congr_arg (fun m:A→ℂ=> aeval m (milk Q _)); ext1 j; exact he j ∅
    intro i _; exact offering (u:=u) h L _

variable {p c s v r k:ℝ}{U:Finset A}{W:Finset B}{n d i:ℕ}
omit h in
lemma waltz (i:A→₀ℕ)(x:A→ℝ): ∃ t:ℝ,eve x (monomial i 1)=↑t:=by
    obtain ⟨l,_,hl,hP⟩:=sprout i (1:ℂ) (subset_univ _); rw [hP,map_one,one_mul]
    have hp(l:List A): eve x (winks l)= ((l.map x).prod:ℝ):=by induction l with
    | nil=> unfold winks; simp
    | cons i L ih=> change eve x (MvPolynomial.X i*winks L)=_; rw [map_mul,cylindrical,ih,List.map_cons,List.prod_cons,Complex.ofReal_mul]
    exact ⟨_,hp l⟩
noncomputable def expat (n:ℕ)(p c:ℝ):= p^(n+n)*tumbler (n+n) c
private lemma gain {i:A→₀ℕ}(hm:tags U n i)(hp:Pane Q U c) (hc:0 ≤ c)(hv:bill m U r)(hr:1 ≤ r):
   let f:= monomial i (1:ℂ); let g z:= ‖eve (u z) f‖; Integrable (fun z=>g z^2) μ ∧ (∫ z,g z^2 ∂μ) ≤ expat n r c:=by
    intro f g; have hT z: (↑(g z^2):ℂ)= eve (u z) (f*f):=by
       rw [map_mul]; obtain ⟨k,hx⟩:= waltz i (u z); unfold g f; rw [hx,Complex.norm_real]; simp [sq_abs,pow_two]
    have hh:=sow h (f*f); have hx:Integrable (fun z=>g z^2) μ:=by
        have he z: g z^2=Complex.reCLM (eve (u z) (f*f)):=by rw [←hT]; rfl
        simp_rw [he]; exact Complex.reCLM.integrable_comp hh.nice
    have hQ: 0 ≤ ∫ z,g z^2 ∂μ:= integral_nonneg fun z=>sq_nonneg _
    have he:cents (milk Q (f*f)) ≤ tumbler (n+n) c:=by
       have hc₀:=hc; let H:= calculate Q _ (manufacture (sparks (1:ℂ) hm) (sparks (1:ℂ) hm)) hp hc₀; refine le_trans H (mul_le_of_le_one_right (?_) (le_trans (bag f f) ?_)); unfold tumbler; positivity; unfold f; rw [solely]; simp
    have hh: eve m (milk Q (f*f))=((∫ z,g z^2 ∂μ):ℝ):=by
        rw [show eve m _= _ from hh.meet.symm, ← integral_complex_ofReal]; exact integral_congr_ae (ae_of_all _ fun i=>(hT i).symm) -- coercion.D
    refine ⟨hx,?_⟩
    rw [← Real.norm_of_nonneg hQ, ← Complex.norm_real,← hh]; exact (tender _ (milky Q _ (manufacture (sparks _ hm) (sparks _ hm))) hv hr).trans (mul_le_mul_of_nonneg_left he (pow_nonneg (zero_le_one.trans hr) _))
lemma joins {Z: Finset D} (hφ:φ∈Ledger Z U n d) (he:∀ x:Patio D,x.val∈ Rim Z d→ ‖L x‖ ≤ s*‖x‖) (hp:Pane Q U c)(hc:0≤c) (hv:bill m U r)(hr:1≤r)(hk:0<k)(u':Set α)(h': μ.real u'≤v):
    (∫ i in u',‖L (rose D (u i) φ)‖ ∂μ)≤ (v*k+k⁻¹*expat n r c)*(s*cents φ) :=by
     let Q' z:= rose D (u z); let t x:= monomial x (coeff x φ); let p i z:= L (Q' z (t i)); have hx z:L (Q' z φ)= ∑ i∈ φ.support,p i z:=by
          conv_lhs=> rw [φ.as_sum,map_sum,map_sum]
     have hp' i:Integrable (p i) μ:= offering h L (t i)
     let Y:=v*k+k⁻¹*expat n r c; have hu:0≤Y:=by unfold Y expat tumbler; have hx:0 < r:=zero_lt_one.trans_le hr; have hV:0 ≤v:=(measureReal_nonneg).trans h'; positivity
     change (∫ i in u',‖L (Q' i φ)‖ ∂μ) ≤ _; refine le_trans (b:=∫ z in u',∑ i∈ φ.support,‖p i z‖ ∂μ) (integral_mono ((offering h L φ).norm.restrict) (integrable_finset_sum _ (fun i _=> (hp' i).norm.restrict)) (fun i=> ?_)) (?_); · rw [hx]; exact norm_sum_le ..
     rw [integral_finset_sum _ (fun i _=> (hp' i).norm.restrict)]; change _≤ Y*(s*cents φ); unfold cents; rw [mul_sum,mul_sum]; refine sum_le_sum fun i hi=>?_
     let z:= coeff i φ; let f:= monomial i (1:ℂ); let g q:= ‖eve (u q) f‖; have he' q:p i q= eve (u q) f • L z:=by unfold p t Q'; rw [show monomial _ _=outer f z from (?_),antiquity,map_smul]; unfold f; rw [outmono,one_smul]
     simp_rw [he',norm_smul,MeasureTheory.integral_mul_const]; change _ ≤ Y*(s* ‖z‖); apply mul_le_mul _ (he z (careful hφ i)) (norm_nonneg _) hu
     obtain ⟨hm,hP⟩:= gain h (stampC hφ.2 _ hi) hp hc hv hr
     have hy : (∫ x in u',g x^2 ∂μ) ≤ ∫ x,g x^2 ∂μ:= MeasureTheory.integral_mono_measure (Measure.restrict_le_self) (Eventually.of_forall (fun _=> sq_nonneg _)) hm
     calc
       _ ≤ ∫ z in u', (k + k⁻¹ * g z^2) ∂μ:= integral_mono ((sow h f).nice.norm.restrict) ((integrable_const _).add ((hm.const_mul k⁻¹).restrict)) (fun i=>by change g i≤ _; rw [← div_eq_inv_mul]; apply le_add_of_sub_left_le; apply (le_div_iff₀ hk).mpr; nlinarith [sq_nonneg (g i-k)]) -- lemma choice
       _ = μ.real u'*k+k⁻¹*(∫ i in u',g i^2 ∂μ):=by rw [integral_add (integrable_const _) ((hm.const_mul _).restrict), MeasureTheory.setIntegral_const,integral_const_mul,smul_eq_mul]
       _ ≤ _:=add_le_add (mul_le_mul_of_nonneg_right h' hk.le) (mul_le_mul_of_nonneg_left (hy.trans hP) (inv_nonneg.mpr hk.le))
end YM.QCD.Bera.Oce
#print axioms YM.QCD.Bera.Oce.comingV
#print axioms YM.QCD.Bera.Oce.joins
