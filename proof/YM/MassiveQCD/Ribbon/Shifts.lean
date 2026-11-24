import YM.MassiveQCD.Ribbon.Burst
/-! # Incidence and graded locality
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Lat QCD.Cove QCD.Creek Function Filter Finset MeasureTheory NormedSpace
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B C D I:Type}[Fintype A][Fintype B][Fintype C][Fintype I]
def clad (s:Finset A)(x:Alg (A⊕B)): Prop:=∀ t,scrape A t x ∈region s
variable {p q r:Finset I}{U:Finset A}{x y:Alg (A⊕B)}
lemma grade_region (x:Alg A)(h:x∈region U): grade x∈region U:=by obtain ⟨u,rfl⟩:=h; exact ⟨grade u,(embed_grade (fun x:↥U=> (x:A)) u).symm⟩
lemma clad.one (s:Finset A) : clad (B:=B) s 1:= by intro i; rw [show (1:Alg _)= stake A (∅:Finset B) 1 from ((quiet ..).trans (map_one _)).symm,stakesX]; split; exact (region s).one_mem; exact (region s).zero_mem
lemma clad.nil (s:Finset A) : clad (B:=B) s 0:=fun i=>by rw [map_zero]; exact (region s).zero_mem
lemma clad.plus (h:clad U x)(he:clad U y): clad U (x+y):=fun i=>by rw [map_add]; exact (region U).add_mem (h _) (he _)
lemma clad.neg (h:clad U x): clad U (-x):= fun i=>by rw [map_neg]; exact (region U).neg_mem (h _)
lemma clad.gates (x:Alg A)(hp:x∈region U)(t:Finset B): clad U (stake A t x):= fun i=>by rw [stakesX]; split; exact hp; exact (region U).zero_mem
lemma clad.scale (h:clad U x)(p:ℂ): clad U (p • x):=fun i=>by rw [map_smul]; exact (region U).smul_mem (h _) _
lemma clad.sumR (p:Finset D) (f:D→Alg (A⊕B))(h:∀ i∈p,clad U (f i)):clad U (∑ i∈p,f i):= fun i=>by rw [map_sum]; exact (region U).sum_mem (fun i hi=> h i hi _)
lemma clad.attend (x:Alg A) (y:Alg B)(h:x∈region U):clad U (fiber B x*quill A y):=by
   rw [← write y,map_sum,Finset.mul_sum]; refine clad.sumR _ _ (fun i hi=>?_); rw [map_smul,mul_smul_comm]; exact (clad.gates _ h i).scale _
lemma clad.raise {Q:Finset A} (h:clad U x)(he:U⊆Q):clad Q x:= fun i=> regionMon he (h i)
lemma clad.mul (h:clad U x)(he:clad U y): clad U (x*y):=by
   rw [← rewriteR A x,← rewriteR A y]; simp_rw [Finset.mul_sum,sum_mul]; apply clad.sumR; intro i _; apply clad.sumR; intro j _; rw [wheel]; apply clad.attend; apply Subalgebra.mul_mem _ (h _); split; exact grade_region _ (he _); exact he _
lemma clad.expR {x:Patio (A⊕B)}(h:clad U x.val):clad U (light _ (exp x-1)):=by
    rw [map_sub,sub_eq_add_neg,map_one,light_exp]; apply clad.plus _ ((clad.one U).neg); let y:= light _ x; have hp n:clad U (y^n):=Nat.rec (by rw [pow_zero]; exact clad.one _) (fun n ih=>by rw [pow_succ]; exact clad.mul ih h) n
    intro i; exact Stays.tab U ((scrape A i).hasSum (exp_series_hasSum_exp' (𝕂:=ℂ) y)) fun k=> (hp k).scale _ _
lemma attire {x:Patio (A⊕Spine I)}{q:I→Bool}{s:Finset I}(h:Polite q s x):Polite q s (exp x-1):=by
    suffices ht: ∀ n:ℕ, Polite q s (x^(n+1)) by
       have hg :HasSum (fun i:ℕ=> (i.factorial:ℂ)⁻¹ • x^i) (exp x):= exp_series_hasSum_exp' x
       rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show ((0:ℕ).factorial:ℂ)⁻¹ • x^0=1 from by simp] at hg
       rw [← hg.tsum_eq]; exact polite_tsum fun i=>(ht i).smooch _
    intro i; induction i with
    | zero=>simpa only [Nat.zero_add,pow_one] using h
    | succ i ih=> simpa only [Finset.union_self,← pow_succ] using ih.attached h
lemma reCarry (p:Alg A→L[ℂ] Alg C) (s:Finset A)(u:Finset C)(h:∀ x∈region s,p x∈region u)(x:Alg (A⊕B))(he:clad s x):clad u (carry B p x):=fun t=>by rw [wing]; exact h _ (he t)
lemma politeStep (p:Alg A→L[ℂ] Alg C){q:I→Bool}{s:Finset I}{x: Patio (A⊕Spine I)}{y:Patio (C⊕Spine I)}(h:Polite q s x)(hy:y.val=carry (Spine I) p x.val): Polite q s y:= Polite.of_ranges fun t ht=>by rw [hy,wing,h.spectral t ht,map_zero]
variable {s t:Finset A}
private lemma charge (p:EndA A)(h:Stays p s)(x):p (grade x)=grade (p x):=DFunLike.congr_fun h.evenG.eq x
private lemma righty (p:EndA A)(h:Stays p s){y:Alg A} (hx:y∈region t) (he:Disjoint t s) (x:Alg A): p (x*y)= p x*y := DFunLike.congr_fun (h.parts he y hx).eq x
private lemma lefty (p:EndA A)(h:Stays p s) (he:Disjoint t s) (x y:Alg A)(hx:x∈region t)(b: Bool)(hX:Hom b x): p (x*y)=x*p y:=by
    cases b
    · rw [(Plus.central hX y).symm.eq,righty p h hx he,(Plus.central hX (p y)).eq]
    rw [show x*y=grade y*x from (Minus.slides hX (grade y)|>.trans (congr_arg _ (grade_twice y))).symm,righty p h hx he,charge p h]; exact (Minus.slides hX _).trans (congr_arg _ (grade_twice _)) -- check
lemma widespread (F G:EndA A)(h:Stays F s) (hv:Stays G t)(hp:Disjoint s t)(hx:clad s x)(hy:clad t y) : carry B (F*G) (x*y)=carry B F x* carry B G y:=by
    have hu (a b:Alg A)(ha:a∈region s)(hk:b∈region t):F (G (a*b))= F a * G b:=by
       rw [show G (a*b)=a*G b from ?_,righty F h (hv.keeps (Subset.refl _) _ hk) hp.symm]
       nth_rw 1 2 [← both a]; rw [add_mul,map_add,add_mul]; exact congr_arg₂ _ (lefty G hv hp (plus a) _ ((region s).smul_mem ((region s).add_mem ha (grade_region _ ha)) _) false (plus_grade a)) (lefty G hv hp _ _ ((region s).smul_mem ((region s).sub_mem ha (grade_region _ ha)) _) true (minus_grade a))
    have hz (p:EndA A)(x:Alg A)(y:Alg B): carry B p (fiber B x*quill A y)=fiber B (p x)*quill A y:=by rw [carries_r,← quiet,speaks,quiet]
    rw [← rewriteR A x,← rewriteR A y]; simp only [map_sum,Finset.mul_sum, sum_mul, map_sum]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [wheel,speaks,speaks,wheel,hz]; simp only [mul_apply_eq_comp]; split
    · rw [hu _ _ (hx _) (grade_region _ (hy _)), charge G hv]
    rw [hu _ _ (hx _) (hy _)]
end YM.MassiveQCD.Ribbon
