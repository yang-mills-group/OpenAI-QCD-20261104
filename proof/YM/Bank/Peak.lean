import YM.Bank.Jule
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Peak
open Function Wilson Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free
open Kith Jule Pap Pilot Jump Cent Bee Osc Horse Murmur MeasureTheory
open QCD.Pearl (beamP beamH beam0)
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexConjugate ContDiff InnerProductSpace
variable {n k:ℕ}{a C e b r t w:ℝ}{L:recordL}{f g: Momentum→ℂ}{c:Side}
lemma swipe {v:Cover}(ht:0<t)(he:0<e)(hv:t⁻¹ • rock v∈ Oasis e b): ∃ i:Axis,(e/2)*t ≤|(v i:ℝ)|:=by
    let y:= t⁻¹ • rock v
    let q:= fly y
    have hq:‖y‖≤ 2*‖q‖:=(le_of_eq (show ‖y‖=‖earth q‖ from (congr_arg (‖·‖) (size_p y)).symm)).trans (Pilot.pace (scope_p ..))
    obtain ⟨i,h⟩: ∃ i:Axis, ‖q‖=‖q i‖:= by
      rw [← coe_nnnorm]; change ∃ i, ↑(univ.sup fun i=>‖q i‖₊)=(‖q i‖:ℝ); obtain ⟨i,_,ha⟩:= exists_mem_eq_sup univ univ_nonempty fun i=>‖q i‖₊; exact ⟨i,by rw [ha]; rfl⟩
    refine ⟨i,?_⟩
    have hf : e/2 ≤ ‖q i‖:=by
        have hp: e≤ ‖y‖:= (consp hv).1; linarith
    have hh:q i=((t⁻¹ * (v i:ℝ):ℝ):ℂ):=rfl
    rw [hh,Complex.norm_real,norm_mul,Real.norm_of_nonneg (inv_pos.mpr ht).le,Real.norm_eq_abs (v i:ℝ),inv_mul_eq_div] at hf
    exact (le_div_iff₀ ht).mp hf
-- continuum alias assertion. normer normalization.E. logarithm buys.
def priceL (L:recordL) := ∑ i∈L.support, ‖L i‖
def vote (σ:Bool)(c:Side)(x:Cover)(f: Momentum→ℂ) :ℂ := (c.val:ℝ)⁻¹^4 • summit c x σ (f ∘ grid σ)
lemma marks (c:Side) : normer *beamH c^4=(c.val:ℝ)⁻¹^4:=by rw [normer,← mul_pow]; unfold beamH; have he:=Real.pi_pos; field_simp
lemma tall (hk:k+7≤n)(ha:0<a)(hg:∀ x,physical x→ g x=crewG L x)(hL: steady L k) (C b:ℝ)(he:0<e) (σ:Bool):∃ A:ℝ,0≤A∧∀ᶠ w:ℝ in atTop,∀ x:Cover,((w^n)⁻¹ • rock x) ∈ Oasis e b → ∀ᶠ c: Side in atTop,∀ f:Momentum→ℂ, Genie k σ c f g a C→
    w * ‖(w^n)^(k+3) • vote σ c x f-metricL L ((w^n)⁻¹ • rock x)‖≤A :=by
     let D:= normer; have hd: 0<D:= by unfold D normer; positivity
     let s:=min a a₀; have hs:0<s:=lt_min ha ans
     let P:=priceL L; have hp :0≤P:=sum_nonneg fun i _=> norm_nonneg _
     refine ⟨D+D+D+P,by positivity,?_⟩
     have h:Tendsto (fun w:ℝ => w^n) atTop atTop:=tendsto_pow_atTop (by omega)
     filter_upwards [eventually_gt_atTop (1:ℝ), Jump.Work.readout (e/2) s (half_pos he) hs k n hk g L hg hL C (min_le_right ..), h.eventually (fade L (k+3+1)), h.eventually (costly L 1 b he)] with w hw hT hF hu x hx
     let r:= w^n; have hw':0<w:=zero_lt_one.trans hw; have hr : 0<r:=pow_pos hw' _
     let p:=r^(k+3); let y:= (r⁻¹) • rock x; have hy: y ≠0:=door hx he
     let F:=∫ i,vault L r (rock x) i; let S:=∫ i in coast,vault L r (rock x) i -- ambiguity
     have hx':‖metricρ L r⁻¹ y -metricL L y‖ * r ≤ P:=by rw [mul_comm]; simpa only[r,P,priceL,pow_one] using hu y hx -- pow inside problem
     have hz: r*(p*‖F-S‖)≤ 1:=by rw [← mul_assoc,mul_comm r,← show r^(k+3+1)=p*r from pow_succ ..]; exact hF (rock x)
     have hr': w ≤ r:=by nth_rw 1 [← pow_one w]; exact pow_le_pow_right₀ hw.le (by omega)
     have hS: p • (D • F)=metricρ L r⁻¹ y:=by
        have hv:= scaled hL hr hy; unfold F; rw [show rock x=r • y by unfold y; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]]; -- RHS y unaffected?
        exact hv
     obtain ⟨i,hK⟩:= swipe hr he hx
     have hM : 0<(r*p)⁻¹:=inv_pos.mpr (mul_pos hr (by unfold p; positivity))
     filter_upwards [hT x i hK, Metric.tendsto_nhds.mp (vault_r L r x hr hL σ) _ hM] with c hc ht; intro f H
     let Z:=vote σ c x f; let g' := stunted r L; let Y:=vote σ c x g'; let F':=D • F; let S':= D • S
     have ht1 : w* (beamH c^4*p*‖summit c x σ ((gapF f L r)∘grid σ)‖) ≤1:= by have he:=hc f σ (H.mono hs (min_le_left ..) le_rfl); apply he.trans' (le_of_eq ?_); unfold p r; ring
     have hJ : ‖Y-S'‖≤ D*(r*p)⁻¹:=by
        unfold Y vote; rw [← marks]; unfold S'; change ‖(D*_ ) • _-D • S‖≤_; rw [← smul_smul,← smul_sub, norm_smul,Real.norm_of_nonneg hd.le]; exact mul_le_mul_of_nonneg_left (show ‖beamH c^4 • summit c x σ (g' ∘ grid σ) - S‖≤(r*p)⁻¹ from (dist_eq_norm (beamH c^4 • summit c x σ (g' ∘ grid σ)) S) ▸ ht.le) hd.le
     have hz': Z-Y=D • (beamH c^4 • summit c x σ (gapF f L r ∘ grid σ)):=by
        unfold Z Y vote D; rw [smul_smul,marks,←smul_sub]; congr 1; unfold Horse.summit; rw [← sum_sub_distrib]; simp only [gapF,comp_apply,Pi.sub_apply]; apply sum_congr rfl; intro i _; rw [mul_sub]
     have hV(A B:ℂ) : w*‖p • A-p • B‖ = w*(p * ‖A-B‖) :=by rw [←smul_sub,norm_smul,Real.norm_of_nonneg (pow_pos hr _).le]
     have h1: w*‖p • Z-p • Y‖≤D:=by rw [hV,hz',norm_smul,norm_smul,Real.norm_of_nonneg hd.le,Real.norm_of_nonneg (pow_pos (beamP _) _).le]; exact ((mul_le_of_le_one_right hd.le ht1).trans' (le_of_eq (by ring)))
     have h2: w*‖p • Y-p • S'‖≤ D:=by rw [hV]; have hv:0<p:=pow_pos hr _; apply (mul_le_mul hr' (mul_le_mul_of_nonneg_left hJ hv.le) (by positivity) hr.le).trans_eq; field_simp
     have h3: w*‖p • S'-p • F'‖≤ D:=by rw [hV,norm_sub_rev]; unfold F' S'; rw [←smul_sub,norm_smul,Real.norm_of_nonneg hd.le]; have hh : w*(p*‖F-S‖) ≤ 1:= (mul_le_mul_of_nonneg_right hr' (by unfold p; positivity : 0≤p*‖F-S‖)).trans hz; exact (mul_le_of_le_one_right hd.le hh).trans' (le_of_eq (by ring))
     have h4: w*‖p • F'-metricL L y‖ ≤ P:=by unfold F'; rw [hS]; exact (mul_le_mul_of_nonneg_right hr' (norm_nonneg _)).trans ((mul_comm ..).trans_le hx')
     let M:=metricL L y; have he (x y z:ℂ):w*‖x-y‖ ≤ w*‖x-z‖+w*‖z-y‖:=by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub ..) hw'.le
     change w*‖p • Z-M‖ ≤ _; calc
       _ ≤ w*‖p • Z-p • F'‖+_:= he _ _ (p • F')
       _ ≤ _ := add_le_add ((he _ _ (p • S')).trans (add_le_add ((he _ _ (p • Y)).trans (add_le_add h1 h2)) h3)) h4
end YM.Bank.Peak
#print axioms YM.Bank.Peak.tall
