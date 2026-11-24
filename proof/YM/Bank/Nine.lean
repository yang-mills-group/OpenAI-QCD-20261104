import YM.Bank.Glyph
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Glyph
open Wilson Gauge Function Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free
open Learn Wale Osc Pilot Matrix Exterior
open scoped Topology Matrix Matrix.Norms.L2Operator ComplexConjugate BigOperators InnerProductSpace
local notation "θ"=>TypeFace 2
local notation "δ"=>TypeFace 1
variable {a b r:ℝ}{p:Momentum}{F:Bed} {c:Side}
def home (p: Momentum) : Matrix δ δ ℂ:= ((lengthSq p:ℝ):ℂ) • 1
lemma null_lap (p:Momentum): (τ p 1)ᴴ*τ p 1+ τ p 0*(τ p 0)ᴴ = home p:= by
   unfold τ home; rw [bladeΔ]; congr 2;
   rw [Work.F06.sqLength_apply]; simp_rw [norm_mul,Complex.norm_I,one_mul]; rfl
lemma hold_pos {p:Momentum}(h:p≠0): IsUnit (home p).det ∧ ‖(home p)⁻¹‖≤ (‖p‖^2)⁻¹:=by
    have hp := lengthSq_pos h; have hu: QCD.Cost.Floor (‖p‖^2) (home p):=QCD.Cost.Floor.for_scalar.lower (QCD.Pearl.vector_max p)
    have he:=pow_pos (norm_pos_iff.mpr h) 2; exact ⟨hu.unit he,hu.reciprocal he⟩
def oldG (p: Momentum):= τ p 1* (home p)⁻¹*(τ p 1)ᴴ
lemma kiln (a b r:ℝ)(ha:0<a)(hb:0≤b)(hr:0<r): ∃ s E,0<s ∧ s≤1 ∧ 0≤ E ∧∀ {c:Side}(H:Bed) (i:Site c),H.metric.strip r b→Numeric (H.metric.acts c) a b→ H.metric.read 0=1→ mon i≠0 → ‖mon i‖≤s → Twin (skyF H (mon i)) (oldG (mon i)) E 1 ‖mon i‖:=by
   obtain ⟨C,c₀,Y⟩:= sails 0; obtain ⟨D,d₀,V⟩:= sails 1
   obtain ⟨T,s,hT,hs,h₁,H₁⟩:= blouse r b hr hb
   let d:= 2*(2*D*T)*D+ 2*C*C; let W:=(lum a)⁻¹; let U:=max (max W 1) (W*d); have hm:0<W:=inv_pos.mpr (luminous ha); have he: 0≤ U:=(hm.trans_le ((le_max_left ..).trans (le_max_left ..))).le
   refine ⟨s,2*(2*D*U)*D,hs,h₁,by positivity,fun {c} H i h h₂ hp h₃ h₄=>?_⟩
   let p:=mon i; let v:=‖p‖; let A:=gaugeR H.metric p; let X:= home p; let K:= spaceK H.metric p; let t:=v^2; let M:= X⁻¹
   have hx := V p (h₄.trans h₁); have hy:= Y p (h₄.trans h₁)
   have hv: 0 < t:=pow_pos (norm_pos_iff.mpr h₃) 2
   have hw:= purse _ h₂ ha i (Row.rights _ _ h hr.le) h₃; have hpot: X * M=1:= X.mul_nonsing_inv (hold_pos h₃).1; have hi:A*K=1:= A.mul_nonsing_inv hw.1
   have hQ:Twin A X d t v:=by
     have hz:= (((hx.ref.prod (H₁ _ h hp p h₄)).prod hx).add (?_ : Twin (signal 1 0 p*(signal 1 0 p)ᴴ) (τ p 0*(τ p 0)ᴴ) (2*C*C) _ _)) -- edit
     · change Twin (gaugeR H.metric (mon i)) _ _ _ _; rw [gauge_gram (mon_mem ..),live_gram (mon_mem ..)]
       unfold X t v; rw [← null_lap p,pow_two]
       simpa only [Matrix.mul_one,mul_one] using hz
     simpa only [mul_one] using hy.prod hy.ref
   have hK :‖K‖≤W*t⁻¹:=hw.2.trans_eq (mul_inv _ _)
   have hg :‖M‖≤ t⁻¹:= (hold_pos h₃).2; have hu : Twin K M U t⁻¹ v:=by
     have he: K-M= K*(X-A)*M :=by rw [mul_sub,sub_mul,mul_assoc K X M,hpot,mul_one,show K*A=1 from mul_eq_one_comm.mp hi,one_mul]
     refine ⟨hK.trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_left ..)) (inv_nonneg.mpr hv.le)),hg.trans (le_mul_of_one_le_left (by positivity) ((le_max_right W 1).trans (le_max_left ..))),?_⟩
     rw [he]; have hé:= mul_le_mul hK ((norm_sub_rev ..).trans_le hQ.fares) (norm_nonneg (X-A)) (mul_nonneg hm.le (by positivity))
     exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le K (X-A)).trans hé) hg (norm_nonneg _) ((by positivity : 0≤ ‖K‖*‖X-A‖).trans hé)).trans ((le_of_eq (show W*t⁻¹*(d*t*v)*t⁻¹=W*d*t⁻¹*v from by field_simp)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) (norm_nonneg _))))
   have hZ:= (hx.prod hu).prod hx.ref
   rw [show ‖p‖*t⁻¹*‖p‖=1 from (by have hg:0<v:=norm_pos_iff.mpr h₃; change v*t⁻¹*v=_; unfold t; field_simp)] at hZ
   unfold skyF; rw [mirage_herm _ _ (mon_mem ..).1]; exact hZ
lemma path_s (p: Momentum)(x:Cover): skyF F (p+reciprocal x)=skyF F p:=by unfold skyF starΔ spaceK gaugeR live mirage signal; simp only [signal, tripQ_stays, show -(p+reciprocal x:Momentum)=-p+reciprocal (-x) by rw [reciprocal_negate]; abel, Row.periods]
lemma gaugeW (a b r:ℝ)(ha:0<a)(hb:0≤b)(hr:0<r):∃ s C:ℝ,0<s ∧0≤ C ∧ ∀ {c:Side}(P:Bed),P.metric.strip r b→Numeric (P.metric.acts c) a b→ P.metric.read 0=1 →∀ i j,
    Genie 1 false c (fun p=>skyF P p i j) (fun p=> oldG p i j) s C:=by
   obtain ⟨s,E,he,hi,hE,H⟩:=carpet a b r ha hb hr; obtain ⟨x,K,hx,hx',hK,h⟩:=kiln a b r ha hb hr
   let t:=min s x; let C :=max E K; have ht:0<t:=lt_min he hx
   refine ⟨t,C,ht, hE.trans (le_max_left ..),fun {c} P hp h0 hR i j=>?_⟩
   have ha (p:Site c)(q:Momentum)(hf:q∈collar (grid false p) t):q∈collar (mon p) s:= ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_left ..) (norm_nonneg _)) hf
   refine ⟨ht,(min_le_left ..).trans hi,hE.trans (le_max_left ..),Or.inl ?_, ?_,fun p q hq hf=>?_,fun p q hq hf=>(H P hp h0 p hq q (ha p q hf)).1, fun x p hp _ _=> by rw [path_s],fun p hq hy=>?_⟩
   · simp [skyF,starΔ,outside]
   · simp [oldG,τ,wedge]
   · obtain ⟨_,hD,hh⟩:= H P hp h0 p hq q (ha p q hf)
     exact ⟨(listenD i j).differentiableAt.comp _ hD,(QCD.Cost.north ..).trans (hh.trans (div_le_div_of_nonneg_right (le_max_left ..) (norm_nonneg _)))⟩
   have hv := (h P p hp h0 hR hq (hy.trans (min_le_right ..))).peek i j; rw [pow_one,div_self (norm_pos_iff.mpr hq).ne']; exact hv.higher (le_max_right ..) zero_le_one (norm_nonneg _)
end YM.Bank.Glyph
#print axioms YM.Bank.Glyph.gaugeW
