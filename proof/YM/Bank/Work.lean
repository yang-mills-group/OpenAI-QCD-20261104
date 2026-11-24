import YM.Bank.Jump
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Jump.Work
open Filter MeasureTheory Function Lattice Laurent Bloch Metric Finset RG Zoom Pilot Pap Cent Bee Osc Horse
open Next.Free
open QCD.Pearl (beamH beam0 beamP)
open scoped Topology BigOperators ComplexConjugate Matrix.Norms.L2Operator
variable {σ:Bool}{c:Side}{R b v w K:ℝ}{k n j:ℕ}{g f:Momentum→ℂ}{L:recordL}
lemma rolling (hv:0<v)(hb:0<b)(n k:ℕ)(hk:2≤n):∀ᶠ w:ℝ in atTop, Gates j k (4/(v*w^n)) (w/w^n) b:=by
    have he : ∃ d,n=1+d∧0<d:=⟨n-1,by omega,by omega⟩
    obtain ⟨d,rfl,hd⟩:=he
    let h(w:ℝ):=w/w^(1+d); have hx:Tendsto h atTop (𝓝 0):=by
       refine (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α:=ℝ) hd.ne')).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw; dsimp[h]; rw [pow_add,pow_one]; field_simp
    filter_upwards [eventually_gt_atTop (0:ℝ), hx.eventually (gt_mem_nhds (half_pos hb)),eventually_gt_atTop (4*j/(b*v)),eventually_gt_atTop (4*8^j/(b*v))] with w he hi hQ hK
    change _<_ at hQ hK
    have hp : w/w^(1+d)< b/2:=hi
    refine ⟨by linarith,by positivity, ?_,?_⟩
    · rw [div_lt_iff₀ (by positivity)] at hQ; field_simp; linarith
    rw [div_lt_iff₀ (by positivity)] at hK; field_simp; linarith
def costs (d k:ℕ):= (k+4)*d+2
lemma journey (hv:0<v)(hb:0<b)(C:ℝ)(k:ℕ)(hk:k+7≤n): Tendsto
    (fun w:ℝ=> w*(w^n)^(k+3)*quotaE (costs n k) k C (w^n) b (w/w^n) (4/(v*w^n)) L) atTop (𝓝 0):=by
    let η:=fun w:ℝ=> w/w^n; let τ:=fun w:ℝ=> w^n; let f:=fun w:ℝ=>4/(v*τ w)
    let p(w:ℝ):= w*(τ w)^(k+3)
    let i:=costs n k
    let D:=betaL L k; let s:= Real.pi/4; have hs:0<s:=by unfold s; positivity
    let X(a:ℝ)(w:ℝ):= p w*headH i (a/η w) (f w) (b*η w)
    have HX (a:ℝ) : Tendsto (X a) atTop (𝓝 0) :=by
       let K:ℝ:=a*(4*8^i/(v*b))^i
       refine (show Tendsto (fun w:ℝ=> K/w^2) atTop (𝓝 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))).congr' ?_
       filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw
       dsimp only [X,headH,p]; rw [show f w / (b*η w /8^i)=(4*8^i/(v*b))/w by unfold f η τ; field_simp, div_pow]; unfold τ η K; field_simp
       -- ^ rearrange
       unfold i costs; simp only [pow_add,pow_mul]; ring
    let S(w:ℝ):= p w*Real.exp (-(τ w)*s^2)
    have hs': Tendsto S atTop (𝓝 0):=by
       have he:Tendsto (fun w:ℝ=> w^(n*(k+4))*Real.exp (-(s^2)*w)) atTop (𝓝 0) := by
          have hx:= tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((n*(k+4):ℕ):ℝ)) _ (pow_pos hs 2); simpa only [Real.rpow_natCast,neg_mul] using hx
       refine squeeze_zero' ?_ ?_ he
       · filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw; unfold S p τ; positivity
       filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
       have hm : 0<w:=one_pos.trans_le hw; have hS: w ≤ w^n:=by nth_rw 1 [← pow_one w]; exact pow_le_pow_right₀ hw (by omega)
       unfold S p τ; rw [pow_mul]; apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
       · apply (mul_le_mul_of_nonneg_right hS (by positivity : 0≤(w^n)^(k+3))).trans_eq; ring
       apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg s]
    let m1(w:ℝ):= p w*η w^k*(η w)^4; let m2(w:ℝ):=p w*τ w*η w^(k+1)*(η w)^4
    have hx (a:ℕ)(h:a<n): Tendsto (fun w:ℝ=> w^a / (w^n)) atTop (𝓝 0):=by
        refine (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α:=ℝ) (show n-a≠0 by omega))).congr' ?_
        filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw; dsimp only [comp_apply]; nth_rw 2 [show n= a+(n-a) by omega]; rw [pow_add]; field_simp
    have h1: Tendsto m1 atTop (𝓝 0):=by
        refine (hx (k+5) (by omega)).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw; unfold m1 p η τ; simp_rw [pow_add,div_pow]; field_simp
    have h2: Tendsto m2 atTop (𝓝 0):=by
        refine (hx (k+6) (by omega)).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw; unfold m2 p η τ; simp_rw [pow_add,div_pow]; field_simp
    let T:=(2*Real.pi)^4; let A:=Real.pi^k; let B:=3^4*(Real.pi^2/2)*2^i
    let W:=(2:ℝ)^i * (D*A/s)
    let Y (w:ℝ):=(X C w + X (D*A) w+S w*W)*T + (m1 w*(C*(2:ℝ)^k)+m2 w*(16*D*2^(k+1)))*B
    have hh : Tendsto Y atTop (𝓝 0) :=by
       simpa only [Y,add_zero,zero_mul] using (((HX C|>.add (HX (D*A))).add (hs'.mul_const W)).mul_const T|>.add ((h1.mul_const (C*(2:ℝ)^k)|>.add (h2.mul_const (16*D*2^(k+1)))).mul_const B))
    apply hh.congr'; filter_upwards [] with w; unfold Y T W B X m1 m2 S
    change _=p w*quotaE i k C (τ w) b (η w) (f w) L; unfold quotaE fineE darkE s D A; ring
lemma readout (v b:ℝ)(hv:0<v)(hb:0<b)(k n:ℕ)(h:k+7≤n)(g:Momentum→ℂ)(L:recordL)(he:∀ x,physical x→g x=crewG L x)(hs:steady L k) (C:ℝ)(hC:b≤a₀) : ∀ᶠ w:ℝ in atTop, ∀ (x:Cover)(i:Axis), v*w^n ≤|(x i:ℝ)|→∀ᶠ c:Side in atTop, ∀ (f:Momentum→ℂ) (σ:Bool),Genie k σ c f g b C→
     w*(w^n)^(k+3)*beamH c^4*‖summit c x σ (gapF f L (w^n) ∘ grid σ)‖ ≤ 1:=by
    let j:=costs n k; filter_upwards [eventually_gt_atTop (0:ℝ),rolling (j:=j) hv hb n k (by omega),(journey (L:=L) hv hb C k h).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with w hw hh hX; intro x i hT
    have hp:0<v*w^n:=by positivity
    have hz:x i≠0:=by intro e; rw [e,Int.cast_zero,abs_zero] at hT; linarith
    filter_upwards [enough x i hz _ hp hT,beam0.eventually (gt_mem_nhds hh.h0)] with c hc ht; intro f σ h; obtain ⟨s,hg,hy⟩:=hc
    have h' := total h he hs (pow_nonneg hw.le n) x s hC hh hg hy (le_of_lt ht)
    rw [mul_assoc _ (beamH c^4)]; exact (mul_le_mul_of_nonneg_left h' (by positivity)).trans (le_of_lt hX)
end YM.Bank.Jump.Work
#print axioms YM.Bank.Jump.Work.readout
