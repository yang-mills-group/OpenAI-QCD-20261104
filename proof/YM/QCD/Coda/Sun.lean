import YM.QCD.Fount.Cut
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings
variable {n:Side}{N j:ℕ}
local notation "A"=>EvenA n N
private lemma shade_pow (v:ℂ)(a:A)(i:ℕ): (v • a)^i=v^i • a^i:= smul_pow ..
abbrev line (i:ℕ)(x:A):= ((↑(i+1):ℂ))⁻¹ • x^(i+1) -- log1-x
abbrev noon (x:A):=∑' i,line i x
def bark (x:A):= -noon (-x)
lemma solK {x:A} (h: ‖x‖<1) : exp (-(noon x))=1-x:=by
   obtain ⟨u,h,hp⟩ : ∃ u:ℝ,1<u∧u*‖x‖<1:=by
      have hr:ContinuousAt (fun a:ℝ=> a*‖x‖) 1:=by fun_prop
      have hf := (hr.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (1:ℝ)))).eventually (gt_mem_nhds (show (1:ℝ)*‖x‖<1 from by simpa))
      exact ((show ∀ᶠ y in 𝓝[>] (1:ℝ),1<y from self_mem_nhdsWithin).and hf).exists
   let S:= ball (0:ℂ) u; have hS : IsOpen S:=isOpen_ball; have hc : IsPreconnected S := (convex_ball (0:ℂ) u).isPreconnected
   have hz: (0:ℂ)∈S:= mem_ball_self (lt_trans zero_lt_one h); let H i (v:ℂ):= line i (v • x);
   let g i (v:ℂ):=(v • x)^i*x; have he: ∀ i (v:ℂ), HasDerivAt (H i) (g i v) v:=by
      intro i v; have hh:= (hasDerivAt_pow (i+1) v).smul_const (line i x)
      have hX: (fun z:ℂ=>z^(i+1) • line i x)= H i:= funext fun z=>by unfold H line; rw [shade_pow,smul_comm]
      rw [hX] at hh; convert! hh using 1; unfold g line; rw [shade_pow, Algebra.smul_mul_assoc, ← pow_succ,smul_smul]; congr 1; simp only [Nat.add_sub_cancel]; field_simp -- casts
   have hH v (hv:v∈S): ‖v • x‖ ≤ u*‖x‖:=by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hv).le (norm_nonneg _)
   let s i:=(u*‖x‖)^i*‖x‖; have hs: Summable s:= (summable_geometric_of_lt_one (mul_nonneg (by linarith) (norm_nonneg _)) hp).mul_right ‖x‖
   have hb i v (hv:v∈S): ‖g i v‖≤ s i:= (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) (hH v hv) _)) (norm_nonneg _))
   let V (v:ℂ):= noon (v • x); let Z (v:ℂ):= 1-v • x; let D (v:ℂ):=exp (V v)*Z v
   have h₁ : V 0=0:=by simp [V,noon,line]
   have hV v (hv:v∈S): HasDerivAt V (Ring.inverse (Z v)*x) v:=by
      have hx := hasDerivAt_tsum_of_isPreconnected hs hS hc (fun i v _=>he i v) hb hz (by simp [H,line]) hv
      have h':= (hasSum_geom_series_inverse _ ((hH v hv).trans_lt hp)).mul_right x; rw [show (∑' i,g i v)=_ from h'.tsum_eq] at hx; exact hx
   have hD v (hv:v∈S): HasDerivAt D 0 v:=by
      have hZ : HasDerivAt Z (-x) v:=by simpa only [zero_sub,one_smul] using! (hasDerivAt_const v (1:A)).sub ((hasDerivAt_id' v).smul_const x)
      have hQ:= ((hasFDerivAt_exp (𝔸:=A) (𝕂:=ℂ)).comp_hasDerivAt v (hV v hv)).mul hZ; have hU : Ring.inverse (Z v)*Z v=1:=Ring.inverse_mul_cancel _ (isUnit_one_sub_of_norm_lt_one ((hH v hv).trans_lt hp))
      change HasDerivAt D (exp (V v)*(Ring.inverse (Z v)*x)*Z v+exp (V v)*(-x)) v at hQ
      rw [mul_assoc,mul_right_comm (Ring.inverse (Z v)),hU,one_mul,mul_neg,add_neg_cancel] at hQ; exact hQ
   have hX:= hS.is_const_of_deriv_eq_zero hc (fun x hx=> (hD x hx).differentiableAt.differentiableWithinAt) (fun x hx=> (hD x hx).deriv) (show (1:ℂ)∈S from by simpa [S]) hz
   unfold D at hX; rw [h₁,exp_zero,one_mul,show Z 0=1 by simp [Z],show Z 1=1-x by simp [Z],show V 1=noon x by unfold V; rw [one_smul]] at hX
   rw [← mul_one (exp (-noon x)),← hX,← mul_assoc, ← NormedSpace.exp_add, neg_add_cancel,exp_zero,one_mul,hX]
lemma beech {x:A}(h: ‖x‖<1): exp (bark x)=1+x:=by rw [bark,solK (by rwa [norm_neg]),sub_neg_eq_add]
lemma daw (i:ℕ)(x:A): ‖line i x‖ ≤ ‖x‖^(i+1):=by unfold line; rw [norm_smul]; refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_pow_le ..); rw [norm_inv,show ‖(↑(i+1):ℂ)‖= (i+1:ℝ) by norm_cast]; exact inv_le_one_of_one_le₀ (by simp)
lemma mist {x:A}(hx: ‖x‖<1) : AnalyticAt ℂ noon x:=by
   obtain ⟨r,hr,he⟩:= exists_between hx; let δ:= r-‖x‖; have hp:=sub_pos.mpr hr
   have hu : Summable fun i:ℕ=> r^(i+1):=(summable_nat_add_iff 1).2 (summable_geometric_of_lt_one ((norm_nonneg _).trans hr.le) he)
   refine Work.F02.analytic_series line hp (fun i=> ?_) hu (fun i y hy=>?_); -- arg order
   · intro p; unfold line; fun_prop
   apply (daw ..).trans; apply pow_le_pow_left₀ (norm_nonneg _) _ _; have hp' := mem_ball_iff_norm.mp hy; have hf:= norm_sub_norm_le y x; linarith
lemma sprung {x:A}{a:ℝ}(h: ‖x‖≤a)(hp:a≤ 1/2): ‖bark x‖≤2*a:=by
   let f i:=line i (-x); have ha := (norm_nonneg _).trans h; have hv:= hasSum_geometric_of_lt_one ha (lt_of_le_of_lt hp (by norm_num)); let g i:= (a:ℝ)^i*a; have hk := hv.mul_right a
   have hh i: ‖f i‖≤g i:= (daw ..).trans (pow_le_pow_left₀ (norm_nonneg _) (show ‖-x‖≤a from (norm_neg _).trans_le h) _ |>.trans_eq (pow_succ ..)); unfold bark; rw [norm_neg]; apply (tsum_of_norm_bounded hk hh).trans -- check lemma
   have ht : 0 <1-a:=by linarith
   rw [mul_comm (1-a)⁻¹,←div_eq_mul_inv]; apply (div_le_iff₀ ht).2; nlinarith
abbrev feeD (j:ℕ)(δ:ℝ):ℝ:= j.factorial*(letterP 1 j*(2*(2*δ)))*2^j
lemma shelter {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{f:E→A}{a b:ℝ}(h:0<a)(he:a≤ 1/4)(hp:Brush j a b f x): Brush j (feeD j a) b (bark∘f) x:=by
   let G y:= a⁻¹ • f y; have hG : Brush j 1 b G x:=by have hh:= hp.smul a⁻¹; rwa [Real.norm_of_nonneg (inv_pos.mpr h).le,inv_mul_cancel₀ h.ne'] at hh
   let K : A→L[ℂ] A:= (a:ℂ) • ContinuousLinearMap.id ℂ _; let F (i:A):= bark (K i); have hY:2*a ≤ 1/2:=by linarith
   have hK y (hy:y∈ball (G x) 1): ‖K y‖≤2*a:=by
       change ‖a • y‖≤_; rw [norm_smul,Real.norm_of_nonneg h.le,mul_comm 2 a]; have hr: ‖y-G x‖ < 1:=mem_ball_iff_norm.mp hy; have hh:= norm_sub_norm_le y (G x); apply mul_le_mul_of_nonneg_left _ h.le; linarith only [hh,hG.bound,hr]
   have hf y (hy:y∈ball (G x) 1): DifferentiableAt ℂ F y:= by
       have hx : ‖- K y‖ <1 :=(norm_neg _).trans_lt (lt_of_le_of_lt ((hK y hy).trans hY) (by norm_num)); exact ((mist hx).differentiableAt.comp y K.differentiableAt.neg).neg
   have hV:= hG.pine (beau zero_lt_one hf (fun i hi=> sprung (hK _ hi) hY) j)
   have hX: (fun i=>F (G i))=bark∘ f:=funext fun i=>by change bark (a • a⁻¹ • f i)=_; rw [smul_inv_smul₀ h.ne']; rfl
   rw [hX] at hV; refine ⟨hV.smooth,hp.pos,fun i hi=>?_⟩
   have hn:0≤↑j.factorial * (letterP 1 j*(2*(2*a))) := hV.nonneg; refine (hV.order i hi).trans ?_; rw [one_add_one_eq_two,mul_pow, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi) hn) (pow_nonneg hp.pos _)
end YM.QCD.Coda
