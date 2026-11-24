import YM.Bank.Avalon
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Warm
open Function Lattice Laurent Bloch Matrix Metric Precision Exterior Wilson
open Next.Free Work.F06 Knot Avalon Avalon.Worth Learn
open AnalyticBridge.LocalGaussianLaws.Current Finset
open scoped ContDiff Topology BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
variable {c f:Side} {j:ℕ} {m n :Type}[Fintype m][Fintype n]
local notation "δ"=>TypeFace 1
local notation "θ"=>TypeFace 2
lemma counterparts {a b:ℝ}(H:Bed)(h:Numeric (H.metric.acts c) a b)(hp:H.metric.safe)(ha:0<a)(X: Matrix m (Co c θ) ℝ)(Y:Matrix n (Co c θ) ℝ):
     approached (X*learned H c*Y.transpose)=(stageVolume c)⁻¹ • ((approached (X*d 1 c)*rotations c δ)*solo c (spaceK H.metric)*(approached (Y*d 1 c)*rotations c δ)ᴴ):=by
   simp only [prom_mul]; rw [learned_eq hp h ha]; unfold gaugeΞ; rw [prom_adj]; simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.smul_mul,Matrix.mul_smul]
lemma fibSum {K: Momentum→Matrix δ δ ℂ} (X:Matrix m (Co c δ) ℂ)(Y:Matrix n (Co c δ) ℂ)(i j):
   (X*solo c K*Yᴴ) i j= ∑ p : Site c,∑ y:δ,∑ x:δ, X i (p,x)*K (mon p) x y*(star (Y j (p,y))) :=by
     rw [Matrix.mul_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun p _=>sum_congr rfl fun y _=>?_; rw [Matrix.mul_apply,← sum_mul,Matrix.conjTranspose_apply,Fintype.sum_prod_type,sum_eq_single p]; · simp [solo,fiber]
     intro i _ hi; simp [solo,fiber,hi]; simp
lemma portrait (a b:ℝ)(ha:0<a)(hb:0≤b)(j:ℕ)(u v:List Axis)(hu:u.length+2≤j)(hv:v.length+2≤j) :∃ C:ℝ,0≤C ∧ ∀ {c f:Side}(r:Ratio c f)(F B:Bed){J Q R}(b':ℝ),TowerW j r F B J R Q→ F.metric.safe → (∃ z:ℝ,0≤z∧B.metric.strip z b) →Numeric (F.metric.acts f) a b'→ Numeric (B.metric.acts c) a b'→∀ x y,
     ‖((rocker f θ u*J)*learned B c*(rocker f θ v*J).transpose) x y‖ ≤ C/(r.count.val:ℝ)^(4+u.length+v.length):=by
   obtain ⟨E,e₀,HE⟩:=pose a b ha hb j u hu; obtain ⟨D,d₀,HD⟩:=pose a b ha hb j v hv
   let N:ℝ:= Fintype.card δ; let V:= E*D/lum a; have hw:= luminous ha; have hV :0≤V:=by unfold V; positivity
   refine ⟨N^2*V,by positivity,fun {c f} r F B {J Q R} b' G hF hl h0 h1 i j=> ?_⟩
   obtain ⟨z,hz,hB⟩:= hl; have hp:=Row.rights _ _ hB hz
   let X:= approached (rocker f θ u*(J*d 1 c))*rotations c δ; let Y:= approached (rocker f θ v*(J*d 1 c))*rotations c δ; let l:ℝ:=r.count.val; have him :0 < l:= side_pos _
   rw [← Complex.norm_real]; change ‖approached _ _ _‖ ≤ _; rw [counterparts B h1 hp ha]; rw [Matrix.smul_apply,norm_smul,Matrix.mul_assoc (rocker f θ u) J (d 1 c),Matrix.mul_assoc (rocker f θ v) J]; rw [fibSum];
   let U:=fun (p:Site c) (x y:δ)=> X i (p,x)*spaceK B.metric (mon p) x y *star (Y j (p,y))
   let w:= 4+u.length+v.length; let B₀:= V/l^w; let F₀:=(c.val:ℝ)
   have H p x y: ‖U p x y‖ ≤ B₀:=by
       unfold U; rw [norm_mul,norm_mul,norm_star]; let a':=‖mon p‖
       have hg : ‖X i (p,x)‖≤ E*a'/l^(2+u.length):= HE _ _ _ _ G hF ⟨z,hz,hB⟩ h0 _ _ _ _
       have hh : ‖Y j (p,y)‖≤ D*a'/l^(2+v.length):= HD _ _ _ _ G hF ⟨z,hz,hB⟩ h0 _ _ _ _
       by_cases hk:mon p=0
       · unfold a' at hg; rw [hk,norm_zero,mul_zero,zero_div] at hg; rw [show ‖X i (p,x)‖=0 from le_antisymm hg (norm_nonneg _),zero_mul,zero_mul]; unfold B₀; positivity
       have ht: ‖spaceK _ (mon p) x y‖≤(lum a*a'^2)⁻¹:= (QCD.Cost.north (spaceK B.metric (mon p)) _ _).trans (purse _ h1 ha p hp hk).2 -- annotate
       have hl : 0<a':=norm_pos_iff.mpr hk
       refine (mul_le_mul (mul_le_mul hg ht (norm_nonneg _) (by positivity)) hh (norm_nonneg _) (by positivity)).trans_eq ?_
       unfold B₀ V w; simp only [pow_add]; field_simp
   change ‖(stageVolume c)⁻¹‖*‖∑ p : Site c, ∑ y,∑ x:δ,U p x y‖ ≤ _
   have ht : ‖∑ p:Site c,∑ y:δ,∑ x:δ,U p x y‖ ≤ ∑ _p:Site c, ∑ _y:δ,∑ _x:δ,B₀ :=
       (norm_sum_le ..).trans (sum_le_sum fun p _=> (norm_sum_le ..).trans (sum_le_sum fun y _=> (norm_sum_le ..).trans (sum_le_sum fun x _=> H p x y)))
   apply (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq; unfold stageVolume; simp only [norm_inv,norm_pow,Complex.norm_natCast,sum_const,card_univ,nsmul_eq_mul,site_card,Nat.cast_pow]; unfold B₀ w l N; have hy:=side_pos c; field_simp
end YM.Bank.Warm
#print axioms YM.Bank.Warm.portrait
