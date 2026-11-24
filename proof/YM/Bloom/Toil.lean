import YM.Bloom.Even
/-! # weighted gauge envelopes at pilot. no period costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.TreeP
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B B₀ r L n D d:ℕ}{a b u v t s W A T ε C y' z' ψ:ℝ}
variable (p:Zinc G k)(q:Zinc G m)(x y:Cover)
variable (h:Eyes G D L (2*n) j a v b ε s C)
noncomputable def billN (t:ℝ)(D:ℕ):= t^(4+2*D)
lemma priceW (hk:1 ≤ W)(hp:k ≤ D): 0 ≤ favorU W p ∧ favorU W p ≤ billN W D:=⟨pow_nonneg (zero_le_one.trans hk) _,pow_le_pow_right₀ hk (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ((rare p).trans hp)) 4)⟩
include h
lemma costume (hp:k≤ D)(x:Cover)(hk:1 ≤ W): cusp (pots W f p x) () ≤ billN W D*C:=by unfold pots; rw [cups_scale,Complex.norm_real,Real.norm_of_nonneg (priceW p hk hp).1]; exact mul_le_mul (priceW p hk hp).2 ((venture f p x).trans (h.price k hp p)) (cups_pos ..) ((priceW p hk hp).1.trans (priceW p hk hp).2)
lemma liteU (hp:k ≤ D)(ht:L ≤ B) (i: Col G f)(hi:pots W f p x () i≠0): i∈clique G f 2 B (wrap f x):=by unfold pots at hi; rw [Matrix.smul_apply,smul_eq_mul] at hi; exact stays0 _ x _ _ _ (right_ne_zero_of_mul hi) ((h.span _ hp p).trans ht)
lemma idolV (hp:k≤ D)(hq:m≤D) (F:Bed)(hV:Grain a v b F f) (hw:1 ≤ W) : ‖pop1 (pots W f p x) (pots W f q y) (heartP F G f) () ()‖ ≤ billN W D*(billN W D*C):=by
    unfold pop1 pots; rw [Matrix.smul_mul,Matrix.smul_mul, Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_apply,Matrix.smul_apply,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (priceW q hw hq).1,Real.norm_of_nonneg (priceW p hw hp).1]; have hx:0 ≤ billN W D:=pow_nonneg (zero_le_one.trans hw) _; exact mul_le_mul (priceW p hw hp).2 (mul_le_mul (priceW q hw hq).2 (h.youth k hp m hq p q f F hV x y) (norm_nonneg _) hx) (mul_nonneg (priceW q hw hq).1 (norm_nonneg _)) hx
variable (g: Ratio c f) (J: Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed) (ht:Fare j a b g J F H)
-- inputs dimension aperture
structure Factor (t:ℝ)(D:ℕ)(c:Side)(e:ℝ): Prop where
     urge : 1 ≤ t
     posse :0 ≤ e
     hips (k:ℕ)(hk:k≤ D): t^(4+2*k)/(c.val:ℝ)^(2+k) ≤ e
include ht
variable (hq:Factor W D g.count A)
include hq
lemma tilted (x:Cover)(y: Cover)(hk:k≤ D)(hm:m≤D): ‖pop1 (pots W f p x) (pots W f q y) (treasureP f c G H (paid G J)) () ()‖ ≤ C*A^2:=by
     let R:= treasureP f c G H (paid G J); let i:=favorU W p; let t:=favorU W q; have hi:=priceW p hq.urge hk; have hw:=priceW q hq.urge hm; have hi':0 ≤ i:=hi.1; have ht':0≤ t:=hw.1; let l:=(stemP p).length; let s:=(stemP q).length; let z:=(g.count.val:ℝ); have hz:0 <z:=side_pos _
     unfold pop1 pots; rw [Matrix.smul_mul,Matrix.smul_mul, Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_apply,Matrix.smul_apply,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht',Real.norm_of_nonneg hi']; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h.pearly k hk m hm p q g J F H ht x y) ht') hi')
     let X:=i/z^(2+l); let Y:= t/z^(2+s); change i*(t*(C/z^(4+l+s))) ≤ _; rw [show 4+l+s=(2+l)+(2+s) by omega,pow_add,show i*(t*(C/(z^(2+l)* z^(2+s))))=C*(X*Y) from by unfold X Y; ring,sq]; exact mul_le_mul_of_nonneg_left (mul_le_mul (hq.hips l ((rare p).trans hk)) (hq.hips s ((rare q).trans hm)) (div_nonneg ht' (pow_nonneg hz.le _)) hq.posse) h.pay.le
noncomputable def crop (G:Gauge)(W C T A:ℝ)(D B:ℕ):= let α:= billN W D*(C*T*(fareV G 1 1*4)); α+fareV G 1 (B+1)*(α+C*A)
lemma stalkE (hk:k≤ D)(hs:L ≤ B₀)(o:Site c) (R:Matrix (Col G f) (Col G c) ℂ) (hr:∀ i (hp:i∈clique G f 2 B₀ (wrap f x)) v, R i v≠0 →v∈clique G c 2 B o) (hR:∀ i,cusp (paid G J-R) i≤ T)(hT:0 ≤ T): cusp (pots W f p x*paid G J*radi G c) () ≤ crop G W C T A D B :=by
     let z:=(g.count.val:ℝ); let ξ:=(stemP p).length; have hz:0 < z:= side_pos _; let P:=glimpse p; let α:=voteP f p x; let C₁:=C/z^(2+ξ); have hc:=h.pay; have hh:= hq.urge; let μ:= favorU W p; have hm:=priceW p hq.urge hk; have hu:0 ≤ μ:=hm.1
     have hg:= profuse (P:=P) (x:=x) (i:=p.2) (p:=p.1.2.1) (b:=B₀) o (J:=J) ((h.span _ hk p).trans hs) (show 0≤ C₁ by unfold C₁; positivity) (h.ask k hk p g J F H ht x) R hr hR hT
     unfold pots; rw [Matrix.smul_mul,Matrix.smul_mul,cups_scale,Complex.norm_real,Real.norm_of_nonneg hu]; apply le_trans (mul_le_mul_of_nonneg_left hg hu); let d:=fareV G 1 1*4; let j:=fareV G 1 (B+1); let Z:= billN W D*(C*T*d); let Y:=tollP p*T*d; have hd:0 ≤ d:=by unfold d fareV; positivity
     change μ*(Y+j*(Y+C₁)) ≤ Z+j*(Z+C*A)
     have hp: μ*Y ≤ Z:= mul_le_mul hm.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h.price k hk p) hT) hd) (mul_nonneg (mul_nonneg (toll_pos _) hT) hd) (hu.trans hm.2)
     rw [show μ*(Y+j*(Y+C₁))= μ*Y+j*(μ*Y+μ*C₁) from by ring]; apply add_le_add hp; apply mul_le_mul_of_nonneg_left (add_le_add hp _) (show 0 ≤ j from by unfold j fareV; positivity)
     exact Eq.trans_le (show μ*C₁=C*(μ/z^(2+ξ)) by unfold C₁; ring) (mul_le_mul_of_nonneg_left (hq.hips ξ ((rare p).trans hk)) hc.le)
lemma light_view (hk:k≤ D)(hs:L ≤ B₀)(o:Site c) (R:Matrix (Col G f) (Col G c) ℂ) (hr:∀ i (hp:i∈clique G f 2 B₀ (wrap f x)) v, R i v≠0 → v∈clique G c 2 B o) (hR:∀ i,cusp (paid G J-R) i≤ T)(hT:0 ≤ T) (U: Directions G c)(hv:‖U‖ ≤ y')(hW:|ψ⁻¹|≤ z') : cusp (pots W f p x*paid G J*jetO G c ψ U) () ≤ z'*(crop G W C T A D B * y'):= pockets U _ () (stalkE p x h g J F H ht hq hk hs o R hr hR hT) hv hW
end YM.Bloom.TreeP
#print axioms YM.Bloom.TreeP.light_view
#print axioms YM.Bloom.TreeP.tilted
