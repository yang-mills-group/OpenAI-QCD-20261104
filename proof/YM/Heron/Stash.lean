import YM.Heron.Trill
import YM.Heron.Quack
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Finset
variable {d:ℕ}(s:Ortho.Skew)(Γ:ℝ→EuPin)(hΓ: EuPin.Path s Γ)(x:ℝ)(p:Multi d)(i:Pinor)(a:Hue)(u v:Flavor 6)(t:Bool)
noncomputable def spiritX(u:Flavor 6)(Γ:ℝ→EuPin)(x:ℝ)(d:ℕ): SpinPol d→ₐ[ℂ] SpinPol d:= spun (maskH u (Γ x)) d
noncomputable def sonic (u:Flavor 6)(Γ:ℝ→EuPin)(x:letters d): SpinPol d:=deriv (fun t:ℝ=> spiritX u Γ t d (atom x)) 0
lemma strokeT(h:v≠u): spiritX u Γ x d (atom (code t p i a v))= atom (code t p i a v):=by
    have he:= rolls (d:=d) v i a p t (1:PClan); change spun _ _ _=_; rw[rolls, show maskH u (Γ x) v=(1:PClan) v from if_neg (Ne.symm h),← he,self_spun]
lemma voicing : ∀ v:letters d, ∃ a:Bool, ∃ p: Multi d, ∃ i:Pinor, ∃ k:Hue,∃ c:Flavor 6,v=code a p i k c:=by
    intro v; rcases v with ⟨⟨p,i,k⟩,c⟩|⟨⟨p,i,k⟩,c⟩; exact ⟨false,p,i,k,c,rfl⟩; exact ⟨true,p,i,k,c,rfl⟩
include hΓ
lemma bannerU(y:SpinPol d):spiritX u Γ 0 d y=y:=by unfold spiritX; rw [hΓ.1,mask_one,self_spun]
lemma suitable(v:letters d) : HasDerivAt (fun x:ℝ=> spiritX u Γ x d (atom v)) (sonic u Γ v) 0:=by
    apply DifferentiableAt.hasDerivAt; obtain ⟨y,p,i,a,b,rfl⟩:= voicing v; by_cases he:u=b; swap; · simp_rw[strokeT Γ _ _ _ _ _ _ _ (Ne.symm he)]; exact differentiableAt_const _
    subst b; unfold spiritX; simp only [rolls,maskH, ↓reduceIte]
    refine DifferentiableAt.fun_sum (fun q _=> DifferentiableAt.fun_sum fun j _=>?_ ); exact ((hops s Γ hΓ p q).mul (fibre s Γ hΓ y i j)).smul (differentiableAt_const (atom (code y q j a u)))
lemma optic (w:letters d)(b:letters d): atom b*sonic u Γ w=-(sonic u Γ w * atom b):=by
    obtain ⟨t,p,i,a,c,rfl⟩:= voicing w; let V:= fun x:ℝ=> spiritX u Γ x d (atom (code t p i a c)); have hp(x:ℝ): atom b*V x= -(V x*atom b):=by unfold V spiritX; rw[rolls,mul_sum,sum_mul]; rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; rw [mul_sum,sum_mul, ←sum_neg_distrib]; apply sum_congr rfl; intro k _; rw [mul_smul_comm,_root_.smul_mul_assoc,atom_flip b,smul_neg]
    have hv:= suitable s Γ hΓ u (code t p i a c); exact (hv.const_mul _).unique ((hv.mul_const _).neg.congr_of_eventuallyEq (Eventually.of_forall hp)) -- const_mul order wrong
lemma jolt (u':List (letters d)): HasDerivAt (fun x=>spiritX u Γ x d (Hail.tagD u')) (slips u' (fun i j=> sonic u Γ i * Hail.tagD j)) 0:=by
    induction u' with
    | nil => rw [slips_nil]; simp_rw [show Hail.tagD (d:=d) []=1 from rfl,map_one]; exact hasDerivAt_const ..
    | cons a l h=> rw [slips_cons]; simp_rw [show Hail.tagD (a::l)=atom a*Hail.tagD l from rfl,map_mul];
                   apply HasDerivAt.congr_deriv ((suitable s Γ hΓ u a).mul h); simp only [bannerU s Γ hΓ]; unfold slips; rw [mul_sum,sub_eq_add_neg, ←sum_neg_distrib]; congr 1; apply sum_congr rfl; intro j _; dsimp only; rw [mul_smul_comm, ←mul_assoc, optic s Γ hΓ,neg_mul, mul_assoc,smul_neg]; rfl
lemma mistB(x:SpinPol d): DifferentiableAt ℝ (fun t=>spiritX u Γ t d x) 0:=by
    rw [← Grass.write x]; simp_rw [map_sum,map_smul]; apply DifferentiableAt.fun_sum; intro i _; rw [show mono i=Hail.tagD (atomList i) from (expression i).choose_spec.2.2.trans (by rw [atomList,Hail.tagD,List.map_ofFn])]; exact DifferentiableAt.fun_const_smul ((jolt s Γ hΓ u _).differentiableAt) _
end YM.Heron
#print axioms YM.Heron.jolt
