import YM.Heron.Rork
import YM.Heron.Stash
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad away)
open Finset
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(u v:Flavor 6)
noncomputable def dawd (x: Points 2)(u:Dot d): SpinPol d →ₗ[ℂ] ℂ:= (lease (chime (oakT d) x)) ∘ₗ LinearMap.mulRight ℂ (line (east d u)) ∘ₗ (twig (oakT d) 0).toLinearMap
noncomputable def charm (x: Points 2)(Γ:ℝ→EuPin)(a:Flavor 6)(i j:Dot d):ℂ:= if i.1=0 then dawd x j (sonic a Γ i.2) else 0
local notation "S"=> Dot d
local notation "Y"=> chime (oakT d) x
lemma tuck(v:letters d):twig (oakT d) 0 (atom v) =line (east d ((0,v): Dot d)):= ExteriorAlgebra.map_apply_ι (rifle (oakT d) _) _
lemma mask(v: Dot d)(s:letters d): dawd x v (atom s)= unionB Y (east d (0,s)) (east d v):=by
    unfold dawd; change lease (chime (oakT d) x) (twig (oakT d) 0 (atom s)*line (east d v))=_; rw[tuck]; rw[← show pwn [east d v]=line (east d v) from (by simp [pwn]),veil]; simp [pwn,DawnS.clean1]
include hx
lemma motor(v: Dot d)(s:letters d): dawd x v (atom s)=if v.1=(0:Fin 2) then 0 else linked (x 0) (x v.1) s v.2:=by
    rw[mask, east,east,mounted,mounted,DawnS.sector x hx]; by_cases h:v.1=0; · unfold UV.Free.pair; simp only [h,↓reduceIte]; -- dep
    unfold UV.Free.pair linked; rw [if_neg (Ne.symm h), if_neg h]
omit hx
variable (Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(p q:Multi d)(i j:Pinor)(a b:Hue)(t w:Bool)(r:Fin 2)
local notation "κ"=> code t p i a u
local notation "μ"=> code w q j b v
lemma ch_phase(z:ℝ) : spiritX u Γ z d (atom κ) = ∑ k:Multi d,∑ j:Pinor,(multiMove (Γ z) p k * splice t (Γ z) i j) • atom (code t k j a u):=by rw[spiritX,rolls, maskH]; simp
include hΓ
lemma sunny (h:v≠u) (T: Dot d) : dawd x T (sonic v Γ κ)=0:=by
    suffices H:sonic v Γ κ=0 by rw[H,map_zero]
    unfold sonic; simp_rw [fun z:ℝ=> strokeT Γ z p i a v u t (Ne.symm h)]; simp
include hx
lemma hazeY (s:letters d): dawd x (0,s) (sonic u Γ κ)=0:=by
     let T:= (dawd x (0,s)).toContinuousLinearMap.restrictScalars ℝ; let P:=fun t:ℝ=>spiritX u Γ t d (atom κ); have hp: T ∘ P=fun _=>0:=by
          funext z; change dawd x (0,s) _ =0; unfold P; rw[ch_phase]; simp_rw [map_sum,_root_.map_smul, motor x hx]; simp
     apply (T.hasFDerivAt.comp_hasDerivAt (0:ℝ) (suitable Δ Γ hΓ u κ)).unique; exact (hp.symm ▸ hasDerivAt_const 0 (0:ℂ))
lemma hazeK (h: ¬ (a=b∧u=v∧w=(!t)) ) : dawd x (1, μ) (sonic u Γ κ)=0:=by
     let T:= (dawd x (1, μ)).toContinuousLinearMap.restrictScalars ℝ; let P:=fun t:ℝ=>spiritX u Γ t d (atom κ); have hp: T ∘ P=fun _=>0:=by
          funext z; change dawd x (1,μ) _=0; unfold P; rw[ch_phase]; simp_rw[map_sum, _root_.map_smul,motor x hx]; simp only [(show (1:Fin 2)≠0 from (by decide)), if_false]; apply sum_eq_zero; intro p' _; apply sum_eq_zero; intro j' _; apply smul_eq_zero_of_right; by_cases he:w=t; · rw [he]; exact blank ..
          have hz:w=(!t):=by cases t <;> cases w <;> simp_all
          rw[hz]; exact lowSt t p' q j' j a b u v _ _ (fun hv=> h ⟨hv.1,hv.2,hz⟩)
     apply (T.hasFDerivAt.comp_hasDerivAt (0:ℝ) (suitable Δ Γ hΓ u κ)).unique; exact (hp.symm ▸ hasDerivAt_const 0 (0:ℂ))
local notation "L"=> steps p
local notation "M"=> steps q
local notation "K"=> piD (1:Fin 2) (!t) q j a u
local notation "R"=> pose (formT (!t)) (deck j) M (x 1)
local notation "Y°"=> twistS (formT t) (fromCenter Δ.val (x 0)) R
lemma F_line(y:ℝ): dawd x K (spiritX u Γ y d (atom κ))= -dotL (deck i) (tent (x 0) t p R (Γ y)):=by
    have hv: x 1 ≠ x 0:=(show Injective x.ofLp from hx).ne (show (1:Fin 2)≠0 by decide) -- hx reduc
    have ht:=care _ (deck j) (actual (!t)) (x 1) M; let U:= ({x 1}:Set E4)ᶜ; rw[ch_phase, poseP (Γ y) p (x 0) R (U:=U) isOpen_compl_singleton (show x 0 ∈ U from Ne.symm hv) (fun x h=>ht.live x h) t]; rw [deckP]; simp only[map_sum, _root_.map_smul,motor x hx, Finset.sum_apply]; -- macro K.fst
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro p' _; 
    rw [show (∑ j':Pinor,(multiMove (Γ y) p p' * splice t (Γ y) i j') • _) = ∑ j':Pinor,(multiMove (Γ y) p p' * splice t (Γ y) i j')* linked (x 0) (x 1) (code t p' j' a u) (code (!t) q j a u) from ?_] -- test
    · change _= -(multiMove (Γ y) p p' * Matrix.mulVec (splice t (Γ y)) (deriveL (steps p') R (x 0)) i); unfold Matrix.mulVec dotProduct; rw[Finset.mul_sum,←sum_neg_distrib]; apply sum_congr rfl; intro j' _; have H:= hook (!t) q p' j j' a a u u _ _ hv ⟨rfl,rfl⟩; rw [Bool.not_not] at H; rw [flying,H]; ring
    apply sum_congr rfl; intro j _; rw [if_neg (by exact (show (1:Fin 2)≠0 from (by decide)))]; rfl
end YM.Heron
#print axioms YM.Heron.motor
#print axioms YM.Heron.hazeK
#print axioms YM.Heron.F_line
