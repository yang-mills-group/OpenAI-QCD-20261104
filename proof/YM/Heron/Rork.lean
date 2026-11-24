import YM.Heron.Beam
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad away)
open Finset
variable {d:ℕ}(x:Points 2)(y:E4) (p q: Multi d)(i j:Pinor)(c e:Hue)(u v b: Flavor 6)(f s:Fin 2)(t t':Bool)
noncomputable def piD {d:ℕ}(f:Fin 2)(t:Bool)(p:Multi d)(i:Pinor)(c:Hue)(u:Flavor 6):Dot d:= (f,code t p i c u)
local notation "V"=> dotL
local notation "P"=> piD f t p i c u
local notation "Q"=> piD s t' q j e v
variable (a k:Axis)(m n: Multi 8)
lemma c_absent (h: ¬(t=false ∧ t'=true ∧ c=e ∧ u=b ∧ v=b)) : crossG b a m n x y P Q=0:=by
    unfold crossG; apply sum_eq_zero; intro h' _; apply sum_eq_zero; intro r _; apply sum_eq_zero; intro g _
    suffices he: colorJ x y (code true m r h' b) P=0∨colorJ x y (code false n g h' b) Q=0 by
       rcases he with h|h <;>simp only[h,mul_zero,zero_mul]
    by_cases he : t=false; swap; · left; cases t; contradiction; exact blank ..
    by_cases hx :t'=true; swap; · right; cases t'; exact blank ..; contradiction
    by_cases ht:c=h'∧u=b
    · subst t'; right; have hw:¬(e=h' ∧ v=b):= fun hr=> h ⟨he,rfl,ht.1.trans hr.1.symm,ht.2,hr.2⟩
      exact lowSt true q n j g e h' v b (x s) y hw
    subst t; left; exact lowSt false p m i r c h' u b (x f) y ht -- syntax
lemma aus (h: ¬(t=false ∧ t'=true ∧ c=e ∧ u=b ∧ v=b)): beeD b a k x y P Q=0:=by unfold beeD; simp_rw [c_absent _ _ p q i j c e u v b f s t t' _ _ _ h]; simp
local notation "K"=> piD f false p i c u
local notation "R"=> piD s true q j c u
local notation "σ"=>pose gamma (deck i) (steps p) (x f)
local notation "τ"=>pose (FlipT gamma) (deck j) (steps q) (x s)
variable (hx:x f≠ y)(hz:x s ≠ y)
include hx hz
lemma convoy : crossG u a m n x y K R=dotL (deriveL (steps m) σ y) (cog gamma a (deriveL (steps n) τ y)):=by
    unfold crossG; rw [sum_eq_single c]; swap
    · intro b _ h; apply sum_eq_zero; intro i' _; apply sum_eq_zero; intro j' _; rw [show colorJ x y (code true m i' b u) K=0 from lowSt false p m i i' c b u u (x f) y (fun he=> h he.1.symm),zero_mul,mul_zero]
    rotate_right; · simp
    have he(i':Pinor): colorJ x y (code true m i' c u) K = deriveL (steps m) σ y i':= hook false p m i i' c c u u (x f) y hx ⟨rfl,rfl⟩
    have hp(j':Pinor): colorJ x y (code false n j' c u) R= deriveL (steps n) τ y j':= hook true q n j j' c c u u (x s) y hz ⟨rfl,rfl⟩
    rw [bore,cogP]; simp_rw [he,hp]; unfold Matrix.mulVec dotProduct; apply sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply sum_congr rfl; intro j _; ring -- unfolding ∑
lemma roads : beeD u a k x y K R=blaze gamma σ τ a k y:=by
    unfold beeD; simp_rw[convoy x y p q i j c u f s _ _ _ hx hz]; simp_rw[show ∀ a:Axis,steps (UV.first a)=[a] from tag_p (x f) y hx,snaps]; rfl
-- swapped gamma streak
omit hx hz
lemma sister (A:TinG)(F G: Spins): blaze A F G a k y= -blaze (FlipT A) G F a k y:=by
    unfold blaze streak; simp only [Pi.add_apply]; simp only [bore];
    have he (a:Axis)(v w:Faces) : v ⬝ᵥ (cog A a w)= w ⬝ᵥ (cog (FlipT A) a v):= (flip_mul A a v w).symm.trans (dotProduct_comm ..); rw [he,he,he,he] -- orientation may loop
    ring
end YM.Heron
#print axioms YM.Heron.roads
#print axioms YM.Heron.sister
