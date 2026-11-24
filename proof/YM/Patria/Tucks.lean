import YM.Patria.Digit
/-! Wallet compiler -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
namespace Rolls
variable {X Y:Type}[AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y]
variable (m:ℕ) (u:Averaging)
lemma invite (L:ℕ)(b: Cover)(v: Cover→X)(hv: Odd m)(h: Odd L): Averaging.filter u (L*m) v ((L*m) • b)= Averaging.filter u L (fun x=> Averaging.filter u m v (m • x)) (L • b):=by
    rw [roles,roles, show (fun x:Cover=> Averaging.filter u m v (m • x))=(fun x=> rolls 1 m (menu u) v (m • x)) from funext fun i=>congr_fun (roles ..) _,dilation,cut_space v 1 (menu u) h hv, Nat.mul_comm L m, mul_smul] -- args
open Planned.PrimaryIntegral295 Carrier
open Laurent
lemma tread (c:Side) (x y : Cover)(h : size x ≤ 28*(2*c.val)): Laurent.size (cellar c (c.val • y+x)-y)≤60:=by
    have hE : cellar c (c.val • y+x)-y=cellar c x:=by
         have ht:= balance c (c.val • y+x); have hg : wrap c (c.val • y+x)=wrap c x:=by rw [map_add,map_nsmul]; ext j; simp [Per]
         rw [hg] at ht; conv at ht => lhs; rhs; rw [balance c x]
         apply smul_right_injective Cover c.pos.ne'; dsimp only; rw [smul_sub]; let S:= lift (wrap c x); let u:= c.val • cellar c x; let a:= c.val • y; let b:= c.val • cellar c (c.val • y+x); change b-a=u; have h : a+ (S+u) =S+b:=ht; rw [add_left_comm,add_comm a u] at h; -- bad
         rw [eq_comm]; exact eq_sub_of_add_eq (add_left_cancel h) -- check
    rw [hE]; have ht:= Trellis.scost (L:=c) x; have hp : (size x:ℝ) ≤28*(2*c.val):=by exact_mod_cast h
    suffices h:(size (cellar c x):ℝ)≤60 by exact_mod_cast h
    refine ht.trans ?_; change 4+ (c.val:ℝ)⁻¹ * _≤60; have h :0< (c.val:ℝ):=Nat.cast_pos.mpr c.property; rw [mul_comm _ (Laurent.size x:ℝ),← div_eq_mul_inv]; have he : (Laurent.size x:ℝ)/ c.val ≤56:= (div_le_iff₀ h).mpr (by linarith); linarith
-- Probabilities, exactly for all ℝ vector. With parent tether and charged clocks.
lemma constitution {c f : Side}(V:Ratio c f): ∃ (I:Type)(_ : Fintype I)(_ : Nonempty I)(p:I→ℝ)(t:I→ Cover),(∀ i,0 ≤ p i)∧ (∑ i,p i)=1∧(∀ i x,separation (V.parent (wrap f (V.count.val • x+t i))) (wrap c x) ≤60∧ size (cellar V.count (V.count.val • x+t i)-x)≤60)∧ ∀ (x: Cover→X)(b:Cover), Averaging.filter u V.count.val x b=∑ i,p i • x (b+t i):=by
    obtain ⟨I,hI,hN,p,t,h₁,h₂,hX,hY⟩:= ladder (menu u) (X:=X) 0 V.count.property (widths_menu u) -- V.count.property NatPNat.arg
    refine ⟨I,hI,hN,p,t,h₁,h₂,fun i x=>?_,fun x b=>?_⟩
    · have h:= tread V.count (t i) x ((hX i).trans (Nat.mul_le_mul_right _ (length_menu u))); rw [Streets.owner]; exact ⟨le_trans (Poised.Chute.cost_p ..) h,h⟩
    rw [roles]; exact hY x b
end Rolls
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Rolls.constitution
