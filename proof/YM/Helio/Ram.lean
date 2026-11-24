import YM.Helio.Sigma
import YM.QCD.Leaf.Lift
import YM.QCD.Garden.Lift

/-! # uniform own post estimates for re-sym saturated. Comparator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Lat Function Lattice Wilson Kit Cost Run Rudder Finset RG Eyrie Stationary Sparks Revolve Paths Quarry Orbit Garden
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n: Side}{I:Type}{k B:ℕ}{C:I→Bloom k}{σ t η δ c p ξ b:ℝ}
open Filter Metric Matrix Classical
lemma skyP (k:ℕ)(hr:0<σ)(ht:0≤b): ∃ δ C :ℝ,∃ m:ℕ, 0 < δ ∧ 0<C ∧∀ B:ℕ,m≤B→∀ (ξ:ℝ),0<ξ→ξ≤1→∀ (n:Side)(W: Bloom k), W.Spins → Own n (δ*ξ) b B (trackP W ξ n) (C*(W.paid σ)*ξ^k):=by
  let s:=σ/2; have hx:=half_pos hr
  obtain ⟨c,δ,hp,hD,hA⟩:= skiff s hx
  have hc:=zero_lt_one.trans_le hp
  obtain ⟨m,d,hy,hB,H⟩:= ballad b hr
  obtain ⟨M,hM⟩:=exists_nat_gt (b/s)
  let w:=min δ d
  refine ⟨w,Real.exp (b*(1+2*(k:ℝ)))*c^k*Real.exp (σ*m),max (2*m) M,lt_min hD hB,by positivity,fun B hz ξ h hh n W hZ=>?_⟩
  have he:= (le_max_left ..).trans hz
  have hE:0<B:=by omega
  have hF: b/B≤s:=by
    have hu:0 < (B:ℝ):=by exact_mod_cast hE
    have hd:(M:ℝ) ≤ B:=by exact_mod_cast (le_max_right ..).trans hz
    apply (div_le_iff₀ hu).2; have h: b/s ≤ B :=hM.le.trans hd; have hh:= (div_le_iff₀ hx).1 h; unfold s; linarith
  have hf: δ/ξ*ξ^2=δ*ξ:=by field_simp
  have hv:Bottle s c (δ/ξ) ξ:= ⟨fun n W x Y hv i=> hA ξ h hh n W x Y i (hf ▸ hv)⟩
  have hg:= yardage (n:=n) W hv hF hc.le ht h.le hE hZ; rw [hf] at hg; have hi:=W.price_nn
  apply ((hg.clip (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))).meet ((rides_for (f:=n) 0 W.tail ht hB hr hy he H).clip (show w*ξ≤d from (mul_le_of_le_one_right (lt_min hD hB|>.le) hh).trans (min_le_right ..))) (mul_pos (lt_min hD hB) (by positivity)) ht (by unfold pricey; positivity) (by positivity)).mono
  unfold pricey Bloom.paid; rw [Bloom.span,Nat.cast_add,Nat.cast_sum,mul_add,Real.exp_add]; unfold s Atom.length; push_cast; rw [mul_pow]; apply le_of_eq; rw [show 2*(σ/2)=σ by ring]; rw [mul_add σ,Real.exp_add]; ac_rfl

lemma blue (k)(hσ:0<σ)(ht:0≤t): ∃ δ p:ℝ,∃ B:ℕ,0<δ∧0<p∧∀ (V:Type)(A:V→Bloom k)(R:ℝ), Fractal A σ R→∀ ξ:ℝ,0<ξ→ξ≤1→∀ n b,B≤b → Own n (δ*ξ) t b (wild A ξ n) (p*R*ξ^k):=by
  obtain ⟨δ,P,B,hD,hP,H⟩:=skyP k hσ ht
  refine ⟨δ,P,B,hD,hP,fun V A R h ξ hp ht' n b hB=> ?_⟩
  apply (Heritage.congregation (T:=fun i=> trackP (A i) ξ n) (mul_pos hD (by positivity)) ht (fun i=> H b hB ξ hp ht' n _ (h.sect i)) ((h.bills.mul_left P).mul_right (ξ^k)) (fun U=> (earns U h hp ht' hσ).of_norm.hasSum)).mono
  rw [tsum_mul_right,tsum_mul_left]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h.bill hP.le) (by positivity)
lemma blueP (k)(hσ:0 < σ)(ht:0≤t): ∃ δ p:ℝ,∃ B:ℕ,0<δ∧0<p∧∀ (V:Type)(A:V→Bloom k)(R:ℝ), Fractal A σ R→∀ ξ:ℝ,0<ξ→ξ≤1→∀ n b,B ≤ b →Own n (δ*ξ) t b (wild (frosting A) ξ n) (p*R*ξ^k):=by
  have h : 0<σ/(1+(k:ℕ)):=div_pos hσ (by positivity)
  obtain ⟨δ,P,B,hD,hP,H⟩:=blue k h ht
  refine ⟨δ,P*Real.exp (σ*(2*k)),B,hD,by positivity,fun V A R hZ ξ hv hm n b hB=>?_⟩
  rw [mul_assoc P]; apply H (Fruited V) (frosting A) _ (coined _ h.le hZ ?_) ξ hv hm n b hB; rw [div_mul_cancel₀ _ (by positivity)]

end YM.QCD.Leaf.LeafM
#print axioms YM.QCD.Leaf.LeafM.blueP
