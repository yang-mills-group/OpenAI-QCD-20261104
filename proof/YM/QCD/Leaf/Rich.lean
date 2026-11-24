import YM.QCD.Leaf.Lift

/-! # ray-small genuine -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Lat Function Lattice Wilson Kit Cost Run Rudder Finset RG Eyrie Stationary Sparks Revolve Paths Quarry Orbit Garden
open Filter Metric
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n: Side}{I:Type}{k B:ℕ}{C:I→Bloom k}{σ t η δ c p ξ:ℝ}
variable (W:Bloom k)(U:Grid n)
def dog (ξ:ℝ)(x:Site n)(i):= ξ^2/(ξ^2+‖(W.petals i).atSite U x‖^2)
lemma rate_dog (hx:0<ξ)(x:Site n)(i): 0≤dog W U ξ x i ∧ dog W U ξ x i ≤1:=by unfold dog; refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩; simp
lemma vet (x:Site n): satin W x ξ U=(↑(∏ i,dog W U ξ x i):ℂ) • W.taste U x:=by
  unfold satin Bloom.taste Bloom.hues; rw [smul_sum]; apply sum_congr rfl; intro i _; rw [smul_smul]; congr 1; rw [← Complex.ofReal_mul,← prod_mul_distrib]; unfold pulp dog; rfl

def meek (U:Grid n) (r:ℝ) : Prop:=∀ W:Slot,∀ x: Site n, ‖W.atSite U x‖≤r
lemma growth (h: meek U t)(hp:0<ξ)(hu:0≤t): ‖trackP W ξ n U-W.tonic 0 U‖ ≤W.price*k*(t^(k+2)/ξ^2) :=by
  let f x:=∏ i,dog W U ξ x i
  have ht (x:Site n): ‖W.taste U x‖ ≤ t^k*W.price:=by
    unfold Bloom.taste Bloom.hues Bloom.price; rw [mul_sum]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; rw [norm_smul,Complex.norm_real,norm_prod]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simpa using Finset.prod_le_prod (s:=univ) (g:=fun _=> t) (fun j _=> norm_nonneg ((W.petals j).atSite U x (i j))) (fun j _=> by rw [Real.norm_eq_abs,← EuclideanSpace.basisFun_inner]; apply (abs_real_inner_le_norm ..).trans; rw [OrthonormalBasis.norm_eq_one,one_mul]; exact h _ _)
  have hf (x: Site n): ‖f x-1‖ ≤ k*(t^2/ξ^2):=by
    let a:= dog W U ξ x; have hh (S:Finset (Fin k)): ‖(∏ i∈S,a i)-1‖ ≤ S.card*(t^2/ξ^2):=by
      induction S using Finset.induction_on with
      | empty=> simp
      | insert i s hi ih=>
        have hV: |a i-1|≤ t^2/ξ^2:=by
          have hz : ‖(W.petals i).atSite U x‖^2 ≤ t^2:=pow_le_pow_left₀ (norm_nonneg _) (h _ _) _
          rw [abs_of_nonpos (sub_nonpos.mpr (rate_dog W U hp x i).2),neg_sub]; unfold dog
          rw [one_sub_div (by positivity)]
          simp only [add_sub_cancel_left]; apply le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (show ξ^2≤_ from le_add_of_nonneg_right (by positivity))) (by gcongr)
        rw [prod_insert hi,card_insert_of_notMem hi]; push_cast; rw [show a i*_ - 1 = a i*((∏ i∈s, a i)-1)+(a i-1) by ring]
        refine (norm_add_le ..).trans ((add_le_add (le_trans ?_ ih) hV).trans (le_of_eq (by ring)))
        rw [norm_mul, Real.norm_of_nonneg (rate_dog W U hp x i).1]; exact mul_le_of_le_one_left (norm_nonneg _) (rate_dog W U hp x i).2
    simpa [f,a] using hh univ
  unfold trackP Bloom.tonic yard; rw [← sub_mul]; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (rotation_price (circle ..))).trans; rw [sub_eq_add_neg, show - _= (-1:ℂ) • rides (Equiv.refl _) (W.taste U) by rw [neg_one_smul], ride_smul,ride_add]; apply rides_size _ _ _ _; swap; -- inspect
  · apply mul_nonneg (mul_nonneg W.price_nn (by positivity)) (by positivity)
  intro x; change ‖satin W x ξ U+(-1:ℂ) • W.taste U x‖≤ _
  rw [vet, ← add_smul, ← sub_eq_add_neg, norm_smul]; rw [show ((↑(∏ i,dog W U ξ x i):ℂ)-1)=↑(f x-1) by simp [f],Complex.norm_real]; exact (mul_le_mul (hf _) (ht _) (norm_nonneg _) (by positivity)).trans (le_of_eq (by rw [pow_add]; ring))

lemma lodge (U:Grid n)(h:Fractal C σ p)(hs:0<σ)(hm:meek U t)(hp:0<ξ)(hξ:ξ≤1)(ht:0≤t): ‖wild C ξ n U-dust C n U‖ ≤ p*k*(t^(k+2)/ξ^2):=by
  let D:= (k:ℝ)*(t^(k+2)/ξ^2); have hd:0≤ D:=by unfold D; positivity
  have he i : ‖trackP (C i) ξ n U-(C i).tonic 0 U‖≤ (C i).paid σ*D:=by apply le_trans (growth (C i) U hm hp ht); rw [mul_assoc]; apply mul_le_mul_of_nonneg_right ((C i).paidUp hs.le) hd
  have hh:=h.bills.mul_right D; have hx:=hh.of_nonneg_of_le (fun _=>norm_nonneg _) he
  rw [wild,dust, ← Summable.tsum_sub (earns U h hp hξ hs).of_norm (h.tonics ..).of_norm]
  apply (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hh).trans _); rw [tsum_mul_right,mul_assoc]; exact mul_le_mul_of_nonneg_right h.bill hd
end YM.QCD.Leaf.LeafM
