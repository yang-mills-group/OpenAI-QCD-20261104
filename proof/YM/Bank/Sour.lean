import YM.Bank.Warm
import YM.Bank.Loupe
import YM.Bank.Steeps
/-! finish cumulative sp -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bank
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Pilot Pap Next.Free
open Pearl (beamH beamP)
open Matrix Lat Free Flume
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ComplexConjugate
variable {j:ℕ} {m n:Type}[Fintype m][Fintype n] {f c:Side}
lemma cap_g : ∃ C:ℝ, 0 ≤ C ∧ ∀ n:Side, ∑ p:Site n, (n.val:ℝ)⁻¹^4 / ‖tuning p‖ ≤ C:=by
   obtain ⟨C,hc,H⟩:=pole_tax true; let s:=(2*Real.pi)⁻¹^4; have hs:0 ≤ s:=pow_nonneg (by positivity) _; refine ⟨s*C,by positivity,fun n=>le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (H n) hs)⟩
   rw [mul_sum]; exact sum_congr rfl fun i _=> by unfold s grid beamH; simp only [↓reduceIte]; have hh:= Real.pi_pos; field_simp
lemma fiberSum (X:Matrix m (Lat.Row c) ℂ)(Y:Matrix n (Lat.Row c) ℂ) (K: Site c→Bundle)(i j) :
    (X*install K*Yᴴ) i j = ∑ p:Site c, ∑ y:Fiber,∑ x:Fiber, (X*leaf c) i (p,x)*K p x y*star ((Y*leaf c) j (p,y)):=by
    let V:=X *leaf c; let U:= Y*leaf c; let M:=lined K; rw [show X*install K*Yᴴ=V*M*Uᴴ by unfold install V M U; rw [conjTranspose_mul,←Matrix.star_eq_conjTranspose]; simp only [Matrix.mul_assoc]] -- ← wrong targ
    rw [Matrix.mul_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun p _=> sum_congr rfl fun y _=>?_; rw [Matrix.mul_apply,Fintype.sum_prod_type, sum_eq_single p, Matrix.conjTranspose_apply]; · unfold M; simp [fiber_k,Bloch.fiber,sum_mul]; rfl
    intro i _ hi; simp [M,fiber_k,Bloch.fiber,hi]; simp
local notation "N"=> (Fintype.card Fiber:ℝ)
lemma spin_echo (h:2≤j)(u v:List Axis) (hu:u.length+2≤j)(hv:v.length+2≤j) : ∃ C:ℝ,0≤ C∧∀ {c f:Side}(H:Ratio c f)(D B:Train j){U X Q}, Giant j H D B U X Q→ ∀ i j,
    ‖(oldDiff U u* stage B c * (oldDiff Xᴴ v)ᴴ) i j‖≤ C*gear H.count u.length*gear H.count v.length:=by
   obtain ⟨C₁,h₁,H₁⟩:=spins h u hu; obtain ⟨C₂,h₂,H₂⟩:=spins h v hv; obtain ⟨C,hc,M⟩:= prices h; obtain ⟨A,ha,H₀⟩:=cap_g
   let P:= C₁*C₂*C; have hp : 0 ≤P:=by unfold P; positivity
   refine ⟨N^2 * P*A,by positivity,fun {c f} H D B {U X Q} h i j=>?_⟩
   let t:=P*gear H.count u.length*gear H.count v.length
   let g₁:= gear H.count u.length; let g₂:= gear H.count v.length; have hu:0≤g₁:= (gear_pos ..).le; have hv:0≤ g₂:=(gear_pos ..).le
   have ht:0 ≤ t:=by change 0 ≤ P*g₁*g₂; positivity
   let W(p:Site c):= (c.val:ℝ)⁻¹^4 / ‖tuning p‖
   rw [stage, fiberSum];
   calc
     _ ≤ ∑ p:Site c, ∑ y:Fiber,∑ x:Fiber, t* W p :=(norm_sum_le ..).trans (sum_le_sum fun p _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>(norm_sum_le ..).trans (sum_le_sum fun x _=>?_))) -- period
     _ ≤ N^2*t*A:=by
         refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (H₀ c) (by positivity : 0 ≤ N^2*t)); simp only [sum_const,card_univ,nsmul_eq_mul,Finset.mul_sum]; apply sum_congr rfl; intro i _; unfold W; ring
     _ = _ :=by unfold t; ring
   have hp':= (H₁ _ _ _ h i (p,x)).1; have hk':=(H₂ _ _ _ h j (p,y)).2; have hK:=QCD.Cost.north (rangeG B p) x y|>.trans (M B c p).2; rw [norm_mul,norm_mul,norm_star]; exact (mul_le_mul (mul_le_mul hp' hK (norm_nonneg _) ((norm_nonneg _).trans hp')) hk' (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hp') ((norm_nonneg _).trans hK))).trans_eq (by unfold t P W; ring)
end YM.QCD.Bank
#print axioms YM.QCD.Bank.spin_echo
