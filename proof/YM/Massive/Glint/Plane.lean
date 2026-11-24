import YM.Massive.Mass.Plane
/-! Per-flavor estimates without Fit requirement; from `Mass/Plane.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Reading
open QCD QCD.Lat Lattice Wilson Function QCD.Grass QCD.Stew QCD.Globe QCD.Globe.HalfMass
open QCD.Flume QCD.Cove QCD.Finch QCD.Reggae -- Phase namespace?
open High.PrismT Project YM.Next.Free
open Filter Finset
open scoped Topology ContDiff Classical Matrix BigOperators Matrix.Norms.L2Operator
variable {c : Side} {A ε : ℝ} {j k N m : ℕ} (X : Sheet c)

lemma actual_plane (X:Grid c → EvenA c N) (b:Flavor N) :
    planeProbe (light _ ∘ X) b= (↑(Fintype.card Lat.Fiber):ℂ)⁻¹ * ∑ i,center (fumes b (X 1)) (fun i j=>star (Run.plane i)*Run.plane j) i i:=by
   simp_rw [planeProbe,quadr b X];
   let A (x y: Site c)(v:Lat.Fiber):= (star (Run.plane x)*Run.plane y)* (fumes b (X 1) (x,v) (y,v));
   have hh : ∑ x,∑ y,∑ v:Lat.Fiber, star (Run.plane x) * fumes b (X 1) (x,v) (y,v)* Run.plane y= ∑ v,∑ x:Site c,∑ y:Site c,A x y v:=by
      rw [sum_comm (f:=fun v x=>∑ y,A x y v)]; apply sum_congr rfl; intro x _; rw [sum_comm (f:=fun v y=>A x y v)]; unfold A; congr 1; ext1 y; apply sum_congr rfl; intro i _; ring -- check
   rw [hh]; simp only [div_eq_mul_inv,mul_inv_rev,center, cashRow, Matrix.smul_apply, Matrix.sum_apply,smul_eq_mul]; rw [← mul_sum]; let q:=∑ i, ∑ x, ∑ y:Site c,A x y i; change q*((↑(_:ℕ):ℂ)⁻¹ * (↑(_:ℕ):ℂ)⁻¹) = _*(_*q); ring


theorem own_plane (X : Grid c → EvenA c N) (b : Flavor N) (K : Sheet c)(he : K=fumes b (X 1))
    (hT : Tempo K)(hp: Beam K m A) (hv:1 ≤ m) : amount c * ‖planeProbe (light _ ∘ X) b - (Project.unitF false c K:ℂ)‖ ≤ (budget+40)*A:=by
  let u:= unitF false c K; let k := Fintype.card Lat.Fiber; let w : Site c→Site c→ℂ :=fun i j=> star (Run.plane i)*Run.plane j
  have hQ :0 ≤ budget:=by unfold budget; positivity
  have hc:0≤amount c:=Nat.cast_nonneg _
  have hl (i): amount c*‖center K w i i-(u:ℂ)‖ ≤ (budget+40)*A:=by
        let z:ℂ:= mass K; rw [show _- (u:ℂ)= (center K w i i-z)+ (z-u) from (by abel)]
        apply le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) hc); rw [mul_add]; apply le_trans (add_le_add (coat K w hv hQ closeRe hp hT i) ?_) (b:=(budget+20)*A + 20*A)
        swap
        · refine le_trans (b:=amount c*|u-mass K|) (le_of_eq (by rw [norm_sub_rev,show (u:ℂ)-z= (↑(u-mass K):ℂ) from (Complex.ofReal_sub ..).symm, Complex.norm_real,Real.norm_eq_abs])) (read_toll K hv hp hT)
        linarith
  rw [actual_plane X b, ← he]; let F(i:Lat.Fiber):= center K w i i-(u:ℂ);
  have hr:0<(k:ℝ):=by unfold k; positivity
  change _ * ‖(k:ℂ)⁻¹ * (∑ i,center K w i i) - (u:ℂ)‖ ≤ _
  rw [show (k:ℂ)⁻¹*(∑ i, center K w i i)-(u:ℂ) = (k:ℂ)⁻¹ * ∑ i,F i from ?_, norm_mul,norm_inv,Complex.norm_natCast,mul_left_comm (amount c),inv_mul_eq_div];
  · apply (div_le_iff₀ hr).mpr; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) hc); rw [mul_sum]; apply (sum_le_sum fun i _=> hl i).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_comm ..
  unfold F; have ht:(k:ℂ)≠0:=by unfold k; exact_mod_cast Fintype.card_ne_zero (α:=Lat.Fiber)
  rw [sum_sub_distrib,sum_const, card_univ,nsmul_eq_mul,mul_sub,inv_mul_cancel_left₀ ht]

lemma sky_flag (X:Grid c→ EvenA c N)(b:Flavor N)(K:Sheet c)(hK:K=fumes b (X 1))(h:Tempo K)(hp: Beam K m A)(hm:1 ≤ m): amount c*‖planeProbe (light _ ∘ X) b - (flagW K:ℂ)‖ ≤(2*budget+80)*A:=by
   let u:= Project.unitF false c K; let x:=planeProbe (light _ ∘ X) b; let m':= mass K; let f:= flagW K; have he : |u-f|≤|u-m'|+|f-m'|:=by rw [abs_sub_comm f]; exact abs_sub_le ..
   have ht : 0 ≤ amount c := Nat.cast_nonneg (α:=ℝ) c.val; have hv : amount c*|u-f|≤20*A+(budget+20)*A:=by apply (mul_le_mul_of_nonneg_left he ht).trans; rw [mul_add]; exact add_le_add (read_toll _ hm hp h) (read_flag _ hm hp h)
   change _ * ‖x- ↑f‖ ≤ _; rw [show x-(f:ℂ)=x-↑u+(↑(u-f):ℂ) from (by push_cast; abel)]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) ht).trans; rw [Complex.norm_real,mul_add]; linarith only [show amount c*‖x-(u:ℂ)‖≤ (budget+40)*A from own_plane X b K hK h hp hm, (show amount c*‖u-f‖ ≤ _ from hv)]
end YM.Massive.Reading
#print axioms YM.Massive.Reading.own_plane

#print axioms YM.Massive.Reading.sky_flag
