import YM.QCD.Jets.Mark
/-! # unforced main inheritance budget, grants. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{L:Side} {x u v a b c ν C D T θ: ℝ} {i j:ℕ}{f g: ℝ→ℝ}

def chip (L:Side)(x : ℝ):ℝ:= (betaF su x L)⁻¹ * pra L x
def rust (L:Side)(θ x : ℝ):ℝ:= ((fan L θ x)^2)⁻¹
def cashM (L:Side)(θ x:ℝ):= rust L θ x * (chip L x)⁻¹

def taxK (L:Side)(x p:ℝ):ℝ:= Real.exp (p *fan L (1/3) x)

lemma healthy_chip (hp:0 < betaF su x L):0 < chip L x:=mul_pos (inv_pos.mpr hp) (Delay.monitor_pos ..)
lemma chip_rate (L:Side): Rate su L (-1) (chip L):=by
   have h : Rate su L (-1) (fun x=> (betaF su x L)⁻¹):= Rate.power.congr ((Delay.shift_pos su L).mono fun x hx=>by simp only [Real.rpow_neg hx.le,Real.rpow_one,le_refl])
   have hh:=h.mul (Rate.monitor); rw [add_zero] at hh; exact hh
lemma top_chip (L:Side):Rate su L 1 (fun x=>(chip L x)⁻¹):= by
   have h :Seat L (-1) (fun x=>(pra L x)⁻¹):=by simpa only [fan,Real.rpow_one] using skin_i L 1
   have hg:=Rate.mul (Rate.hat (G:=su) (L:=L)) h.ruled; rw [add_zero] at hg; refine hg.congr (Eventually.of_forall fun i=>?_); simp [chip,mul_comm]

lemma chip_r (L:Side)(θ:ℝ):Seat L (-2*θ) (rust L θ):=by
   have h:= (skin_i L θ).powered 2; push_cast at h
   apply (h.above (by linarith)).equal
   exact Eventually.of_forall fun i=> by simp [rust]
lemma cash_r (L:Side)(θ : ℝ): Rate su L 1 (cashM L θ):=by have hg:=(chip_r L θ).ruled.mul (top_chip L); rw [zero_add] at hg; exact hg
lemma rust_inv (L: Side)(θ :ℝ):Rate su L 0 (fun x=>(rust L θ x)⁻¹):=by
   have h := (Rate.rpow_monitor (L:=L) (G:=su) θ).pow 2; rw [zero_mul] at h
   apply h.congr (Eventually.of_forall fun i=>?_); simp [rust]
lemma cash_h (L:Side)(θ : ℝ) : Rate su L (-1) (fun x=>(cashM L θ x)⁻¹):=by
   have hv:= (rust_inv L θ).mul (chip_rate L); rw [zero_add] at hv
   apply hv.congr (Eventually.of_forall fun i=>?_); simp [cashM,mul_comm]
lemma event_chip (L: Side)(θ:ℝ): ∀ᶠ x in atTop,0<betaF su x L ∧ 0<chip L x∧chip L x≤1 ∧ 1≤cashM L θ x:=by
 filter_upwards [Delay.shift_pos su L,(chip_rate L).below (by norm_num) 1 zero_lt_one,(cash_h L θ).below (by norm_num) 1 zero_lt_one] with x hp ht hx
 have he:=healthy_chip hp; have hg : 0<cashM L θ x := by unfold cashM rust; have := fan_pos L θ x; positivity
 exact ⟨hp,he,(le_abs_self _).trans ht,(one_div_le_one_div hg zero_lt_one).mp (by simpa only [abs_of_nonneg (inv_pos.mpr hg).le,one_div,inv_one] using hx)⟩

lemma couplings (L:Side) {p:ℝ}(h:0<p): Rate su L a (fun x=>(taxK L x p)⁻¹):= by
   have hh: Rate su L a (fun x=> Real.exp (-p*(fan L (1/3) x))):= Rate.monitor_cutoff h (by norm_num)
   apply hh.congr (Eventually.of_forall fun i=>?_); simp [neg_mul,taxK,Real.exp_neg]
lemma upperTax (L: Side) (T:ℝ) (h:0<T)(f:ℝ→ℝ)(a:ℝ)(hv: Rate su L a f):∀ᶠ x in atTop,f x ≤ taxK L x T:=by
   have hf : Rate su L (-1) (fun x=> f x*(taxK L x T)⁻¹):=by simpa only [show a+(-1-a)=-1 by ring] using hv.mul (couplings (a:=-1-a) L h)
   filter_upwards [hf.below (by norm_num) 1 zero_lt_one] with x hx
   have hp:= (le_abs_self _).trans hx; rw [← div_eq_mul_inv] at hp; exact (div_le_one (show 0<taxK L x T from Real.exp_pos _)).mp hp
lemma minnow (L:Side)(F:ℕ)(A B:ℝ):Seat L 0 (fun x=>A*Cove.kappa (radiusB x+1) F):=by
   unfold kappa; simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
   apply Seat.timesL; apply Seat.times; apply Seat.times; apply Seat.timesL
   have hh:= (Seat.radius (L:=L)).comb (Seat.numbers 1)
   simpa only [zero_mul] using (((hh.comb hh).comb (Seat.numbers 1)).powered 4)
lemma zealous (L:Side)(F:ℕ) (C:ℝ)(hc:0<C): ∀ᶠ x in atTop,C^(Cove.kappa (radiusB x + 1) F) ≤ taxK L x (1/4):=by
   have hp :=Seat.timesL (minnow L F (Real.log C) 0) 4
   filter_upwards [hp ((1:ℝ)/3) (by norm_num)] with x h
   have he:C^(Cove.kappa (radiusB x+1) F)=Real.exp ((Real.log C)*Cove.kappa (radiusB x+1) F):=by rw [show _ * (Cove.kappa (radiusB x+1) F:ℝ)=(Cove.kappa (radiusB x+1) F:ℝ) * Real.log C from mul_comm ..,Real.exp_nat_mul,Real.exp_log hc]
   rw [he,taxK,Real.exp_le_exp]; have hf:= (le_abs_self _).trans h; unfold fan; linarith
lemma toll (L:Side)(θ : ℝ)(F:ℕ)(C :ℝ)(hc:0<C):∀ᶠ x in atTop, ∀ d : ℕ,0<d→
    cashM L θ x * taxK L x (1/2)^d*C^(Cove.kappa (radiusB x +1) F*d) ≤ rust L θ x *taxK L x 1^d:=by
  filter_upwards [zealous L F C hc,upperTax L (1/4) (by norm_num) _ _ (top_chip L), Delay.shift_pos su L] with x hx h H d hd
  let P p:= taxK L x p; have he i:0 < P i:= Real.exp_pos _
  have hi:1 ≤ P (1/4):= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
  have hz:=healthy_chip H
  unfold cashM; rw [mul_assoc (rust L θ x), mul_assoc (rust L θ x)]; apply mul_le_mul_of_nonneg_left _ (by unfold rust; positivity)
  rw [pow_mul]; apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right (h.trans (le_self_pow₀ hi hd.ne')) (pow_nonneg (he _).le _)) (pow_le_pow_left₀ (pow_nonneg hc.le _) hx _) (pow_nonneg (pow_nonneg hc.le _) _) (mul_nonneg (pow_nonneg (he _).le _) (pow_nonneg (he _).le _))) -- check le_self_pow0
  change P (1/4)^d*P (1/2)^d *P (1/4)^d ≤ P 1 ^ d; rw [← mul_pow,← mul_pow,show P _ * P _*P _ = P 1 from ?_] -- binder ambiguous
  unfold P taxK; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
end YM.QCD.Jets.Touch
