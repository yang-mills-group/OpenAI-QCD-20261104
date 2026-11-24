import YM.QCD.Oasis.Gold
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Purple
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Jets.Touch
variable {L:Side}{a b u v t σ C m l r q:ℝ}{f h g p:ℝ→ℝ}
lemma forego (V:ChartPrices)(h : 0 < a)(hV:0<V.gap)(he: 0<b)(ht:b<1)(hx:0<v)(hp:v<b): Tame L fun i=>barley V (wick su L a i) (arcT L b i)*Real.exp (fan L v i):=by
   let Z i:= Real.exp (fan L v i)
   have hv :Seat L v (fun i=>fan L v i):=Seat.keeps
   have hh:= joyP hv zero_lt_one he hp
   let F t:= wick su L a t; let q:= V.gap*a^2/8; have hq:0<q:=by unfold q; positivity
   have hs (i): - (V.gap*(F i)^2/4)/2= -q*fan L 2 i:=by unfold q F wick fan pra; rw [Real.rpow_two]; ring
   have hF := joyP hv hq (show (0:ℝ) < 2 by norm_num) (lt_trans (hp.trans ht) (by norm_num)); intro i; refine (((hh i).mul_right (Real.exp 1)).add (hF i)).congr (Eventually.of_forall fun y=> ?_); unfold barley arcT; change ( _+ Real.exp (-(V.gap*(F y)^2/4)/2))*Real.exp _=_; rw [hs]; ring
lemma swellA (K: KernelChoices)(L:Side)(j:ℕ)(Z z I:ℝ) (hv:Bolt su L f)(h:Rate su L u g)(hp:Rate su L v p): ∃ r:ℝ,Rate su L r (fun i=> Awe j (prime su K j Z z (2*betaF su i L) (f i)) (p i) I (g i)):=by
    unfold Awe; have h' := primeR (G:=su) f K (n:=j) (Z:=Z) (a:=z) hv.uses
    exact ⟨_, (Rate.mul (climbF h' (by positivity) j I) (Rate.mul h' ((h.mul_right _).mul hp))).mul_right _⟩
lemma ennA (j:ℕ)(A s v:ℝ)(h:0≤a)(hp:a≤b)(hv:0≤A)(he:0 ≤v)(hs:0 ≤ s): Awe j a v A s ≤ Awe j b v A s:=by
    unfold Awe; have hr:= rising j h hp hv; apply mul_le_mul_of_nonneg_right _ (by positivity); apply mul_le_mul hr (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity); unfold clump; have hx:= h.trans hp; positivity
lemma brimmingP (H m:ℝ)(l:ℕ)(L:Side):∃ V:ℝ, ∀ᶠ x in atTop,Assim su L l x (betaF su x L^H) (betaF su x L^V) (betaF su x L^m):=by
    obtain ⟨B,h⟩:= Lantern.iteration su L l (m:=m) (d:=H) zero_lt_one; exact ⟨B,h⟩
def brass (L:Side)(x v:ℝ):ℝ:= (betaF su x L)⁻¹ * fan L v x
lemma arctic (θ:ℝ)(h:Seat L a f)(hx:a<θ):∀ᶠ x in atTop, ∀ β:ℝ, betaF su x L/2≤β → (betaF su x L)^(- (2:ℝ)) + (gStep β)^2*f x ≤ brass L x θ :=by
    let g i:= betaF su i L^(- (1:ℝ)); have hh:=((Seat.eliminated (f:=g) Rate.power (by norm_num) (b:=a)).comb (h.compares (g:=fun i=>|f i|) (Eventually.of_forall fun i=>(abs_abs _).le) |>.timesL 2)) _ hx
    filter_upwards [hh,Delay.shift_pos su L] with x h ht β hb; have hβ:0<β:=(half_pos ht).trans_le hb
    have hy : gStep β^2 ≤ 2*(betaF su x L)⁻¹:=by
       rw [←div_eq_mul_inv, le_div_iff₀ ht]; nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg (gStep β)), (Fare.gS _ hβ).2]
    have h₁: g x+2*|f x|≤fan L θ x:=(le_abs_self _).trans h; simp only [g,Real.rpow_neg ht.le,Real.rpow_one] at h₁
    unfold brass; simp only [Real.rpow_neg ht.le,Real.rpow_two,←inv_pow]; calc
      _ ≤ _+2*(betaF su x L)⁻¹*|f x|:= add_le_add le_rfl ((mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right hy (abs_nonneg _)))
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left h₁ (inv_pos.mpr ht).le]
lemma quaint (L:Side)(h: Rate su L a f)(ht : a <0): ∀ᶠ x in atTop, f x≤1:=by filter_upwards [h.below ht 1 zero_lt_one] with x h using (le_abs_self _).trans h
end YM.QCD.Oasis
