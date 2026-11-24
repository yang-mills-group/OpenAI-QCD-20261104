import YM.Next.ROTATIONS.Charge
import YM.Gust.Cav.OSwitch
/- Variant of YM.Next.ROTATIONS.Charge, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Set Function Filter MeasureTheory Measure Row Boundary Probe OS Word Nodes
open scoped Topology NNReal ENNReal ContDiff BigOperators
lemma runs_order {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i) (H : S.Hierarchy)
    (A : Weight L) (hA : Pressed i A) : ∃ M : ℕ, ∀ m : ℕ,M ≤ m → ∀ (s : ℝ), 0<s → ∀ f : Profile, Ends f → Reflects false f →
        Runs (ν V A) i 1 (stamp (Resid m s f)) := by
  obtain ⟨D,hD⟩ := runs_point V H A hA
  refine ⟨D,fun m hm s hs f hf hl => hD _ (centred_hollow _ D ?_) _ (by norm_num)⟩
  exact fun i hi => correct m s hs f hf hl i (by omega)
variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)
/-- Alternative cost with any high transverse axis moment. `z` turned into cap
before paying its band. -/
lemma far_pay (A : Weight L) (h : ℕ → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p) (K : ℝ)
    (hj : ∀ j∈Q, -K ≤ w j) (j : Axis) (hi : j∈Q) (he : j≠i) (k : ℕ) (a : ℝ)
    (hp : ∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (h n) p * ‖p j‖^(2*k)) (ν V A))
    (ht : Budget a (fun n => ∫ p : E4, Reel i (h n) p * ‖p j‖^(2*k) ∂ν V A))
    (g : Profile) (hg : Far g) (u : ℝ) (hu : 0≤u) :
    Budget (-u*(2*k:ℕ)+K*((Q.erase i).erase j).card+a)
      (fun n => pay (ν V A) i Q (h n) (update (mails w f n) j (bill u n g))) := by
  obtain ⟨C,hC,hG⟩ := far_gain u hu k g hg
  let x : ℝ := -u*(2*k:ℕ)
  let T := (Q.erase i).erase j
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  let y := K*T.card
  apply ((((budget_fuel x).times C).prod ((budget_fuel y).times M)).prod ht).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  let μ := ν V A
  let R (p : E4) := Reel i (h n) p * ‖p j‖^(2*k)
  let W := (C*fuel x n)*(M*fuel y n)
  change _ ≤ W * integral μ R
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul W) ?_
  filter_upwards [before V A] with p hp
  rw [crop_cons (Q.erase i) _ j _ _ (Finset.mem_erase.mpr ⟨he,hi⟩),norm_mul,norm_mul,Real.norm_of_nonneg (hn p hp)]
  have hb : ‖crop T (mails w f n) p‖ ≤ M*fuel y n := sum_cash w f K n T (fun i hi => hj i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) p
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hG n _) hb (norm_nonneg _) ((hG n _).trans' (norm_nonneg _))) (hn p hp)) (le_of_eq ?_)
  dsimp only [W,x,R]; ring
lemma done_pay (A : Weight L) (h : ℕ → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p)
    (hj : ∀ j∈Q,0≤w j) (a : ℝ) (hp : ∀ᶠ n in atTop, Integrable (Reel i (h n)) (ν V A))
    (ht : Budget a (fun n => ∫ p : E4, Reel i (h n) p ∂ν V A)) :
    Budget a (fun n => pay (ν V A) i Q (h n) (mails w f n)) := by
  let T := Q.erase i
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  apply (ht.times M).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  change _ ≤ M * integral (ν V A) (Reel i (h n))
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul M) ?_
  filter_upwards [before V A] with p hp
  rw [norm_mul, Real.norm_of_nonneg (hn p hp),mul_comm M]
  refine mul_le_mul_of_nonneg_left ?_ (hn p hp)
  have h : ∀ j∈T,-(0:ℝ)≤ w j := by simp_rw [neg_zero]; exact fun j h => hj j (Finset.mem_of_mem_erase h)
  simpa only [zero_mul,fuel0,mul_one] using sum_cash w f 0 n T h p
lemma accounts (H : S.Hierarchy) (A : Weight L) (h : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, ∀ (x d a : ℝ) (_ : 0 ≤ d) (_ : 1≤ a) (f : Profile), Ends f → Plus f →
    (∀ᶠ n in atTop, Room (bill x n f) (a*fuel d n)) → ∀ m : ℕ, D ≤ m →
    (∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (lamps m x d a f n) p * ‖p j‖^(2*k)) (ν V A)) ∧
    Budget (max (-x) (d*D)) (fun n => ∫ p : E4, Reel i (lamps m x d a f n) p * ‖p j‖^(2*k) ∂ν V A) := by
  obtain ⟨D,hD⟩ := surface V H A h j hj k
  refine ⟨D,fun x d a hd ha f hf hp hR m hm => ?_⟩
  obtain ⟨C,hC,ht⟩ := hD m (by omega) f hf hp
  have hx n : 1 ≤ a*fuel d n := one_le_mul_of_one_le_of_one_le ha (by simpa only [fuel0] using fuel_le hd n)
  constructor
  · filter_upwards [hR] with n hh; exact (ht _ (hx n) _ (fuel_pos ..) hh).1
  apply ((((budget_inv x).rise (le_max_left ..)).add ((((budget_fuel d).times a).pow D).rise (le_max_right ..))).times C).signed
  · filter_upwards [hR] with n hr
    refine integral_nonneg_of_ae ?_
    filter_upwards [before V A] with p hu
    exact mul_nonneg (lamp_signs m x d a f hf hp n (by linarith) hr i p hu) (pow_nonneg (norm_nonneg _) _)
  filter_upwards [hR] with n hh
  exact (ht _ (hx n) _ (fuel_pos ..) hh).2
end YM.Spiral.Outer

