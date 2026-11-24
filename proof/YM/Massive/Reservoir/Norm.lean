import YM.Massive.Reservoir.Prior

/-! Variant sup chess estimate with integrated normalized Pixel budget.
This way strong when pressure estimates on norms keep the tree volumes.
Adapted from `YM/QCD/Plum/Fable`. -/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Plum.Bank
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
variable (hp:Healing J X)(he:Continuous X)(hv:Cvol X=1)(h: Even c.val)(hN:4≤c.val)

abbrev Stated (X:Pixel c F):= ∫ U,‖X U‖ ∂prior su c
lemma sheer (b:ℝ)(hT:Stated X ≤ b)(x:Stud c F)(hw:WithinP w x)(he:Continuous X): ‖Tide.fresh X x‖≤ b*w:=by
   unfold Tide.fresh; refine (norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const (μ:=prior su c) w) (Eventually.of_forall fun U=>?_)).trans ?_
   · exact (Grass.price _).trans ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (hw U) (norm_nonneg _)))
   rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hT hw.nonneg
local notation "d"=> longM J
variable {r:ℕ}
include hp he hv h hN
lemma planetary (p:Site c)(he':r+2*d ≤ c.val) (x:Stud c F)(H:Fence (RP.square p fun _=>r) x)(hx:WithinP w x)(A:ℝ)(hU:Stated X ≤ Globe.expo A c) : ‖Tide.fresh X x‖ ≤ quota J r A * w:=by
    let Q:= r+2*d; have hQ:0<Q:=by unfold Q; change 0<r+2*(40*(J.J+3)); omega
    obtain ⟨m,hM,hk⟩:∃ m:ℕ,2^m*Q ≤ c.val ∧ c.val< 2^(m+1)*Q:=by
        let m:= Nat.log 2 (c.val / Q)
        have hp:2^m ≤ c.val / Q:=Nat.pow_log_le_self 2 (by have hv:c.val / Q ≥ 1:= (Nat.le_div_iff_mul_le hQ).2 (by simpa using he'); omega)
        refine ⟨m,(Nat.le_div_iff_mul_le hQ).1 hp,?_⟩; by_contra! he; exact Nat.not_lt_of_ge ((Nat.le_div_iff_mul_le hQ).2 he) (Nat.lt_pow_succ_log_self (by norm_num) _)
    obtain ⟨y,Y,hw,hY⟩:= quadrant hp he hv h hN hM p x H hx
    have hx':0≤ w:= hx.nonneg; apply le_of_pow_le_pow_left₀ (show ((2^m)^4:ℕ) ≠ 0 by positivity) (mul_nonneg (Real.exp_pos _).le hx'); apply (hY.trans (sheer _ hU y hw he)).trans; rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold Globe.expo; rw [← Real.exp_nat_mul,Real.exp_le_exp,site_card];
    have he : (c.val:ℝ) ≤ (2:ℝ)^m * ↑(2*Q) := by rw [pow_succ, mul_assoc] at hk; exact_mod_cast hk.le
    change -(↑(c.val^4):ℝ)*A ≤ ↑((2^m)^4:ℕ)*(|A| * (↑(2*Q):ℝ)^4); have hp:= pow_le_pow_left₀ (Nat.cast_nonneg _) he 4; rw [mul_pow] at hp; push_cast at *; nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs A) (show 0≤ (c.val:ℝ)^4 by positivity),mul_le_mul_of_nonneg_right hp (abs_nonneg A)]

end YM.QCD.Plum.Bank
#print axioms YM.QCD.Plum.Bank.planetary
