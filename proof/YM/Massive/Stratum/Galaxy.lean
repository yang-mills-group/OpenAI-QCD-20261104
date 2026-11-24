import YM.Massive.Stratum.Epoch
/-!
# Cumulative log ruler and affordability

Includes an estimate uniform **through arbitrarily long prefixes**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.AtlasH
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j:ℕ}{Q:Rock j}{J:Plan j}{p:ChartRatio su} (Y:AtlasH Q J p)
abbrev length (i:ℕ):= (Y.path i).L

def orbit (Y:AtlasH Q J p) : ℕ→Side
  | 0=>1
  | i+1=> Y.orbit i * (Y.length i)
abbrev ring (R:Side)(i:ℕ):= R*Y.orbit i
@[simp] lemma at_zero : Y.orbit 0=1:=rfl
theorem next (R:Side) (i:ℕ): (Y.ring R (i+1)).val=(Y.ring R i).val*(Y.length i).val:=by rw [ring,orbit,← mul_assoc,PNat.mul_coe]

def measure (i:ℕ):= Real.log ((Y.orbit i).val:ℝ)
abbrev scale (x:ℝ)(i:ℕ):= x+su.slopeConstant*Y.measure i
lemma origin_cost: Y.measure 0=0:=by simp[measure]
lemma era (i:ℕ): Y.measure (i+1)=Y.measure i+ Real.log ((Y.length i).val:ℝ):=by unfold measure; rw [orbit,PNat.mul_coe,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
lemma atBirth (x:ℝ): Y.scale x 0=x:=by simp[scale,Y.origin_cost]
lemma eras (x:ℝ) (i:ℕ):Y.scale x (i+1)= betaF su (Y.scale x i) (Y.length i):=by
   change _=_+_; unfold scale; rw [era]; ring
-- `x` + scale.clock
lemma bounded (i:ℕ):1≤(↑(Y.orbit i).val:ℝ):=by exact_mod_cast (Y.orbit i).pos
lemma per_len (i:ℕ):2 ≤(↑(Y.length i).val:ℝ):=by exact_mod_cast (show 2 ≤(Y.length i).val from (by have h:= (Y.path i).coarse; exact (show 2≤3 from by decide).trans h))
lemma measure_nn (i:ℕ):0 ≤ Y.measure i :=Real.log_nonneg (Y.bounded i)
lemma measure_strict:StrictMono Y.measure:=strictMono_nat_of_lt_succ (fun i=>by rw [era]; exact lt_add_of_pos_right _ (Real.log_pos (by linarith [Y.per_len i])))
lemma measure_pos (i:ℕ)(he:0< i):0<Y.measure i:= by rw [←origin_cost Y]; exact measure_strict Y he
private lemma unbounded : Tendsto (fun i=>Real.log ((Y.length i).val:ℝ)) atTop atTop:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp Y.free)
lemma ample (A:ℝ):∃ b:ℝ,∀ i:ℕ,A*(i:ℝ) ≤Y.measure i+b:=by
  obtain ⟨n,h⟩:= eventually_atTop.mp (Y.unbounded.eventually_ge_atTop |A|)
  refine ⟨|A| *(n:ℝ), fun i=>?_⟩
  have ht:= le_abs_self A
  induction i with
  | zero=> rw [Nat.cast_zero,Y.origin_cost,mul_zero]; positivity
  | succ i ih=>
      by_cases hh:n≤ i
      · rw [Nat.cast_add,Nat.cast_one,era]; linarith [h i hh]
      have hi:i+1 ≤ n:= lt_of_not_ge hh
      have hp: (↑(i+1):ℝ) ≤ (n:ℝ) := by exact_mod_cast hi
      exact (mul_le_mul ht hp (by positivity) (abs_nonneg _)).trans (le_add_of_nonneg_left (Y.measure_nn _))
lemma funds (A B:ℝ):∀ᶠ i:ℕ in atTop, A+B*(i:ℝ)≤Y.measure i:=by
  obtain ⟨b,h⟩:= ample Y (B+1); filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (A+b)] with i hi; linarith [h i]
lemma long : Tendsto Y.measure atTop atTop:=tendsto_atTop.2 fun A=> by simpa using Y.funds A 0
lemma outlay (A B:ℝ)(v:ℝ)(hv:0<v): ∀ᶠ i:ℕ in atTop,A+B*(i:ℝ)≤v*Y.measure i:=by
   filter_upwards [Y.funds (A/v) (B/v)] with i hi; apply (div_le_iff₀ hv).1 ?_ |>.trans_eq (mul_comm ..)
   rw [add_div,mul_div_right_comm]; exact hi
lemma freedom (A B:ℝ)(v:ℝ)(hv:0<v):∀ᶠ x:ℝ in atTop,∀ i:ℕ,A+B*(i:ℝ) ≤ x +v*Y.measure i:=by
  obtain ⟨b,h⟩:=ample Y (B/v);
  filter_upwards [eventually_ge_atTop (v*b+A)] with x hx i
  have hl:B*(i:ℝ) ≤(Y.measure i+b)*v:= ((div_le_iff₀ hv).1 (by rw [mul_div_right_comm]; exact h i))
  linarith
-- relative startup fee with any stride-dependent offset (eg $δ_G(L)$) can be requested at setup.
lemma funded (A B:ℝ):∀ᶠ x in atTop,∀ i:ℕ,A+B*(i:ℝ) ≤ Y.scale x i:= freedom Y A B _ (Gauge.slopeConstant_pos simple)
end YM.QCD.Acre.Stratum.AtlasH
#print axioms YM.QCD.Acre.Stratum.AtlasH.outlay
#print axioms YM.QCD.Acre.Stratum.AtlasH.freedom
