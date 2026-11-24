import YM.Needle.Mind
/-! Universal placement clips. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag
open Finset
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Rᴮ" i:arg => (C.A i).regulator
local notation "B" i:arg=> C.S.side (C.R i) (C.N i)
noncomputable def digit (w:ℝ) (x:Cover):E4:=w • vector x
@[simp] lemma digit_zero (w:ℝ):digit w 0=0:=by unfold digit; simp [show vector 0=0 from by ext a; simp [vector]]
lemma digit_plus (w:ℝ)(x y:Cover):digit w (x+y)=digit w x+digit w y:=by ext a; simp [digit,vector]; ring
lemma digit_neg (w:ℝ)(x:Cover):digit w (-x)=-digit w x:=by ext a; simp [digit,vector]
noncomputable def bead (w:ℝ) (x:E4):Cover:=fun i:Axis=>⌊x i/w⌋
variable {k:ℝ}(hw:0 < k)
include hw
lemma smoothV (x:E4):dist (digit k (bead k x)) x ≤2*k:=by
    rw [dist_eq_norm]; let z:= digit k (bead k x)-x
    have hx (i:Axis): ‖z i‖ ≤ k:=by
         let y:=bead k x; change ‖k*(↑(y i):ℝ)-x i‖≤k; have h:= Int.lt_floor_add_one (x i/k); have hm : (↑(y i):ℝ)*k ≤ x i :=(le_div_iff₀ hw).1 (Int.floor_le _); change x i/k < ↑(y i)+1 at h; rw [div_lt_iff₀ hw] at h; rw [Real.norm_eq_abs,abs_le]; constructor<;> nlinarith
    have hh:‖z‖^2 ≤(2*k)^2:=by rw [PiLp.norm_sq_eq_of_L2]; exact (Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hx i) 2)).trans_eq (by simp[Axis]; ring)
    exact le_of_pow_le_pow_left₀ (by decide) (by linarith) hh -- n binder fix
omit hw
variable {β ν:ℝ}(hC:C.Path β ν)
local notation "a" i:arg=> C.S.spacing (C.N i)
open YM.Bloom YM.Bloom.Jar YM.Bank YM.Bank.Jule
lemma presenting (w:ℝ) (x:Cover): digit w x = posT w⁻¹ 1 x:=by unfold posT digit; rw [pow_one, inv_inv]; rfl
include hC
lemma approaches (x:E4): Tendsto (fun i=>digit (C.S.spacing (C.N i)) (bead (C.S.spacing (C.N i)) x)) atTop (𝓝 x):=by
   have hh:= tendsto_nhds_of_tendsto_nhdsWithin hC.physical
   have h:Tendsto (fun i=>2*a i) atTop (𝓝 0):=by simpa only [mul_zero] using hh.const_mul 2
   refine Metric.tendsto_nhds.mpr fun ε he=>?_ ; filter_upwards [h.eventually_lt_const he] with i hi; exact lt_of_le_of_lt (smoothV (space0 _ _) _) hi
lemma fullPrice (X v:ℝ):∀ᶠ i:ℕ in atTop,∀ x y:Cover,X ≤ dist (digit (a i) x) (digit (a i) y) → dist (digit (a i) x) (digit (a i) y)≤v → X/2 ≤ (C.S.spacing (C.N i))* separation (wrap _ x) (wrap (C.S.side (C.R i) (C.N i)) y):=by
     have h:= (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp hC.infinite) -- args
     filter_upwards [h.eventually (eventually_gt_atTop (2*v))] with i hx x y hp hY
     let V:= posT (a i)⁻¹ 1; have hw:0 < a i:=space0 _ _; have hm : V x-V y∈ Oasis X v:=disc (by simpa only [dist_eq_norm, presenting] using hp) (by simpa only [dist_eq_norm, presenting] using hY)
     have hU : 2 * (v*((a i)⁻¹^1)) < (((B i).val):ℝ):=by
          change (2:ℝ)*(v*((C.S.spacing (C.N i))⁻¹^1)) < ↑((C.S.side (C.R i) (C.N i)).val); unfold Scheme.spacing Scheme.side; rw [pow_one,inv_inv,PNat.mul_coe, Nat.cast_mul, ←mul_assoc]; exact mul_lt_mul_of_pos_right hx (by positivity)
     have ht:= (Consent.rootV x y _ 1 (inv_pos.mpr hw) X v hm hU).1; rw[pow_one,← div_eq_mul_inv,div_le_iff₀ hw] at ht; linarith only [ht]
end YM.Massive.Needle
#print axioms YM.Massive.Needle.approaches
#print axioms YM.Massive.Needle.fullPrice
