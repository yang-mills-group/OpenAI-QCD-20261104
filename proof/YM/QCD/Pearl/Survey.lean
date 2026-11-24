import YM.QCD.Pearl.Charge

/-!
# Cumulative-sign instrument: log polarization of actual endpoint Dirac paths on box
of spacing 1. UNIFORM in period and in every Dirac kernel in a supported radius class.
This is one-loop geometry, NOT a lattice running-coupling theorem. Includes irrelevant
non-flat curvature vertices with arbitrary fixed prices, no positivity assumption on those
modified Dirac matrices away from flat. Normalization mixed second derivative, full (not half),
divide by volume and physical continuum plaquette k^2. Use logdet after freezing gauge, sign (-).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch Pine Stationary
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p : Site n} {i : Axis} {κ η c s q b B r ε K a d D' : ℝ}{j:ℕ}{F : Momentum→Para}

def antenna (M : Weather n→Sheet n):ℝ:= testN M 0/(n.val^4 *beamH n^2 : ℝ)
def chargeF : ℝ := 3/(6*Real.pi^2)
lemma docket (C:su.Color)(hC:‖C‖=1) (P:Plan j)(hη:0<η) (a b c:ℝ): ∃ W:ℝ, ∀ᶠ n:Side in atTop,∀ (I J D:Type)(v:Train j)(G:I→Gleam)(U:J→Bloom 1)(V:D→Bloom 2),Package η a b c P v G U V →
    |antenna (extent C G U V n) - chargeF * Real.log n.val| ≤ W:=by
  obtain ⟨r,c₁,Z,Q⟩:= boot P.good; have hr:0<r:=(Q (Train.top j)).hr
  obtain ⟨Z₂,ZB⟩:= adder hr; let Y:=max Z Z₂; let u:=min c₁ 1
  have hu : 0<u:=lt_min (Q (Train.top j)).hc one_pos
  have hP : Pinch shaft r u Y:= ZB.reduce hr le_rfl hu (min_le_right ..) (le_max_right ..)
  obtain ⟨ε,hE,hL⟩:=hP.source ((η/2) / Real.pi) (by positivity)
  have hε:= (le_div_iff₀ Real.pi_pos).mp hL; have hy:=hE.seed
  let κ:= max (9/ε) 3
  have hk:3≤κ:=le_max_right ..; have hx :8<κ*ε:=by nlinarith [(div_le_iff₀ hy).mp (le_max_left (9/ε) (3:ℝ))]
  obtain ⟨z,w,HV⟩:= vertex C hη a b c
  let K:= |wobble2 r u Y η z w|
  obtain ⟨L,Lg⟩:= sweeping hk
  let C₀:ℝ:=(outPay ε K)*(8*(2*Real.pi^2))+960*(32*(2*Real.pi^2))+ ((κ+1)^4*(Real.pi^2/2))*(4*lowCost r u Y z w)+ upland ε K
  let D:=C₀+L+tuneBill κ 0; let f:ℝ:=(2*Real.pi)^4; let y:ℝ:= 2*Real.pi
  have hp:0<f:=by unfold f; positivity
  refine ⟨D/f+ |chargeF * Real.log y|,?_ ⟩
  filter_upwards [beam0.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),exhausting.eventually_ge_atTop 4, beam0.eventually (gt_mem_nhds zone_pos), beam0.eventually (gt_mem_nhds (div_pos (show (0:ℝ)<1/4 by norm_num) (show 0<κ+1 by linarith)))] with n h1 h2 h3 h4 I J J' v G U V h
  have hn:4≤n.val:=h2; have ht : beamH n<1/4:= h1
  let A:=v₁ G U C 1; let X:=v₂ G U V C 1
  obtain ⟨hW,hZ⟩:=HV I J J' G U V (packBill h) 1; let M:=extent C G U V n; have hb:=gun C hn h3 h
  let t:= beamH n; let g:= shock A X (Dir v) (n:=n); let T:= fans (midst n κ); have ht':0<t:=beamP n
  have hX : |(∑ i,g i)- ∑ i∈midst n κ,t^4*windward (centerZ i)|≤ C₀:= wales C hC hn ht h3 hk (at_sea C h _) ((Q v).reduce hr le_rfl hu (min_le_left ..) (le_max_left ..)) hP hE hη hW hZ hε hx (by rfl)
  have hh:= missing (κ:=κ) ht hk (by rw [mul_comm (κ+1)]; exact (le_div_iff₀ (by linarith : 0<κ+1)).mp (show beamH n<1/4/(κ+1) from h4).le)
  have hY : ∑ i,g i=t^2*testN M 0:=by unfold g shock; rw [← Finset.mul_sum,← hb]; change t^4/(2*t^2)*_= _; field_simp; ring
  have hQ : |t^2*testN M 0 -4*(2*Real.pi^2*Real.log t⁻¹)|≤ D:= by
    rw [← hY]
    refine (abs_sub_le _ (∫ x in T,windward x) _).trans (add_le_add ?_ ?_)
    · exact (abs_sub_le _ _ _).trans (add_le_add hX (Lg n ht.le))
    rw [abs_sub_comm]; exact hh
  have hi : Real.log t⁻¹=Real.log n.val-Real.log y:=by
    unfold t beamH y; have hp:0<2*Real.pi:=by positivity
    rw [Real.log_inv, Real.log_div hp.ne' (side_pos n).ne',neg_sub]
  change |antenna M- _| ≤ _
  apply (abs_sub_le _ (chargeF*(Real.log t⁻¹)) _).trans; refine add_le_add ?_ ?_
  · have hm : antenna M *f=t^2*testN M 0:=by
      unfold antenna
      have ht : (n.val:ℝ)^4*t^4=f:=by simpa only [site_card,Nat.cast_pow] using! oceanCount n
      rw [← ht]; change testN M 0/ ((n.val:ℝ)^4*t^2)*_= _; field_simp
    have hM : chargeF *Real.log t⁻¹*f=4*(2*Real.pi^2* Real.log t⁻¹):=by unfold f chargeF; field_simp; ring
    rw [le_div_iff₀ hp,← abs_of_nonneg hp.le, ← abs_mul] -- risks rewrites f
    rw [sub_mul,hm,hM]; exact hQ -- inspect
  rw [hi,mul_sub,sub_right_comm,sub_self,zero_sub, abs_neg]
end YM.QCD.Pearl
