import YM.Lust.Price
import YM.Lust.Beam
/-! Choose a census witness. Keeping a true finite pitch but without extrapolating to the large-volume matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}
local notation "S"=> C.S
set_option quotPrecheck false
local notation "a" i:arg=> C.S.spacing (C.N i)
open CardsT
variable {P}
namespace GaugeP
variable {Z:Laurel d}(J:Landing P.sym Z)
variable (u:Averaging)
open Metric
variable (j:ℕ)(r:ℝ)(he:0 < r)
local notation "σ"=>  C.S.spacing j
local notation "b"=> bead (C.S.spacing j /r) J.a
include he
lemma mines (C:Sequence)(x:Cover) : digit (C.S.spacing j) x = r • Ibis.screen C.S j r x:=by unfold digit Ibis.screen Ibis.rescaling; rw[smul_smul]; field_simp
lemma runway (hB: 2*(C.S.spacing j/r) ≤ J.l)(hG:400*(C.S.spacing j/r) ≤ J.e): (Ibis.screen C.S j r (bead (C.S.spacing j/r) J.a)) ∈ Metric.closedBall J.a J.l ∧ J.e*r+400*σ ≤ ‖digit (C.S.spacing j) (bead (C.S.spacing j/r) J.a)‖:=by
    have hx: (Ibis.screen C.S j r b) ∈ Metric.closedBall J.a J.l:= (Metric.mem_closedBall.mpr ((smoothV (div_pos (space0 _ _) he) J.a).trans hB)); refine ⟨hx,?_⟩; let y:= Ibis.screen C.S j r b; have hy :2*J.e ≤ ‖y‖:= le_trans ((J.pose y hx).2.1 timeAxis) (le_trans (le_abs_self (y timeAxis)) (show |y timeAxis| ≤ ‖y‖ from (by rw[←Real.norm_eq_abs]; exact PiLp.norm_apply_le ..))); rw [mines j r he C,norm_smul,Real.norm_of_nonneg he.le]; rw [←mul_div_assoc] at hG -- name inspect
    nlinarith only [mul_le_mul_of_nonneg_left hy he.le,(div_le_iff₀ he).1 hG]
lemma census (A:ℝ)(hA:1 ≤A)(hB:2*(C.S.spacing j/r) ≤ J.l)(hG:400*(C.S.spacing j/r) ≤ J.e) (h:∀ᶠ i:ℕ in atTop,∃ g h: Stokes d→Label d,(∀ t,‖g t‖ ≤ A∧ ‖h t‖≤A)∧ ∀ x:Cover, (Ibis.screen C.S j r x) ∈ Metric.closedBall J.a J.l → nearG P.sym Z J.ε (fun t v:Stokes d=>let K:=ratioTo C.S (C.N i) j;(C.A i).regulator.average (CardsT.checkedT u K (stemV P d i u (g t)) 0 * CardsT.checkedT u K (stemV P d i u (h v)) x))): Nonempty (LensZ P Z J u):=by
      obtain ⟨N,hN⟩:= eventually_atTop.mp h; choose! g f hg h using hN; have hh:= runway J j r he hB hG
      exact ⟨g,f,A,zero_le_one.trans hA,eventually_atTop.mpr ⟨N,hg⟩,j,b,_,mul_pos J.far he, hh.2,eventually_atTop.mpr ⟨N,fun i hi=>h i hi b hh.1⟩⟩
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.census
