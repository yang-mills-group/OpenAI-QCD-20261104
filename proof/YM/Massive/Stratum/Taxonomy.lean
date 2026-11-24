import YM.QCD.Garden.Temple

/-!
# Geometric restoration at stride changes

Widening at the coarse end of a step (relative widths, by a dilation
factor) is needed, not just permission to start paying at narrower widths.
Actual prices of the inherited spin pages, adapted from the
same-width proofs `Trophy` and `Shrine`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m:ℕ} {P:Flight j k}{D E:Bed}{Z:Towers P.L}{I:Type}{W:I→Bloom m}
lemma panGreater (η Ω Θ : ℝ) (hη:0<η) (hj:4≤j)(hk:4≤k) (m:ℕ) (hh:0<m) (hm:0≤Ω)(hM:0≤Θ):
    ∃ δ c:ℝ,0<δ∧0≤c ∧ ∀ (σ ρ C:ℝ) (P:Flight j k)(_ : 0<σ)(_:0<ρ) (_:ρ≤δ)(I:Type)(W:I→Bloom m)(D E:Bed)(Z:Towers P.L)(s:ℕ),
    ρ*(1+(m:ℝ)) ≤ σ*P.L.val →1 ≤ s → D.dual_diag.strip η Ω → E.diagonal.strip η Θ → Z.Deep η Ω s → Fractal W σ C →
     (∃ y:ℝ, Fractal (tray P (psi D E Z) W) (ρ*(1+m)) y) ∧ Fractal (pot P D E Z W) ρ (c/(P.L.val:ℝ)^(2*m-1)*C) :=by
  obtain ⟨t,A,ht,ha,H⟩:= pack_funds hj hk
  let M:ℝ:=1+m
  have hv : 1≤ M:=le_add_of_nonneg_right (by positivity); have hp : 0 < M:=zero_lt_one.trans_le hv
  let w:=min η t
  have hu : 0<w:=lt_min hη ht
  let T:= psiPrice Ω Θ; have hT : 0≤T:=by unfold T psiPrice; positivity
  let B:=bouquet A T w m; have hb : 0≤B:=by unfold B bouquet; positivity
  let c:=ceiling w m B
  refine ⟨w/(M*M),c,by positivity,mul_nonneg (Real.exp_pos _).le hb, fun σ ρ C P hs hρ hr I W D E Z s hF hi hD hE hZ hh'=>?_⟩
  have hC:= (tsum_nonneg fun i=>frc (W i) σ).trans hh'.bill
  have hw:= (le_div_iff₀ (mul_pos hp hp)).1 hr
  have hd : ρ*M*M ≤ w:=by rwa [mul_assoc]; -- inspect
  have hx : ρ*M≤w:= (le_mul_of_one_le_right (mul_nonneg hρ.le hp.le) hv).trans hd
  have heq : Row.strip (psi D E Z none) (ρ*M) (T/(P.L.val:ℝ)^2):=fun i j=> ((psi_strip hη hD hE hi hZ none) i j).mono (hx.trans (min_le_left ..)) le_rfl
  have hfit : ρ*M ≤ σ*P.L.val:= hF
  let L:ℝ:= P.L.val
  have hn := tray_funds hh' (mul_nonneg hρ.le hp.le) hfit ha hT hh (fun i=> ⟨((H P i).1.mono (hx.trans (min_le_right ..)) le_rfl), ((H P i).2.mono (hd.trans (min_le_right ..)) le_rfl)⟩) heq
  refine ⟨⟨_,hn⟩, reduction (coined ρ hρ.le hn le_rfl) hρ.le le_rfl ?_⟩
  have hA:0≤ L:= (side_pos _).le
  unfold c ceiling; rw [div_mul_eq_mul_div, div_mul_eq_mul_div,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (pow_nonneg hA _)
  have hB : 0≤bouquet A T (ρ*M) m:=by unfold bouquet; positivity
  have hc : Real.exp (ρ*M*(2*m))≤Real.exp (w*(2*m)):=by gcongr
  have hL : bouquet A T (ρ*M) m ≤ B:=by unfold B bouquet; gcongr
  linarith only [mul_le_mul hc (mul_le_mul_of_nonneg_right hL hC) (mul_nonneg hB hC) ((Real.exp_pos _).le)]
end YM.QCD.Garden

namespace YM.QCD.Garden.Transfer
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m i:ℕ}{K:KernelChoices}{E:Patch}{p:Clip}{C B u v r a b c η Ω Θ:ℝ}{c₁:Side}
lemma pliant (P:Plan j)(T: Plan k) (m:ℕ)(hm:0<m)(hj:4≤j)(hk:4≤k)(hu:0<η)(hv:0≤Ω)(ht:0≤Θ): ∃ α X, 0<α∧0≤X∧∀ (K:KernelChoices)(E:Patch)(p:Clip)(u v:ℝ)
    (V: Back E K j k p u v) (_:Engine V η Ω Θ) (Y:On)(r s c:ℝ)(W:Offer m r c), 0 < r → 0 < s → s ≤ α → s*(1+m) ≤ r*E.L.val → Vital Y → (Clan V.chain (V.charge P T Y) ∧ ∀ j,Noble (V.charge P T Y j)) →(Clan V.chain (V.charge P T (Y+W.lamp)) ∧ ∀ j,Noble (V.charge P T (Y+W.lamp) j)) →
      ∃ A:Offer m s (X/(E.L.val:ℝ)^(2*m-1)*c), ∀ i,Tender ((V.charge P T (Y+W.lamp)-V.charge P T Y) i) (castF (A.lamp _)) (m+1):=by
  obtain ⟨σ,C,h,hC,H⟩:=panGreater η Ω Θ hu hj hk m hm hv ht; refine ⟨_,_,h,hC,fun K E p u v V J Y r s c W hp hs hF hL hx ⟨hM,hW⟩ ⟨hJ,hJ'⟩=>?_⟩
  obtain ⟨⟨y,hy⟩,hz⟩:= H r s c V.fly hp hs hF W.roots W.W J.D J.D' J.T J.s (V.has ▸ hL) J.begun J.price J.nextP J.coins W.price
  refine ⟨⟨_,_, ?_,Vital.tribute hz hs hm (fun _=>coined_port hy)⟩,fun j=>?_⟩
  · convert hz using 1; rw [V.has]
  obtain ⟨a,b,Hq⟩:= J.floorP j
  rw [Pi.sub_apply, differences ..]; have ht:0<s*(1+m):=by positivity
  apply noble_fruit J.begun hu J.nextP J.price J.coins (J.stays j) Hq hx W.bright (V.port.critical j) (J.sworn j) W.price hy hp ht ?_ ?_ hj hk
  · have h := (hJ.less hM).way j|>.ready; rwa [Pi.sub_apply, differences ..] at h
  have h: Noble (_-_) := Noble.less (hJ' j) (hW j); rwa [differences ..] at h


end YM.QCD.Garden.Transfer
#print axioms YM.QCD.Garden.Transfer.pliant
