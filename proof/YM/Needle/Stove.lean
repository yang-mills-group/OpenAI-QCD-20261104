import YM.Needle.Slots
/-!
  Backsolving all authentic averaging conventions on a detector and kernel aperture.
  Volume prices, horizon inclusions allocated later against THIS frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
noncomputable def mover (i:ℕ)(u:Averaging):Label d→ₗ[ℂ]Label d:= ((P.mix d u i).trans (P.mix d none i).symm).toLinearMap
lemma moveV (i:ℕ)(u:Averaging)(x:Label d): stem P d i (mover P d i u x)=stemV P d i u x:=by ext1 t; change P.candidate _ _ _ (P.mix d none i ((P.mix d none i).symm _))=_; rw [LinearEquiv.apply_symm_apply]; rfl
variable {P d} {E:Invest P d}
structure Wealthy (H:Rack E) :Prop where
    hi : ∃ A:ℝ, 1 ≤ A ∧∀ᶠ i in atTop,∀ (u:Averaging)(x:Label d), ‖x‖ ≤ 1 → H.w i (mover P d i u x) ≤ A*H.κ i
structure Spring (P:Calibration C) (d:ℕ):Prop where
    reach (u:Averaging) (x:Label d) (p:Bool)(hp:moored x.val p)(h:x≠0): Basket C (fun i=>stemV P d i u x) u
variable {Z:Laurel d}{J:Landing P.sym Z} {β ν:ℝ}(hC:C.Path β ν)
namespace GaugeP
variable (K: GaugeP P Z J)(G:Capital P d 1)(H:Rack E)(hG:Sway C.S)(h: Wealthy H)(hv:Spring P d)
noncomputable def glean (u:Averaging)(i:ℕ):Label d→ₗ[ℂ](Stokes d→ℂ) := (tip K E i).comp (mover P d i u)
noncomputable def grains (u:Averaging)(i:ℕ):Label d→ₗ[ℂ](Fin (deficit d)→ℂ):= (tipEnd K E i).comp (mover P d i u)
include hC G hG h hv
lemma tilted (u:Averaging)(x:Label d)(p:Bool)(hP:moored x.val p):∃ T M:ℝ,0 ≤ T∧ 0 ≤ M ∧ ∀ᶠ i:ℕ in atTop, ‖K.glean (E:=E) u i x‖≤ T ∧ ‖K.grains (E:=E) u i x‖ ≤ M*E.scale i:=by
    by_cases hz:x=0; · subst x; exact ⟨0,0,le_rfl,le_rfl,Eventually.of_forall fun _=>by simp⟩
    obtain ⟨B,hB,hN⟩:= testPack hC K hG G u (fun i=> stemV P d i u x) (hv.reach u x p hP hz); obtain ⟨A,hA,hk⟩:= h.hi
    have hm:0 < ‖x‖:= norm_pos_iff.mpr hz
    have hp:0 < ‖x‖*A:=mul_pos hm (zero_lt_one.trans_le hA)
    obtain ⟨L,M,hL,hM,hV⟩:= racks hC K hG G H (‖x‖*A) B hp hB
    refine ⟨L,M,hL.le,hM,?_⟩; filter_upwards [hk,hV,hN] with i hi h ht
    obtain ⟨O,h'⟩:= ht; apply h (mover P d i u x) ?_ ⟨O,(by rw [moveV]; exact h')⟩
    let s:ℂ:= (‖x‖:ℂ)⁻¹; have hs : ‖s‖= ‖x‖⁻¹:=by unfold s; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hm.le]
    have hu:‖s • x‖ ≤ 1:=by rw [norm_smul,hs,inv_mul_cancel₀ hm.ne']
    have hQ:= hi u _ hu; rw [map_smul,H.dimM, hs,inv_mul_eq_div, div_le_iff₀ hm] at hQ; exact hQ.trans_eq (by ring)
lemma pours (u:Averaging)(x:Label d):∃ T M:ℝ,0 ≤ T∧ 0 ≤ M ∧ ∀ᶠ i:ℕ in atTop, ‖K.glean (E:=E) u i x‖≤ T ∧ ‖K.grains (E:=E) u i x‖ ≤ M*E.scale i:=by
     obtain ⟨L,M,hL,hM,h1⟩:=tilted hC K G H hG h hv u _ true (fronting P.sym x true); obtain ⟨b,c,hb,hc,h2⟩:=tilted hC K G H hG h hv u _ false (fronting P.sym x false); refine ⟨L+b,M+c,add_nonneg hL hb,add_nonneg hM hc,?_⟩; filter_upwards [h1,h2] with i hi hj; rw[revelation P.sym x,map_add,map_add,add_mul]; exact ⟨(norm_add_le ..).trans (add_le_add hi.1 hj.1), (norm_add_le ..).trans (add_le_add hi.2 hj.2)⟩ -- fronting sig
lemma attests (u:Averaging):∃ T M:ℝ,0 ≤ T∧ 0 ≤ M ∧ ∀ᶠ i:ℕ in atTop,∀ x:Label d, ‖K.glean (E:=E) u i x‖≤ T*‖x‖ ∧ ‖K.grains (E:=E) u i x‖ ≤ M*‖x‖*E.scale i:=by
      let b:= Module.finBasis ℂ (Label d); let Γ:= Fin (Module.finrank ℂ (Label d)); choose v t h0 h1 h using fun i:Γ=> pours hC K G H hG h hv u (b i)
      let F (i:Γ):= (b.coord i).toContinuousLinearMap; let V:=∑ i:Γ,‖F i‖ * v i; let T:=∑ i:Γ,‖F i‖*t i
      refine ⟨V,T,Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (h0 i),Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (h1 i),?_⟩; filter_upwards [eventually_all.mpr h] with i hi x
      have hx:x=∑ k:Γ,F k x • b k :=(b.sum_repr x).symm
      constructor
      · conv_lhs=>rw [hx, map_sum]
        apply (norm_sum_le ..).trans; unfold V; rw[Finset.sum_mul]; refine sum_le_sum (fun k _=>?_); rw [map_smul,norm_smul]; exact (mul_le_mul ((F k).le_opNorm _) (hi k).1 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
      conv_lhs=>rw [hx,map_sum];
      apply (norm_sum_le ..).trans; unfold T; rw[Finset.sum_mul, Finset.sum_mul]; refine sum_le_sum (fun k _=>?_); rw [map_smul,norm_smul]; exact (mul_le_mul ((F k).le_opNorm _) (hi k).2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
omit h hv
variable (E)
lemma weave(u:Averaging) :∀ᶠ i in atTop,∀ x:Label d, stemV P d i u x=stem P d i (K.ridge i (glean (E:=E) K u i x))+stem P d i (Investment.face E i (grains (E:=E) K u i x)):=by
     filter_upwards [slices hC K hG G E] with i hi x; rw[←map_add,←moveV]; exact congr_arg _ (hi _).symm
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.attests
#print axioms YM.Massive.Needle.GaugeP.weave
