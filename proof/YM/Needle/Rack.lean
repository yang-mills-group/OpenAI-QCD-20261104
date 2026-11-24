import YM.Needle.Bezel
/-!
  Use both upper bounds. Rank inversion at the same estimator latitude.
  Works with general prices useful for all label helmets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}(Z:Laurel d) (J:Landing P.sym Z)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Xι"=>Stokes d→ℂ
local notation "Xµ"=>Fin (deficit d)→ℂ
variable {β ν:ℝ}(hC:C.Path β ν)
variable {P Z J} (E:Invest P d)
-- price family preweight hzn.
structure Rack (E:Invest P d) where
    w : ℕ→Label d→ℝ
    κ:ℕ→ℝ
    κ_pos : ∀ i,0<κ i
    sw : ∀ᶠ i in atTop,∀ x y:Label d,w i (x-y) ≤ w i x + w i y
    dimM : ∀ (i:ℕ)(z:ℂ)(x:Label d), w i (z • x)=‖z‖*w i x
    pin : ∃ A:ℝ,0 ≤ A ∧∀ᶠ i in atTop,∀ x:Label d,‖x‖ ≤1→ w i x ≤ A * κ i
    allowance : ∀ᶠ i in atTop,∀ p:Fin (deficit d)→ ℂ, w i (Investment.face E i p) ≤ κ i→ ‖p‖ ≤ E.scale i
namespace Rack
variable {E}(H:Rack E)
lemma booth : ∃ A:ℝ,0 ≤ A∧∀ᶠ i in atTop,∀ x:Label d, H.w i x ≤ ‖x‖*(A*H.κ i):=by
     obtain ⟨V,hv,h⟩:= H.pin; refine ⟨_,hv,?_⟩; filter_upwards [h] with i hi x
     by_cases h:x=0; · subst x; simp only [norm_zero,zero_mul]; have hx:= H.dimM i 0 (0:Label d); rw[zero_smul,norm_zero,zero_mul] at hx; exact hx.le
     have he :0<‖x‖:=norm_pos_iff.mpr h
     let p:ℂ:= (‖x‖:ℂ)⁻¹; have hp: ‖p‖=‖x‖⁻¹:=by unfold p; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg he.le]
     have hv':‖p • x‖≤ 1:=by rw [norm_smul,hp,inv_mul_cancel₀ he.ne']
     have hu:= hi (p • x) hv'; rw[H.dimM,hp,inv_mul_eq_div] at hu; rw [mul_comm]; exact (div_le_iff₀ he).1 hu
lemma contributes :∀ᶠ i in atTop,∀ p:Fin (deficit d)→ ℂ, ∀ A:ℝ,0 < A→ H.w i (Investment.face E i p)≤ A *H.κ i → ‖p‖ ≤ A*E.scale i:=by
     filter_upwards [H.allowance] with i hi p A hv h
     let a:ℂ:= (A:ℂ)⁻¹; have ha:‖a‖= A⁻¹:=by unfold a; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hv.le]
     have hp: H.w i (Investment.face E i (a • p)) ≤ H.κ i:=by
         rw [map_smul,H.dimM,ha,inv_mul_eq_div, div_le_iff₀ hv]; exact h.trans_eq (mul_comm ..)
     have hP:= hi (a • p) hp; rw [norm_smul,ha,inv_mul_eq_div, div_le_iff₀ hv] at hP; rw [mul_comm]; exact hP
noncomputable def regular (E:Invest P d): Rack E:=⟨fun _ x=> ‖x‖,fun _=>1,fun _=>zero_lt_one,Eventually.of_forall fun _ x y=>norm_sub_le ..,fun _=>norm_smul,⟨1,zero_le_one,Eventually.of_forall fun i x hx=>hx.trans_eq (by simp)⟩, E.heights⟩
end Rack
variable {E}
namespace GaugeP
variable (K: GaugeP P Z J) (hv:Sway C.S)(G:Capital P d 1) {E:Invest P d} (H:Rack E)
variable (i:ℕ) {A:ℝ}
open Investment
include hC G hv
lemma topped (hA:0<A) : ∃ B:ℝ,0 < B ∧∀ᶠ i in atTop,∀ p:Label d,H.w i p ≤ A*H.κ i → ‖tipEnd K E i p‖ ≤ B*(1+‖tip K E i p‖)*E.scale i:=by
    obtain ⟨C0,hc0,h1⟩:= H.booth
    let b:= C0*K.heightM; have hb:0 ≤ b:=mul_nonneg hc0 K.h_positive; let B:= A+b; have hB:0<B:=add_pos_of_pos_of_nonneg hA hb
    refine ⟨B,hB,?_⟩; filter_upwards [slices hC K hv G E,H.contributes,h1,H.sw,K.pluck] with i hi ht h Hh hM p hx
    let q:= tip K E i p; let Q:= tipEnd K E i p; have he:face E i Q=p-K.ridge i q:=by rw[← eq_sub_of_add_eq' (hi p)] -- suspect lemma orientation
    have hh: H.w i (face E i Q) ≤ B*(1+‖q‖)*H.κ i:=by
         rw [he]; apply (Hh _ _).trans; apply (add_le_add hx ((h _).trans (mul_le_mul_of_nonneg_right (hM q) (mul_nonneg hc0 (H.κ_pos _).le)))).trans; rw [show K.heightM*‖q‖*(C0*H.κ i) = b*‖q‖ * H.κ i from by unfold b; ring, ←add_mul]; apply mul_le_mul_of_nonneg_right _ (H.κ_pos _).le; change _ ≤ (A+b)*_; nlinarith only [norm_nonneg q,hA,hb]
    exact ht Q _ (mul_pos hB (by positivity)) hh
lemma racksA (A T:ℝ)(hA:0<A)(hT:0 ≤ T):∃ Z':ℝ,0 < Z' ∧ ∀ᶠ i:ℕ in atTop,∀ p:Label d,H.w i p ≤ A *H.κ i →∀ O:Merit K i, ‖O.testR (stem P d i p)‖ ≤ T→ ‖tip K E i p‖ ≤ Z':=by
    obtain ⟨B,hB,h⟩:=topped hC K hv G H hA; obtain ⟨f,hf,hX⟩:= near_race hC K hv G E; let Z':=2*(J.J*T+2)
    have hp':0<Z':=by unfold Z'; have hi:= J.fee; positivity
    let V(i:ℕ):=J.J*(E.scale i*f i*B); have hV:Tendsto V atTop (𝓝 0):=by simpa only [V,mul_zero,zero_mul] using (hf.mul_const B).const_mul J.J
    refine ⟨Z',hp',?_⟩; filter_upwards [h,hX,hV.eventually_le_const (show (0:ℝ)<1/2 from by norm_num),K.loyalH,slices hC K hv G E] with i hi hx h' hu Hq p hm O He
    let q:= tip K E i p; let Q:= tipEnd K E i p; let Vz:= V i; let L:= O.testR.comp (stem P d i); have hq:K.ridge i q = p-face E i Q:= eq_sub_of_add_eq (Hq p)
    have ht: ‖q‖ ≤ J.J*T+V i*(1+‖q‖):= calc
         _ ≤ J.J*‖L (K.ridge i q)‖:=hu O q
         _ ≤ J.J*(T + B*(1+‖q‖)*E.scale i*f i):= by rw [hq,map_sub]; apply mul_le_mul_of_nonneg_left _ J.fee; refine (norm_sub_le ..).trans (add_le_add He (le_trans (hx.2 O Q) ?_)); exact mul_le_mul_of_nonneg_right (hi p hm) hx.1
         _ = _ := by unfold V; ring
    have hv := ht.trans (add_le_add_right (mul_le_mul_of_nonneg_right (show V i≤ 1/2 from h') (show 0≤1+‖q‖ from by positivity)) (J.J*T)) -- add_left naming
    change ‖q‖≤ 2*(J.J*T+2); linarith only [hv]
lemma racks (A T:ℝ)(hA:0<A)(hT:0 ≤ T):∃ Z' Cb:ℝ,0 < Z' ∧ 0 ≤ Cb ∧∀ᶠ i:ℕ in atTop,∀ p:Label d,H.w i p ≤ A *H.κ i →(∃ O:Merit K i, ‖O.testR (stem P d i p)‖ ≤ T)→ ‖tip K E i p‖ ≤ Z'∧ ‖tipEnd K E i p‖ ≤ Cb*E.scale i:=by
     obtain ⟨Z',hz,Hq⟩:= racksA hC K hv G H A T hA hT; obtain ⟨B,hB,h⟩:= topped hC K hv G H hA; refine ⟨Z',B*(1+Z'),hz,by positivity,?_⟩; filter_upwards [Hq,h] with i hi hm p hx hP; obtain ⟨O,hO⟩:= hP; have he:= hi p hx O hO; exact ⟨he,(hm p hx).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right he _) hB.le) (E.pos _))⟩
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Rack.regular
#print axioms YM.Massive.Needle.GaugeP.racks
