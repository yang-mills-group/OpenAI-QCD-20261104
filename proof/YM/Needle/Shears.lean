import YM.Needle.Crest
/-!
  # A finite-dimensional calibrated rank theorem
  The point-operator frame is complementary to the price aperture kernel on all late volumes.
  No extrapolation of the free-rank measurement is used.
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
local notation "Xκ"=> (Stokes d→ℂ) × (Fin (deficit d)→ℂ)
variable {β ν:ℝ}(hC:C.Path β ν)
variable {P Z J}
namespace GaugeP
variable (K: GaugeP P Z J) (hv:Sway C.S)(G:Capital P d 1) (E:Invest P d)
variable (i:ℕ)
open Investment
noncomputable def ridgeL : ((Stokes d→ℂ) × (Fin (deficit d)→ℂ)) →ₗ[ℂ] Label d:=(K.ridge i).comp (LinearMap.fst ℂ _ _) + (Investment.face E i).comp (LinearMap.snd ℂ _ _)
variable {i}
-- normalized pullbacks
lemma race_height :∀ᶠ i in atTop,∀ v (x:Xµ),0 < v→ ‖Investment.face E i x‖ ≤ v → ‖x‖ ≤ v*E.scale i:=by
   filter_upwards [E.heights] with i hi v x hv hx
   let s:ℂ:= (v:ℂ)⁻¹; have hs:‖s‖=v⁻¹:=by unfold s; rw[norm_inv, Complex.norm_real,Real.norm_of_nonneg hv.le]
   have hsi:0<v⁻¹:=inv_pos.mpr hv
   have hu: ‖face E i (s • x)‖ ≤1:=by rw [map_smul,norm_smul,hs]; exact (mul_le_mul_of_nonneg_left hx hsi.le).trans_eq (inv_mul_cancel₀ hv.ne')
   have hh:= hi (s • x) hu; rw [norm_smul,hs,inv_mul_eq_div,div_le_iff₀ hv] at hh; rw [mul_comm]; exact hh
#check LinearMap.finrank_range_add_finrank_ker
#check LinearMap.injective_iff_surjective_of_finrank_eq_finrank
#check Module.finrank_pi
-- the price kernels give exact eventual frames without limiting topology. 
lemma exactRank(d:ℕ): Module.finrank ℂ ((Stokes d→ℂ) × (Fin (deficit d)→ℂ))= Module.finrank ℂ (Label d):=by
   have hz:= LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=UV.Label d) (V₂:=UV.Free.Symbol d) (@UV.Free.projection d); rw[LinearMap.range_eq_top.mpr UV.Free.onto, finrank_top] at hz; rw [Module.finrank_prod]; simpa [Stokes,deficit,Module.finrank_pi] using hz -- fix using hz
include hC G hv
lemma poised : ∀ᶠ i:ℕ in atTop,Bijective (ridgeL K E i):=by
    obtain ⟨f,hf,H⟩:= cheapH hC K hv G E; let T:= K.heightM+1; have ht:0<T:=by unfold T; linarith only [K.h_positive]
    have hm:K.heightM≤T:= by unfold T; linarith
    let V(i:ℕ):= J.J*(T*(E.scale i * f i)); have hy:Tendsto V atTop (𝓝 0):=by simpa only [V,mul_zero] using (hf.const_mul T).const_mul J.J
    filter_upwards [lively hC K,H,E.uniqueI,K.vision, K.pluck,race_height E,hy.eventually_lt_const zero_lt_one] with i hi hp h₁ h₂ h₃ h₄ hz; obtain ⟨x,hx⟩:=hi
    suffices h:Injective (ridgeL K E i) from ⟨h, LinearMap.injective_iff_surjective_of_finrank_eq_finrank (exactRank d) |>.mp h⟩
    have h (p:Xι)(v:Xµ)(h: K.ridge i p+face E i v=0):p=0∧ v=0:=by
         have he:face E i v= -(K.ridge i p):= eq_neg_of_add_eq_zero_right h -- lemma orientation
         have hP:p=0:=by
             by_contra Hk
             have hw:0< ‖p‖:= norm_pos_iff.mpr Hk
             have hb : ‖face E i v‖ ≤ T * ‖p‖:=by rw [he,norm_neg]; exact (h₃ p).trans (mul_le_mul_of_nonneg_right hm hw.le)
             have hΨ := hp.2 x hx v; rw [he,map_neg,map_neg,norm_neg] at hΨ
             have hu:(‖p‖* V i) < ‖p‖:= by simpa only [mul_one] using mul_lt_mul_of_pos_left hz hw
             apply hu.not_ge; exact (h₂ x hx p).trans ((mul_le_mul_of_nonneg_left (hΨ.trans (mul_le_mul_of_nonneg_right (h₄ _ _ (mul_pos ht hw) hb) hp.1)) J.fee).trans_eq (by unfold V; ring))
         rw [hP,map_zero,neg_zero] at he; exact ⟨hP,funext (fun k=> Fintype.linearIndependent_iff.mp h₁ v he k)⟩
    intro p q he; have hy:ridgeL K E i (p-q)=0:=by rw [map_sub,he,sub_self]
    obtain ⟨hm,hv⟩:= h _ _ (show K.ridge i (p.1-q.1)+face E i (p.2-q.2)=0 from hy); exact Prod.ext (sub_eq_zero.mp hm) (sub_eq_zero.mp hv)
omit hC G hv
noncomputable def cutting (i:ℕ): Label d →ₗ[ℂ] ((Stokes d→ℂ) × (Fin (deficit d)→ℂ)):= if h: Bijective (ridgeL K E i) then (LinearEquiv.ofBijective _ h).symm.toLinearMap else 0
noncomputable def tip (i:ℕ):Label d →ₗ[ℂ] (Stokes d→ℂ):=(LinearMap.fst ℂ _ _).comp (cutting K E i)
noncomputable def tipEnd (i:ℕ):Label d→ₗ[ℂ](Fin (deficit d)→ℂ):=(LinearMap.snd ℂ _ _).comp (cutting K E i)
include hC G hv
lemma slices : ∀ᶠ i:ℕ in atTop,∀ p:Label d,K.ridge i (tip K E i p) + Investment.face E i (tipEnd K E i p)=p:=by
    filter_upwards [poised hC K hv G E] with i hi p; change ridgeL K E i (cutting K E i p)=p; rw[cutting,dif_pos hi]; exact (LinearEquiv.ofBijective (ridgeL K E i) hi).apply_symm_apply p
lemma servesR :∀ᶠ i:ℕ in atTop,∀ c r, let p:=K.ridge i c+Investment.face E i r; tip K E i p = c∧ tipEnd K E i p=r:=by
    filter_upwards [poised hC K hv G E,slices hC K hv G E] with i hi hx c r; intro p
    have h:cutting K E i p=(c,r):=hi.1 (hx p); exact ⟨congr_arg Prod.fst h,congr_arg Prod.snd h⟩ -- infer pair projections
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.poised
#print axioms YM.Massive.Needle.GaugeP.servesR
