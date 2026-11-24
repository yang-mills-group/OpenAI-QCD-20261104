import YM.Plateau.Mallet
import YM.Shade.Aster
/-! The authentic iso metering row connected to continuum rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Massive.Fir Fir YM.Fir.NoteF Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Choir
variable {Q: Choir}
variable (H:Q.Harmony P φ)
namespace Measures
set_option maxHeartbeats 720000

variable (ℓ:ℕ)(r:Averaging)(b:Cover)(A:Set E4){d:ℕ}
variable (zm vm:ℕ→ Stokes d→Label d)
variable (z v:Stokes d→Label d)(hx:Tendsto (zm ∘φ) atTop (𝓝 z))(hv:Tendsto (vm∘φ) atTop (𝓝 v))
local notation "T" i:arg a:arg=> tapW P ℓ i b r a
abbrev DeckP:=Stokes d→ℂ
noncomputable abbrev tall (v:Stokes d→Label d) (y:DeckP (d:=d)):=∑ i,y i • v i
noncomputable def sto (Q:Choir)(r:Averaging)(v:Stokes d→Label d):DeckP (d:=d)→ₗ[ℂ] Q.W where
      toFun t:= Q.focus r d (tall v t)
      map_add' x y:=by unfold tall; simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib,map_add]
      map_smul' a x:=by unfold tall; simp only [Pi.smul_apply, smul_assoc]; rw [←Finset.smul_sum,map_smul]; rfl -- simp left
noncomputable def stake (Q:Choir)(H:Q.Domestic) (r:Averaging)(v:Stokes d→Label d) : DeckP (d:=d) →ₗ[ℂ] (Q.level d):= (sto Q r v).codRestrict (Q.level d) (fun x=>by rw [← H.tops r d]; exact ⟨tall v x,rfl⟩)
local notation "TQ" i:arg=> fun j k:Stokes d => tapW P ℓ i b r (zm i j) (vm i k)
variable (S:Laurel d)(J:Landing P.sym S)(B δ:ℝ)
variable (hT:∀ᶠ i in atTop,nearG P.sym S J.ε (fun j k:Stokes d => tapW P ℓ (φ i) b r (zm (φ i) j) (vm (φ i) k)))
variable (hA:IsCompact A)(hn:0∉A)(hs:Pasture C ℓ b A)
lemma pipe_cost (i:ℕ)(x:Stokes d→ℂ)(j:Stokes d): Γ (TQ i) x j = tapW P ℓ i b r (zm i j) (tall (vm i) x):=by
       change ∑ k:Stokes d, tapW P ℓ i b r (zm i j) (vm i k)*x k=tapW P ℓ i b r (zm i j) (tall (vm i) x); unfold tall; rw [map_sum]; apply Finset.sum_congr rfl; intro k _; rw[map_smul]; exact mul_comm ..
include hφ hp hx hv H hA hn hs hT
lemma detectR : Bijective (stake Q H.h r v):=by
       suffices he:Injective (stake Q H.h r v) from ⟨he,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (show Module.finrank ℂ (DeckP (d:=d)) = Module.finrank ℂ (Q.level d) from (by rw [H.h.faith]; simp [DeckP,Stokes,Module.finrank_pi]))).mp he⟩
       intro a y hQ; let t:=a-y; have ht:stake Q H.h r v t=0:=(map_sub ..).trans (sub_eq_zero.mpr hQ); let V(i:ℕ):= TQ i
       let Bq(i:ℕ):=tall (vm i) t -- shadow b fix
       have hz:Tendsto (fun i=>Γ (TQ (φ i)) t) atTop (𝓝 0):= by
            apply tendsto_pi_nhds.mpr; intro k; simp_rw [pipe_cost]; exact nullS hp hφ H (z k) r (tall v t) (fun j=>zm j k) Bq (show Tendsto (fun i=>tall (vm (φ i)) t) atTop _ from tendsto_finsetSum _ fun i _=> (tendsto_pi_nhds.mp hv i).const_smul _) (tendsto_pi_nhds.mp hx k) A ℓ b (congr_arg Subtype.val ht) hA hn hs -- arity
       apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have he:Tendsto (fun i=>J.J*‖Γ (TQ (φ i)) t‖) atTop (𝓝 0):=by simpa only[norm_zero,mul_zero] using (hz.norm.const_mul J.J)
       exact ge_of_tendsto he (hT.mono fun i hi=>J.warmth hi t)
lemma pursed (q:ℕ→ Label d)(u:Label d)(hq:Tendsto (q∘φ) atTop (𝓝 u))(hV:∀ j:Stokes d,‖v j‖ ≤ B)(hD:∀ᶠ i in atTop,∀ j:Stokes d,‖tapW P ℓ (φ i) b r (zm (φ i) j) (q (φ i))‖ ≤ δ)(hb0:0 ≤ B)(hδ:0<δ):∃ p: Label d, Q.focus r d p=0∧ ‖u-p‖ ≤ Fintype.card (Stokes d)* (J.J*(δ+δ)*B):=by
       obtain ⟨t,hP⟩:= (detectR hp hφ H ℓ r b A zm vm z v hx hv S J hT hA hn hs).surjective (⟨Q.focus r d u,(H.h.tops r d) ▸ ⟨u,rfl⟩⟩); let w:= tall v t; have hw:Q.focus r d w= Q.focus r d u:= congr_arg Subtype.val hP; let F(i:ℕ):= TQ i; let W(i):= tall (vm i) t-q i; let p:=u-w
       refine ⟨p,(map_sub ..).trans (sub_eq_zero.mpr hw.symm),?_⟩; have hxQ:∀ j:Stokes d,Tendsto (fun i=> tapW P ℓ (φ i) b r (zm (φ i) j) (W (φ i))) atTop (𝓝 0):=by
            have hX:Tendsto (fun i=>W (φ i)) atTop (𝓝 (w-u)):= (tendsto_finsetSum _ (fun j _=> (tendsto_pi_nhds.mp hv j).const_smul (t j))).sub hq; exact fun j=> nullS hp hφ H (z j) r (w-u) (fun i=>zm i j) W hX (tendsto_pi_nhds.mp hx j) A ℓ b ((map_sub ..).trans (sub_eq_zero.mpr hw)) hA hn hs
       obtain ⟨i,hi,h,he⟩:= (hT.and (hD.and (eventually_all.mpr (fun j:Stokes d=> Metric.tendsto_nhds.mp (hxQ j) δ hδ)))).exists
       have hp:‖t‖ ≤ J.J*(δ+δ):=by
            refine (J.warmth hi t).trans (mul_le_mul_of_nonneg_left ?_ J.fee); refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j=>?_ ; let L:= T (φ i) (zm (φ i) j); let v:=q (φ i); have hh:tall (vm (φ i)) t=W (φ i)+v:= (sub_add_cancel ..).symm
            rw [pipe_cost,hh,map_add]; apply (norm_add_le ..).trans; exact add_le_add ((by simpa only [dist_zero_right] using (he j).le):‖L (W (φ i))‖ ≤δ) (h j)
       rw [show u-p=w from sub_sub_cancel u w]; apply (norm_sum_le ..).trans; refine le_trans (Finset.sum_le_sum (g:=fun _=> (J.J*(δ+δ))*B) (fun i _=>?_)) (by simp); rw[norm_smul]; exact mul_le_mul ((norm_le_pi_norm t i).trans hp) (hV i) (norm_nonneg _) (mul_nonneg J.fee (by positivity))
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.pursed
