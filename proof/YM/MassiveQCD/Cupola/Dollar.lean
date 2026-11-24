import YM.MassiveQCD.Cupola.Swipe
/-! # Billing EVEN in another normalization orientation -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function Loom
open scoped Topology BigOperators ContDiff Classical Matrix
variable {c:Side}{I:Type}[Fintype I]
variable (N:ℕ)(o:I→Site c)(φ:ℝ)(q:I→Bool)
local notation "M"=> ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "X"=> K⊕Spine I
-- normalization using stake lock height ALSO mark burst height-free after pen arm.
lemma withdrawCost (h:0<φ)(x:Patio X): load (fun _=>φ) (light _ (banknote N o φ x))=∑ i:Finset R,load (fun _=> φ) (pluck K i x):=by
     rw [bank_spent,pen,AlgHom.comp_apply]; let r:= stretch φ⁻¹ K R (light _ x); rw [transplant (territory N o) (q:=fun _=>φ) (k:=fun _=>h)] -- arg order
     rw [show (fun _=>φ)∘(territory N o)=expRate (p:=fun _=>φ) (q:=fun _=>φ) from funext fun i=> by cases i<;>rfl, fiscal (fun _=>h) (fun _=>h)]
     refine sum_congr rfl fun i _=>?_; have hp:scrape K i r=((φ⁻¹:ℝ):ℂ)^i.card • pluck K i x :=by
        unfold r
        conv_lhs =>
           rw [← rewriteR K (light _ x),map_sum,map_sum]
        rw [sum_eq_single i]; rw [stretches,quid]; rfl; intro j _ hj; rw [stretches,stakesX,if_neg hj.symm]; simp
     rw [hp, Finset.prod_const,load_scale,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr h).le]; rw [←mul_assoc,←mul_pow, mul_inv_cancel₀ h.ne',one_pow,one_mul]
lemma atWorth (h:0<φ)(s:Finset (Spine I))(x:Patio (Keys c N⊕Spine I)): load (fun _=>φ) (pluck (Keys c N) s x) ≤ ‖token c (ample N I) φ (banknote N o φ x)‖:=by
    -- load→ token norm exact
    have hh:load (fun _=>φ) (light _ (banknote N o φ x))= ‖token c (ample N I) φ (banknote N o φ x)‖:=rfl
    rw [←hh, withdrawCost N o φ h]; exact single_le_sum (f:=fun i=>load (fun _=>φ) (pluck (Keys c N) i x)) (fun t _=>load_nn (fun _=>φ) (pluck (Keys c N) t x)) (mem_univ s) -- lemma names
-- Color (action.slots) of TAPE.Payout is preserved on all Full. `Color` Lift.Sc
noncomputable def parcelColor (z: Lat.Frame c)(I:Type)[Fintype I] : (Patio (Keys c N⊕Spine I))→ₐ[ℂ] Patio (Keys c N⊕Spine I):=by
   let f:= slots N z; let p:= f.toLinearMap.toContinuousLinearMap; have hp x : p (grade x)= grade (p x):= (exterior_parity _ _).symm -- check slots.changeVars
   let St:= Spine I; let v:=carry St p; let a:=LinearMap.comp v.toLinearMap (light _).toLinearMap; let w:=a.codRestrict (roomA (K⊕St)).toSubmodule (fun x=> evenCarry St p hp x.val (bright x)); refine AlgHom.ofLinearMap w ?_ ?_
   · apply Subtype.ext; let F:=fiber St (1:Alg K); change v 1=1; rw [← map_one (fiber St (A:=K)),← quiet,speaks,show p 1=1 from map_one f, quiet, map_one]
   intro i j; exact Subtype.ext (ledger_alg f hp i.val j.val)
lemma partColor (I:Type)[Fintype I] (z: Lat.Frame c)(x:Patio (Keys c N⊕Spine I))(v: Finset (Spine I)): pluck (Keys c N) v (parcelColor N z I x)=slots N z (pluck (Keys c N) v x):= wing (Spine I) _ _ _
open Patron Sway OrbitG Villa Stitch Apron
lemma across (s:Finset I)(z:Lat.Frame c)(x:Patio (Keys c N⊕Spine I))(hv:Polite q s x) :
    banknote N o φ (parcelColor N z I x)=sways (Lat.rotates (ample N I) z) (banknote N o φ x):=by
    apply Subtype.ext; let p:= carry R (slots N z).toLinearMap.toContinuousLinearMap; change pen N o φ (p x.val)= slots (ample N I) z (pen N o φ x.val); nth_rw 1 2 [← hv.exact]; rw [show p _=_ from speaks (Spine I) (slots N z).toLinearMap.toContinuousLinearMap _ _]; exact (signal N o z q s φ _).symm -- order argument? implicit h
lemma vault (s:Finset I)(x:Patio X)(z:Lat.Frame c)(hv:Polite q s x): Polite q s (parcelColor N z I x):= politeStep (slots N z).toLinearMap.toContinuousLinearMap hv rfl
lemma all_color (z: Lat.Frame c)(x:Patio X)(h: ValidPieces K q univ x): banknote N o φ (parcelColor N z I x)=sways (Lat.rotates (ample N I) z) (banknote N o φ x):=by
    rw [h.wholeV,map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; exact fun i _=> across N o φ q i z _ (choseTuft _ _ _ _)
lemma homeTone (z:Lat.Frame c)(x:Patio X)(h:ValidPieces K q univ x):ValidPieces K q univ (parcelColor N z I x):=by rw [h.wholeV,map_sum]; exact ValidPieces.cost _ _ (fun i _=>ValidPieces.role _ (vault N (c:=c) q i _ z (choseTuft _ _ _ _)) (subset_univ _))
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.homeTone
