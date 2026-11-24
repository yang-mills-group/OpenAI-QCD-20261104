import YM.Shade.Robins
import YM.Shade.Dove
import YM.Shade.Belt
/-! Literal uniform cost readings used in mixture. -/
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

variable {d k:ℕ}(w:Label d)(r:Averaging)(v:Label k)(y:ℕ→Label k)(hx:Tendsto y atTop (𝓝 v)) (A:Set E4)(x:E4)

open Needle.GaugeP
lemma smaller {r:ℝ}(he:0<r) (hp:C.Path β e):∀ᶠ j in atTop,C.S.spacing j < r:=by obtain ⟨j,h,hj⟩:= shyness hp r he 0; exact (eventually_ge_atTop j).mono fun k hk=> lt_of_le_of_lt (spacing_antitone C.S hk) hj
private lemma clan (A₁ A₂:ℂ)(x:ℝ)(h:0≤x)(a:ℂ)(v:ℝ)(ha:‖A₁‖≤a.re)(hb:‖A₂‖ ≤a.re):‖x • (A₁-A₂)‖ ≤ x*(2*a.re):=by rw[norm_smul, Real.norm_of_nonneg h]; apply mul_le_mul_of_nonneg_left _ h; linarith only [norm_sub_le A₁ A₂,ha,hb]
lemma netted (t ε:ℝ)(A₁ A₂ X Y b:ℂ)(ht:0 < t)(hV:‖A₁-X‖ ≤ ε*t)(hW:‖A₂-Y‖≤ε*t)(h:‖(t⁻¹/2) • (X-Y)-b‖≤ ε):‖(t⁻¹/2) • (A₁-A₂)-b‖ ≤2*ε:=by
    let a:= (t⁻¹/2) • (X-Y); let x:= (t⁻¹/2) • (A₁-A₂); have hl:‖x-a‖ ≤ ε:=by unfold x a; rw[← smul_sub, sub_sub_sub_comm]; refine (clan _ _ _ (by positivity) (↑(ε*t):ℂ) ε hV hW).trans_eq ?_; rw[Complex.ofReal_re]; field_simp [ht.ne'] -- inspect rewrites sub_sub
    rw [show (t⁻¹/2) • (A₁-A₂)-b=(x-a)+(a-b) from (sub_add_sub_cancel ..).symm]; change ‖_‖ ≤ _; refine (norm_add_le ..).trans ?_; exact (add_le_add hl h).trans_eq (by ring)
local notation "J" i:arg=> (C.N i)
local notation "Γ"=> MassFields.isotropic
local notation "L" a:arg=> MassFields.atVector a
local notation "u"=> Q.focus none d w
local notation "c" i:arg=> C.S.spacing i
local notation "W" i:arg=> rod2 C i (stem P d i w)
variable (a:Axis)(ε:ℝ)(he:0 < ε)(hv:x≠0)
include hφ hp he hv H hx
lemma incomeT :∀ᶠ j in atTop,∀ ℓ:ℕ,j≤ℓ →∀ᶠ i in atTop, let m:=φ i; ℓ ≤ C.N m → ‖(W m) (checkedT r (ratioTo C.S (C.N m) ℓ) (stemV P k m r (y m)) (penC C.S j ℓ x)) - ans2 u (Q.focus r k v) x‖ ≤2*ε :=by
    let g(z):= ans2 u (Q.focus r k v) z; have hg: ContinuousAt g x:= (((H.h.smooth 2 _).continuousOn.continuousAt ((conf_open _).mem_nhds (forms hv))).comp arm.continuous.continuousAt) -- (arm x) elaboration
    have ht:∀ᶠ z in 𝓝 x, ‖g z-g x‖ < ε:= (hg.tendsto.eventually (Metric.ball_mem_nhds (g x) he)).mono fun i hi=>by rw [← dist_eq_norm]; exact hi
    obtain ⟨δ,hδ,hK⟩:= Metric.mem_nhds_iff.mp ht; let t:= min (δ/2) (dist (0:E4) x /2); have hp0:0<dist (0:E4) x:=dist_pos.mpr (Ne.symm hv); have hh:0<t:=lt_min (half_pos hδ) (half_pos hp0); have h₁:t<δ:= lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)
    let A':= Metric.closedBall x t; have he':0 ∉ A':=by rw [show 0∈ A' ↔ dist 0 x ≤ t from Iff.rfl]; exact not_le.mpr ((min_le_right ..).trans_lt (half_lt_self hp0))
    have hf:= pricedQ hφ H w r v y hx A' (isCompact_closedBall ..) he' ε he
    filter_upwards [smaller (show 0<t/202 from by positivity) hp] with j hj ℓ hl
    filter_upwards [hf] with i H₁ m hM
    let I:= ↥(Lattice.box (flex C.S ℓ (C.N m))); let g₀(z:I):=spotB C.S j ℓ (C.N m) x z.val; let V':=stemV P k m r (y m)
    obtain ⟨f,hf,hF,hR⟩:= strummed (C.S) (penC C.S j ℓ x) r V' hM; change ‖(W m) (Averaging.filter r (ratioTo C.S (C.N m) ℓ) V' _)-g x‖≤_; rw [hR,map_sum]; simp_rw [map_smul]
    refine purseL f _ _ (g x) hf hF fun i'=>?_; let z:= digit (C.S.spacing (J m)) (g₀ i'); have hz':dist z x≤ 202*C.S.spacing j:= fleck hl hM i'.val i'.property; have hz : dist z x≤t:=by linarith only [hz',hj]
    have hZ : ‖g z-g x‖ <ε:=hK (show z∈ Metric.ball x δ from hz.trans_lt h₁);
    let F:= (W m) (V' (g₀ i')); have hl':‖F-g z‖ ≤ε:= H₁ _ hz; change ‖F - g x‖ ≤ _; rw [← sub_add_sub_cancel F (g z) (g x)]; linarith only [norm_add_le (F-g z) (g z-g x),hl',hZ]
omit hx
lemma voiceT : ∀ᶠ j in atTop,∀ ℓ:ℕ,j≤ℓ →∀ᶠ i in atTop, let m:=φ i; let h:=C.N m; ℓ ≤ h → ‖(W m) (checkedT Γ (ratioTo C.S h ℓ) (Rolls.nick ((C.S.spacing h)⁻¹) a (stemV P k m (L a) v)) (penC C.S j ℓ x)) - ans2 u (Q.arc a (Q.focus (L a) k v)) x‖ ≤2*ε :=by
       let b:=Q.focus (L a) k v; let g:= ans2 u b; let G:= ans2 u (Q.arc a b) x
       obtain ⟨δ,hδ,hR⟩:= centred u b a x hv H.h ε he; let t:=min (δ/2) (dist (0:E4) x/2); have ht0:0< dist (0:E4) x:=dist_pos.mpr (Ne.symm hv); have hh:0<t:=lt_min (half_pos hδ) (half_pos ht0); have h₁:t<δ:=lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ); let A':= Metric.closedBall x t; have ht : 0∉A':=fun h=> (not_le.mpr ((min_le_right ..).trans_lt (half_lt_self ht0))) (Metric.mem_closedBall.mp h)
       filter_upwards [smaller (show 0<t/203 from by positivity) hp] with j hj ℓ he'
       let s:= C.S.spacing ℓ; have hP:0 < s:= space0 ..; filter_upwards [pricedQ hφ H w (L a) v (fun _=>v) tendsto_const_nhds A' (isCompact_closedBall _ _) ht (ε*s) (mul_pos he hP)] with i hi m n hN
       let V':= stemV P k m (L a) v
       obtain ⟨f,hf,hF,h⟩:= moneyM V' a (penC C.S j ℓ x) (W m) hN
       change ‖(W m) _-G‖≤_; rw[h]; refine purseL f _ _ G hf hF fun i'=>?_
       let J':= spotB C.S j ℓ n x i'.val; let Y':=ratioTo C.S n ℓ • Lattice.step (S:=ℤ) a; let U(z):=digit (C.S.spacing n) z; let z:= U J'
       obtain ⟨h₁p,h₂p⟩:= flanks a J' hN; change U (J'+Y')=z+s • basis a at h₁p; change U (J'-Y')= z-s • basis a at h₂p; have hv:= show dist z x ≤ 202*C.S.spacing j from fleck he' hN i'.val i'.property
       have h_: ‖s • basis a‖=s:=by rw[norm_smul,basis_norm,mul_one, Real.norm_of_nonneg hP.le]
       have hA': dist (z+s • basis a) x ≤t :=by
            rw [dist_eq_norm,add_comm z, add_sub_assoc]; refine (norm_add_le ..).trans ?_; rw [h_,← dist_eq_norm]; have ht':s ≤ C.S.spacing j:=spacing_antitone C.S he'; linarith only [hj,hv,ht']
       have hB': dist (z-s • basis a) x≤t:=by
            rw[dist_eq_norm, sub_eq_add_neg z, add_comm z,add_sub_assoc]; refine (norm_add_le ..).trans ?_; rw[norm_neg,h_, ← dist_eq_norm]; have ht':s ≤ C.S.spacing j:=spacing_antitone C.S he'; linarith only [hj,hv,ht']
       change ‖(s⁻¹/2) • ((W m) (V' (J'+Y'))- (W m) (V' (J'-Y'))) -G‖≤ _; refine netted s ε _ _ (g (z+s • basis a)) (g (z-s • basis a)) G hP ?_ ?_ (hR z s hP (lt_of_le_of_lt hA' h₁) (lt_of_le_of_lt hB' h₁)); rw [←h₁p]; exact hi _ (show U (J'+Y')∈ A' from h₁p.symm ▸ hA'); rw [←h₂p]; exact hi _ (show U (J'-Y')∈ A' from h₂p.symm ▸ hB')
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.voiceT
#print axioms YM.Massive.Tarn.Choir.Measures.incomeT
