import YM.Shade.Reeds
import YM.Shade.Belt
import YM.Avian.Wrens
import YM.Shade.Ozone
import YM.Tarn.Spoil
import YM.Alum.Chord
/-!
   Exact anchored penny stacks for central matched-PC layer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale GaugeP Rolls
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {k i j ℓ n:ℕ}{X:Type} [AddCommGroup X][Module ℝ X]
local notation "αᴺ"=> C.S.spacing (C.N i)
local notation "s" j:arg=> C.S.spacing j
local notation "Γ"=> MassFields.isotropic
lemma cornM (h:stalk C i)(a:Axis)(x:Cover)(U₁ Ω₁:Averaging)(hG: Rolls.Goes a U₁ Ω₁) (Q: Insertion (C.S.side (C.R i) (C.N i)) 6 →ₗ[ℝ] X) (hJ:ℓ ≤ C.N i):∃ f:↥(Lattice.box (flex C.S ℓ (C.N i)))→ℝ,(∀ i,0 ≤ f i)∧(∑ i,f i)= 1 ∧ Q (CardsT.checkedT Ω₁ (ratioTo C.S (C.N i) ℓ) (Rolls.nick αᴺ⁻¹ a h) x) = ∑ i':↥(Lattice.box (flex C.S ℓ (C.N i))), f i' • (((s ℓ)⁻¹/2) • (Q (h (ratioTo C.S (C.N i) ℓ • x+i'.val+ratioTo C.S (C.N i) ℓ • step a))-Q (h (ratioTo C.S (C.N i) ℓ • x+i'.val-ratioTo C.S (C.N i) ℓ • step a)))):=by
      let J:=ratioTo C.S (C.N i) ℓ; let u:=J • x; let b:Cover:= J • Lattice.step a; let F(x):= h (x+b); let G(x):= h (x+ -b)
      have hK : CardsT.checkedT Ω₁ J (nick αᴺ⁻¹ a h) x=((s ℓ)⁻¹/2) • CardsT.checkedT U₁ J (F-G) x:=by
           unfold checkedT; rw [walks h a U₁ Ω₁ hG x hJ,togetherT, smul_add, smul_sub J x,Pi.sub_apply]; unfold F G; rw [filtra,filtra, sub_eq_add_neg (J • x)]
      obtain ⟨f,hf,h1,hT⟩:=strummed C.S x U₁ (F-G) hJ; refine ⟨f,hf,h1,?_⟩; change Q (checkedT Ω₁ J _ x)=_; rw [hK]; unfold checkedT; change Q (_ • Averaging.filter U₁ (ratioTo C.S (C.N i) ℓ) (F-G) _)=_; rw [hT,map_smul,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i' _; rw [map_smul,Pi.sub_apply, map_sub, smul_comm]; unfold F G; rw [← sub_eq_add_neg (ratioTo C.S (C.N i) ℓ • x+i'.val)]
end YM.Massive.Needle
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
local notation "J" i:arg=> (C.N i)
local notation "Γ"=> MassFields.isotropic
local notation "L" a:arg=> MassFields.atVector a
local notation "u"=> Q.focus none d w
local notation "c" i:arg=> C.S.spacing i
local notation "W" i:arg=> rod2 C i (stem P d i w)
variable (a:Axis)(ε:ℝ)(he:0 < ε)(hv:x≠0)
include hφ hp he hv H
lemma windT (V:Averaging)(T:Averaging)(hg: Patria.Rolls.Goes a V T) : ∀ᶠ j in atTop,∀ ℓ:ℕ,j≤ℓ →∀ᶠ i in atTop, let m:=φ i; let h:=C.N m; ℓ ≤ h → ‖(W m) (checkedT T (ratioTo C.S h ℓ) (Rolls.nick ((C.S.spacing h)⁻¹) a (stemV P k m V v)) (penC C.S j ℓ x)) - ans2 u (Q.arc a (Q.focus V k v)) x‖ ≤2*ε :=by
       let b:=Q.focus V k v; let g:= ans2 u b; let G:= ans2 u (Q.arc a b) x
       obtain ⟨δ,hδ,hR⟩:= centred u b a x hv H.h ε he; let t:=min (δ/2) (dist (0:E4) x/2); have ht0:0< dist (0:E4) x:=dist_pos.mpr (Ne.symm hv); have hh:0<t:=lt_min (half_pos hδ) (half_pos ht0); have h₁:t<δ:=lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ); let A':= Metric.closedBall x t; have ht : 0∉A':=fun h=> (not_le.mpr ((min_le_right ..).trans_lt (half_lt_self ht0))) (Metric.mem_closedBall.mp h)
       filter_upwards [smaller (show 0<t/203 from by positivity) hp] with j hj ℓ he'
       let s:= C.S.spacing ℓ; have hP:0 < s:= space0 ..; filter_upwards [pricedQ hφ H w V v (fun _=>v) tendsto_const_nhds A' (isCompact_closedBall _ _) ht (ε*s) (mul_pos he hP)] with i hi m n hN
       let V':= stemV P k m V v
       obtain ⟨f,hf,hF,h⟩:= cornM V' a (penC C.S j ℓ x) V T hg (W m) hN
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

#print axioms YM.Massive.Tarn.Choir.Measures.windT
