import YM.Shade.Reeds
import YM.Shade.Gains
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

private lemma duet_noteR {X Y U V:ℂ}{ε:ℝ}(h:‖X-U‖≤2*ε)(ht:‖Y-V‖≤2*ε)(hD:‖X-Y‖≤ε):‖U-V‖≤ 5*ε:=by rw [← sub_add_sub_cancel U X V, ← sub_add_sub_cancel X Y V]; linarith only [norm_add_le (U-X) (X-Y+(Y-V)), norm_sub_rev U X, norm_add_le (X-Y) (Y-V),h,ht,hD]
local notation "Γ"=> MassFields.isotropic
local notation "L" a:arg=> MassFields.atVector a
variable {K:ℕ}(z:Label K)(a:Axis)
local notation "u"=>Q.focus (L a) K z
local notation "F" i:arg=> Massive.Patria.Rolls.nick (C.S.spacing (C.N i))⁻¹ a (Massive.Needle.stemV P K i (MassFields.atVector a) z) -- parentheses exponent check
variable (hD:∀ᶠ j in atTop,∃ ℓ:ℕ,j ≤ ℓ ∧ ∃ f:ℕ→ℝ,Tendsto f atTop (𝓝 0) ∧ ∀ᶠ i in atTop,0 ≤ f i∧Knoll C i j ℓ ((Rolls.nick (C.S.spacing (C.N i))⁻¹ a (stemV P K i (L a) z))-stemV P k i Γ (y i)) Γ (f i))
include hφ H hD hp hr G hx
local notation "V"=> Q.focus Γ k v
local notation "b"=> Q.focus none d w
local notation "c" j:arg=> C.S.spacing j
lemma fundedM (he:x≠0)(ε:ℝ)(hq:0<ε): ‖ans2 b (Q.arc a u) x-ans2 b V x‖ ≤ 5*ε:=by
      obtain ⟨j,⟨⟨⟨⟨⟨Q₃,hq₃,hQ₃⟩,ℓ,hj,L',hL,hL'⟩,hP1⟩,hP2⟩, hX⟩, hV⟩:=((((((G _).pointsP hp hr none (fun _=>w) ⟨_,norm_nonneg _,Eventually.of_forall fun _=>le_rfl⟩).1.and hD).and -- chain nesting!!! and associates via calls; obtain pattern adjust.
                   (incomeT hp hφ H w Γ v y hx x ε hq he)).and (voiceT hp hφ H w z x a ε hq he)).and (smaller (show 0 < ‖x‖/2 from half_pos (norm_pos_iff.mpr he)) hp)).and (hr.high.eventually_ge_atTop 6)|>.exists
      -- check API argument order.B
      let S'(i):= (F i);
      have hl:Tendsto (fun i=>Q₃* L' (φ i)) atTop (𝓝 0):=by simpa only [mul_zero, Function.comp_apply] using (hL.comp hφ).const_mul Q₃
      have Θ:2*c j< ‖x‖:= by linarith only [hX]
      have hv:= windowV hp x j Θ
      suffices hf:∀ᶠ i:ℕ in atTop, ‖ans2 b (Q.arc a u) x-ans2 b V x‖ ≤5*ε by obtain ⟨i,h⟩:=hf.exists; exact h
      filter_upwards [hφ.eventually_ge_atTop 0,hφ.eventually ((hp.uv.tendsto_atTop).eventually_ge_atTop ℓ), hφ.eventually ((hp.uv.tendsto_atTop).eventually_ge_atTop (j+1)),hφ.eventually hv, hφ.eventually hQ₃, hφ.eventually hL', hl.eventually_lt_const hq, hP2 ℓ hj,hP1 ℓ hj] with i _ hx hx' hG hp0 hΦ hq hT hP
      let m:=φ i; let R:=ratioTo C.S (C.N m) ℓ; let M(x':stalk C m):=checkedT Γ R x' (penC C.S j ℓ x); let C':=stemV P k m Γ (y m); let W:= rod2 C m (stem P d m w)
      have he':‖W (M (S' m-C'))‖ ≤ Q₃*L' m:= aloft hp x Γ hj hx hx' (stem P d m w) _ _ _ hp0 hΦ.2 hV hG
      refine duet_noteR (X:=W (M (S' m))) (Y:=W (M C')) (hT hx) (hP hx) ?_; rw [← map_sub]; refine (le_of_eq ?_).trans (he'.trans hq.le); unfold M checkedT; rw [togetherT]; rfl
-- Funding in same authenticated path proves relation all spectators.
lemma bondedA : Q.arc a u= V:=by
     by_contra h; obtain ⟨x,hx',w,hW⟩:= H.h.listens _ (sub_ne_zero.mpr h); obtain ⟨d,p,rfl⟩: ∃ d:ℕ,∃ p:Label d,Q.focus none d p=w:=by obtain ⟨d,q,h⟩:= H.h.absorbs w; exact ⟨d,q,h⟩
     let W:= Q.focus none d p; let s:= Q.arc a u; have he:x≠0:=fun h=>by obtain hh:=hx' 0; rw [h] at hh; simpa using hh
     have ht:=fundedM hp hr hφ H p v y hx x z a hD (G:=G) he
     by_cases hE:ans2 W s x=ans2 W V x
     · let g(q:Q.W):Fin 2→Q.W:=update ![W,s] 1 q; have hg(q):g q= ![W,q]:=by ext1 i; fin_cases i <;> simp [g]
       apply hW; change ans2 W (s-V) x=0; unfold ans2; rw [← hg]; change Q.total 2 (arm x) (update ![W,s] 1 (s-V))=0; rw [(Q.total 2 (arm x)).map_update_sub]; change Q.total 2 (arm x) (g s)- Q.total 2 (arm x) (g V)=0; rw [hg,hg]; exact sub_eq_zero.mpr hE
     let F₁:= ‖ans2 W s x-ans2 W V x‖; have h0:0 < F₁:= norm_pos_iff.mpr (sub_ne_zero.mpr hE); have hR: F₁ ≤5*(F₁/6):= ht (F₁/6) (by positivity); linarith only [h0,hR]
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.bondedA
