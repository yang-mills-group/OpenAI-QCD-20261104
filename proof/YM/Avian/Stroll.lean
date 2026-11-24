import YM.Shade.Aster
import YM.Avian.Sage
/-! Mixed route. Pays grouped derivative at every rank. -/
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
set_option maxHeartbeats 800000
open Finset
variable {d k:ℕ}(w:Label d)(r:Averaging)(v:Label k)(y:ℕ→Label k)(hx:Tendsto y atTop (𝓝 v)) (A:Set E4)(x:E4)
noncomputable def topL (x:E4)(w:Q.W):Q.W→ₗ[ℂ]ℂ:= {
   toFun:=fun v=> ans2 w v x,map_add':=fun v z=>by
      let X(t:Q.W):=update ![w,v] 1 t; have hv(t): X t=![w,t]:=by ext1 i; fin_cases i <;> simp [X]
      unfold ans2; simp_rw[← hv]; exact (Q.total 2 (arm x)).map_update_add _ _ _ _,map_smul':=fun t v=>by
      let X(s:Q.W):=update ![w,v] 1 s; have he(s): X s=![w,s]:=by ext1 i; fin_cases i<;> simp[X]
      unfold ans2; simp_rw[← he]; exact (Q.total 2 (arm x)).map_update_smul _ _ _ _ }
-- swings: summed input motion same Omega at output.
variable (L:ℕ→ℕ)(F:ℕ)(V:Averaging)(R: Axis→ Averaging)(z:Axis→Label F)(m:ℕ)
local notation "Δ" a:arg i:arg=> Rolls.nick (C.S.spacing (C.N i))⁻¹ a (stemV P F i (R a) (z a))
local notation "Sr"=> ∑ a:Axis,(fun i:ℕ=>Δ a i)
local notation "U" => ∑ a:Axis,Q.arc a (Q.focus (R a) F (z a))
variable (Θ:SourceRead.TaperHol)(hR:∀ a,Rolls.Goes a (R a) V)(he:∀ i,i≤L i)(ht:Weave P L Θ m V (∑ a:Axis,(fun i=>Rolls.nick (C.S.spacing (C.N i))⁻¹ a (stemV P F i (R a) (z a)))) y)
include hx H hφ hR hp
local notation "VQ"=> Q.focus V k v
local notation "b"=> Q.focus none d w
local notation "c" j:arg=> C.S.spacing j
include hr G he ht
lemma nectar (hK:x≠0)(ε:ℝ)(hq:0<ε): ‖ans2 b (U) x-ans2 b VQ x‖ ≤ 11*ε :=by
     let f a i:= Δ a i; let S(i:ℕ):=∑ a:Axis,f a i; let W(a):=Q.arc a (Q.focus (R a) F (z a))
     obtain ⟨j,⟨⟨⟨⟨⟨Q₃,hq₃,hQ₃⟩,A,hA,hL⟩, hP1⟩, hP2⟩, hX⟩, hV⟩:=((((((G _).pointsP hp hr none (fun _=>w) ⟨_,norm_nonneg _,Eventually.of_forall fun _=>le_rfl⟩).1.and ht.lands).and
               (incomeT hp hφ H w V v y hx x ε hq hK)).and (eventually_all.mpr (fun a:Axis=> windT hp hφ H w (z a) x a ε hq hK (R a) V (hR a)))).and (smaller (show 0 < ‖x‖/2 from half_pos (norm_pos_iff.mpr hK)) hp)).and (hr.high.eventually_ge_atTop 6)|>.exists
     let ℓ:= L j; let B:=ans2 b VQ x; have hG: Tendsto (fun i=> Q₃*A (φ i)) atTop (𝓝 0):=by simpa using (hA.comp hφ).const_mul Q₃
     have Θ:2*c j< ‖x‖:= by linarith only [hX]
     have hv:= windowV hp x j Θ; have hj:j ≤ ℓ:= he j
     suffices hf:∀ᶠ i:ℕ in atTop, ‖ans2 b (U) x- B‖ ≤11*ε by obtain ⟨i,h⟩:=hf.exists; exact h
     filter_upwards [hφ.eventually_ge_atTop 0,hφ.eventually ((hp.uv.tendsto_atTop).eventually_ge_atTop ℓ), hφ.eventually ((hp.uv.tendsto_atTop).eventually_ge_atTop (j+1)),hφ.eventually hv, hφ.eventually hQ₃, hφ.eventually hL, hG.eventually_lt_const hq, eventually_all.mpr (fun a=>hP2 a ℓ hj),hP1 ℓ hj] with i _ hx hx' hG hp0 hΦ hq hT hP
     let m':=φ i; let t:=ratioTo C.S (C.N m') ℓ; let o:=penC C.S j ℓ x; let J(g:stalk C m'):=checkedT V t g o; let Gv:= stemV P k m' V (y m'); let M:= rod2 C m' (stem P d m' w); let Y:= M (J (S m')); let Zv:= M (J Gv); let Fg(a):=M (J (f a m')); let H'(a):= ans2 b (W a) x
     have hΦ': Knoll C m' j ℓ (S m'-Gv) V (A m'):=by
          let K:= ht.lands; have hp:= hΦ.2; rw [Finset.sum_apply] at hp; exact hp
     have h1:‖Y-Zv‖ ≤ ε:=by
           unfold Y Zv; rw [←map_sub]; have he : J (S m')-J Gv=J (S m'-Gv):=by unfold J checkedT; rw[togetherT]; rfl
           rw [he]; exact (aloft hp x V hj hx hx' (stem P d m' w) _ _ _ hp0 hΦ' hV hG).trans hq.le
     have ht': Y=∑ i:Axis,Fg i:=by
           unfold Y S; unfold J checkedT; rw [Rolls.accumulate, map_sum]; rfl
     have h2:‖ans2 b (U) x - Y‖ ≤ 8*ε:=by
           change ‖topL x b (U)-Y‖ ≤ _; rw [map_sum,ht',← sum_sub_distrib]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun _=>2*ε) (fun a _=>?_)).trans_eq ?_ ; rw [norm_sub_rev]; exact hT a hx; simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; ring -- exact mod Axis
     rw [← sub_add_sub_cancel _ Y B,←sub_add_sub_cancel Y Zv]; have hb:‖Zv-B‖ ≤ 2*ε:=hP hx
     linarith only[norm_add_le (ans2 b (U) x-Y) (Y-Zv+(Zv-B)), norm_add_le (Y-Zv) (Zv-B),h1,h2,hb]
lemma coupled : (U)= VQ:=by
     by_contra h; obtain ⟨x,hx',w,hW⟩:= H.h.listens _ (sub_ne_zero.mpr h); obtain ⟨d,p,rfl⟩: ∃ d:ℕ,∃ p:Label d,Q.focus none d p=w:=by obtain ⟨d,q,h⟩:= H.h.absorbs w; exact ⟨d,q,h⟩
     let W:= Q.focus none d p; let s:= ∑ a:Axis,Q.arc a (Q.focus (R a) F (z a)); have hc:x≠0:=fun h=>by obtain hh:=hx' 0; rw [h] at hh; simpa using hh
     let t:=topL x W; have hm:t (s-VQ)≠0:=hW; rw [map_sub] at hm; let x':= ‖t s-t VQ‖; have h0:0<x':=norm_pos_iff.mpr hm
     have hf:x' ≤ 11*(x'/12):=nectar hp hr hφ H p v y hx x L F V R z m Θ hR he ht hc _ (by positivity) (G:=G)
     linarith only[h0,hf]
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.coupled
