import YM.Gust.Ally
import YM.Push.STRESS_FLUX.Charges
import YM.Gust.Comb
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Table Work.A05 Tarn Tarn.Choir UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {Q: Choir}{C: Sequence}{P:Calibration C}{d m n:ℕ}{x:Points (n+1)}{χ:E4→ℝ}{V:E4→E4}
variable (S:Axis→Axis→ Q.W) {F:Pollens P Q}(hP:Foil P Q F)
include hP
lemma detected(u v:Q.W)(h:∀ n:ℕ,∀ p:Fin n→ Q.W,∀ x:Points (n+1),x∈conf _→ headG p x u=headG p x v):u=v:=by
      by_contra hv; obtain ⟨w,hw⟩:= (F.adj timeAxis).surjective (u-v); have hW : w ≠0:= by intro h; rw[h,map_zero] at hw; exact hv (sub_eq_zero.mp hw.symm)
      obtain ⟨r,hR,hx⟩:= hP.realPair timeAxis w hW
      let s:= r • basis timeAxis; let q:= points (![0,s]); have he: q∈conf _:=by
          have hS:s≠0:=by
             intro h; have hE:r=(0:ℝ):=by simpa [s] using congr_arg (fun i:E4=> i timeAxis) h
             exact hR.ne' hE
          intro i j h; fin_cases i <;> fin_cases j <;> simp [q,hS,Ne.symm hS] at * -- norm
      rw [hw] at hx; have H:headG ![w] q (u-v) =0:=by rw [map_sub,h _ _ _ he,sub_self]
      rw [heads] at H; exact hx.ne' H
lemma cap_eq (A B Z:Q.W)(hq:Captures Q S V Z A)(ht:Captures Q S V Z B):A=B:= detected hP A B (fun n p x hx=>by obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx; rw[← hq n _ _ hx hχ, ← ht n _ χ hx hχ p])
structure Axle (Q: Choir)(S:Axis→Axis→Q.W) where
   jet : Ortho.Skew→Q.W→ₗ[ℂ]Q.W
   landed d (h:8 ≤ d) g u (hu:u∈Q.level d): jet g u∈Q.level d
   relation g u: Captures Q S (M4.move g.val) u (jet g u)
variable (hQ:Q.Domestic)(T:∃ J:Axis→Axis→ UV.Label 8, ∀ a b, Q.focus none 8 (J a b)= S a b)(hT:Safe Q S)
variable (hE:∀ a b,F.parity (S a b)= S a b) (hO:∀ d,8≤d→Orb P Q d F) {β e:ℝ}(hp:C.Path β e)
open UV Poised Plans Plans.Stamp Intag Intag.Vale Needle Patria.Hub
open Patria Patria.Depth
variable (G:∀ d,Cottage P d) (hs:Sway C.S)
include hQ T hT hE hO hp G hs
lemma heartG: Nonempty (Axle Q S) :=by
      have h(g:Ortho.Skew)(d:ℕ)(h:8≤d)(u:Q.W)(ht:u∈ Q.level d):= surge (StressFlux.Annular.turn g) S hQ T hT hP hE (StressFlux.Annular.turn_motion g) (hO d h) hp G hs u ht
      have he(g:Ortho.Skew)(v:Q.W):∃ u,Captures Q S (M4.move g.val) v u:=by obtain ⟨d,ht⟩:= hQ.absorbs v; obtain ⟨p,hp,hq⟩:= h g (max 8 d) (le_max_left ..) v (hQ.slope (le_max_right 8 d) ht); exact ⟨p,hq⟩
      choose Y hY using he
      have hf(g:Ortho.Skew)(b:Axis):= ((StressFlux.Annular.turn_motion g).smooth b).continuous
      refine ⟨⟨fun g=>{toFun:=Y g,map_add':=fun u v=>cap_eq S hP _ _ _ (hY g _) (cap_plus _ S hQ (hf g) _ _ (hY g u) _ _ (hY g v)),map_smul':=fun c u=>cap_eq S hP _ _ _ (hY g _) (cap_scale _ S hQ (hf g) _ _ (hY g u) c)},fun d hd g u hu=>?_, hY⟩⟩
      obtain ⟨Z,ht,hS⟩:=h g d hd u hu; change Y g u∈ Q.level d; exact (cap_eq S hP _ _ u hS (hY g u)) ▸ ht
end YM.Massive.Gust
#print axioms YM.Massive.Gust.heartG
