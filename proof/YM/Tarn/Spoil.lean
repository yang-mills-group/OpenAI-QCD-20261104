import YM.Tarn.Chair
/-! On a cofinal subsequence whole-point continuum atlas, no fake PC conclusions yet.
Used literally below. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir YM.Fir.NoteF Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Choir
include hp hφ hr G
lemma angels: ∃ g:ℕ→ℕ,StrictMono g∧∃ Q: Choir, Q.Harmony P (φ∘g):=by
     obtain ⟨g,hg,⟨A⟩,h',Z,hZ⟩:= signals hp G hr hφ; exact ⟨g,hg,uplift hp hr (hφ.comp hg.tendsto_atTop) hZ A h'⟩
omit hp hφ hr G
variable {Q: Choir}
instance fin (d:ℕ):FiniteDimensional ℂ (Q.level d):= FiniteDimensional.of_surjective (f:= (Q.focus none d).rangeRestrict) ((Q.focus none d).surjective_rangeRestrict) -- args
namespace Harmony
variable (H:Q.Harmony P φ)
include H
omit H in
private lemma mantis {X Y E:Type}[TopologicalSpace X][TopologicalSpace E] {ψ:ℕ→Y→X}{f:ℕ→Y→ E}{t:ℕ→ℕ}{x:X}{b:E}(ht:Tendsto t atTop atTop)(h:seesF ψ f x b): seesF (fun i=> ψ (t i)) (fun i=> f (t i)) x b:=by
     let l:=noteF (fun i=>ψ (t i)) x; have he:Tendsto (fun i:ℕ×Y=> (t i.1,i.2)) l (noteF ψ x):=NoteF.ride (v:=ψ) _ _ (ht.comp beyond) (show Tendsto (fun p:ℕ× Y=>ψ (t p.1) p.2) l (𝓝 x) from approach)
     exact h.comp he
lemma tuned {t:ℕ→ℕ}(ht:Tendsto t atTop atTop): Q.Harmony P (φ∘t) :=by
    refine ⟨H.h,fun n x hx d u v=>?_⟩; let f(i:ℕ)(p:Strings n):= eyeW P d u (φ i) p v; have ht': seesF (fun i=> pollF C n (φ i)) f x (Q.total n x (fun j=> Q.focus (u j) _ (v j))):= H.trueLimit n x hx d u v; let z:= Q.total n x (fun j=> Q.focus (u j) _ (v j)); have hv:= mantis (t:=t) (f:=f) (ψ:=fun i=>pollF C n (φ i)) (b:=z) ht ht'; change seesF (fun i=> pollF C n (φ (t i))) (fun i=> f (t i)) x z; exact hv 
variable (d:Fin n→ℕ)(u:Fin n→Averaging)(v:(i:Fin n)→Label (d i))
lemma picks (x:Points n)(hx:x∈conf n) {f:ℕ→Strings n}(h:Tendsto (fun i=>pollF C n (φ i) (f i)) atTop (𝓝 x)):Tendsto (fun i=> Fields.Limit.evaluation C P d v u (f i) (φ i)) atTop (𝓝 (Q.total n x (fun j=> Q.focus (u j) _ (v j)))):=by
    have he:Tendsto (fun i=>(i,f i)) atTop (Watch C φ x):=NoteF.ride (v:=fun i=>pollF C n (φ i)) _ _ tendsto_id h; have hq:=H.trueLimit n x hx d u v; let A:= Q.total n x (fun j=> Q.focus (u j) _ (v j)); change Tendsto _ atTop (𝓝 A); have hh:=hq.comp he
    change Tendsto (fun i=>eyeW P d u (φ i) (f i) v) atTop (𝓝 A); exact hh
lemma allS (K:Set (Points n))(h:IsCompact K)(hx:K⊆conf n)(ε:ℝ)(ht:0<ε):∀ᶠ i in atTop,∀ y: Strings n,pollF C n (φ i) y∈K→ ‖Fields.Limit.evaluation C P d v u y (φ i)- Q.total n (pollF C n (φ i) y) (fun j=> Q.focus (u j) _ (v j))‖ ≤ ε:=by
     have hV:= compactity (F:=fun x=>Q.total n x (fun j=> Q.focus (u j) _ (v j))) K h ((H.h.smooth _ _).continuousOn.mono hx) (fun p hp=> H.trueLimit n p (hx hp) d u v) ε ht; exact hV.mono fun i h y hp=> by rw [← dist_eq_norm]; exact h y hp
lemma exposed (V:ℕ→(i:Fin n)→ Label (d i))(ht:Tendsto V atTop (𝓝 v))(x:Points n)(hx:x∈conf n): Exposes C φ (fun i p=> eyeW P d u (φ i) p (V i)) x (Q.total n x (fun j=> Q.focus (u j) _ (v j))):= by
    let K:= (Q.total n x).compLinearMap fun j=> Q.focus (u j) (d j); exact Lantern.horizons (fun i=> lid (d i)) _ K (fun i=> H.trueLimit n x hx d u (fun j=> lid _ (i j))) _ _ (ht.comp beyond)
end Harmony
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.angels
#print axioms YM.Massive.Tarn.Choir.Harmony.tuned
#print axioms YM.Massive.Tarn.Choir.Harmony.exposed
#print axioms YM.Massive.Tarn.Choir.fin
