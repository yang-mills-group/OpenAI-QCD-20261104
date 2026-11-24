import YM.Tarn.Vance
/-! Calibrated pre-real orientation in all conventions including tensor jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Dispersed
open Function QCD QCD.Lat QCD.RP QCD.Tide Lyre Grass Wilson Patria Patria.Depth Patria.Hub Patria.Exposure Lattice Cylinder
open TorusPCAC.Geometry TorusPCAC.Geometry.AxisB MeasureTheory Massive.UV MoveR Needle
open Fir YM.Fir Filter
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} (hQ:P.System) {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q:Choir}{φ:ℕ→ℕ}(h:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
variable (d:Fin n→ℕ)(u:(i:Fin n)→Label (d i))(g:Fin n→ Averaging)
set_option quotPrecheck false
local notation "R" i:arg=> (C.A i).regulator
local notation "Dg" i:arg=> C.S.side (C.R i) (C.N i)
abbrev penS (d:Fin n→ℕ) (u:(i:Fin n)→Label (d i)) (g:Fin n→ Averaging) (Q: Choir)(x:Points n):= Q.total n x (fun i=> Q.focus (g i) _ (u i))
variable {d u g}
lemma corners (s:Signed)(f:Equiv.Perm (Fin n))(x:ℕ→ Strings n)(y:Points n)(hy:Tendsto (fun i=>pollF C n (φ i) (x i)) atTop (𝓝 y)): Tendsto (fun i=> pollF C n (φ i) (fun j=> s.act (x i (f j)))) atTop (𝓝 (points fun j=> Ortho.move s.ortho (y (f j)))):=by
     let T (p:Points n):=points fun i=> Ortho.motion s.ortho (p (f i)); have he:Continuous T:=by unfold T points; fun_prop
     exact ((he.tendsto y).comp hy).congr (fun i=>by ext1 j; change Ortho.motion s.ortho (_ • vector (x i (f j)))=_; rw [map_smul,Canvas.motion_site]; rfl)
include hp hφ h
private lemma earns(d d': Fin n→ℕ)(u:(i:Fin n)→ Label (d i))(u':(i:Fin n)→Label (d' i))(g g': Fin n→Averaging)(k:ℂ→ ℂ)(hk:Continuous k)(τ:ℕ→ Strings n→Strings n)(x y:Points n)(hx:x∈conf n)(hy:y∈conf n)(hf:∀ᶠ i in atTop,∀ p:Strings n,gaze (P:=P) d' u' g' (τ i p) i=k (gaze (P:=P) d u g p i))(H:∀ f:ℕ→ Strings n, Tendsto (fun i=> pollF C n (φ i) (f i)) atTop (𝓝 x) → Tendsto (fun i=>pollF C n (φ i) (τ (φ i) (f i))) atTop (𝓝 y)): penS d' u' g' Q y=k (penS d u g Q x):=by
     obtain ⟨X,hX⟩:= visions hp hφ x
     apply tendsto_nhds_unique (h.picks d' g' u' y hy (H X hX)); exact ((hk.tendsto _).comp (h.picks d g u x hx hX)).congr' ((hφ.eventually hf).mono fun i hi=> (hi (X i)).symm)
variable (d u g) (x:Points n)(hx:x∈conf n)
include hQ hx
lemma motion_f (z:E4): penS d u g Q (points fun i=> x i+z)=penS d u g Q x:=by
     let y(i):=bead (C.S.spacing (C.N i)) z; refine earns hp h hφ d d u u g g id continuous_id (fun i b=> b+ fun _=>y i) x _ hx ?_ (pie hQ ..) (fun f hf=>?_)
     · exact Points.across_in z hx
     have hu:Tendsto (fun i=> digit (C.S.spacing (C.N (φ i))) (y (φ i))) atTop (𝓝 z):=(approaches hp z).comp hφ
     let F(v:Points n×E4):=points fun i=> v.1 i+v.2; have hh:Continuous F:=by unfold F points; fun_prop
     exact ((hh.tendsto (x,z)).comp (hf.prodMk_nhds hu)).congr fun i=>by ext1 j; exact (digit_plus ..).symm -- defeq
lemma adjustF (a:Axis): penS (fun i:Fin n=>d i.rev) (fun i=> P.sym.adj _ a (u i.rev)) (fun i=>g i.rev) Q (points fun i=> Ortho.move (Signed.reflect a) (x i.rev)) = star (penS d u g Q x):=by
    let s:=Signed.mirror a; exact earns hp h hφ d _ u _ g _ star continuous_star (fun _ b=> s.act ∘ b ∘ Fin.rev) x _ hx (Points.move_in (Signed.reflect a) (Points.rearrange_in Fin.revPerm hx)) (heard hQ d u g a) (fun f hf=> corners s Fin.revPerm f x hf)
lemma spinning (s:Signed)(p:EuPin)(ht:p.Lifts s): penS d (fun i=> P.sym.pin _ p (u i)) (Averaging.permute s ∘g) Q (points fun i=>Ortho.move p.coord (x i))=penS d u g Q x:=by
     rw [show p.coord=s.ortho from ht]; exact earns hp h hφ d d u _ g _ id continuous_id (fun _ B=> s.act ∘ B) x _ hx (Points.move_in _ hx) (pinS hQ d u g s p ht) (fun f hf=> corners s (Equiv.refl _) f x hf)
lemma flavored (v:FlavorTorus) : penS d (fun i=> P.sym.flavor _ v (u i)) g Q x=penS d u g Q x:= earns hp h hφ _ _ _ _ _ _ id continuous_id (fun _=>id) _ _ hx hx (flavorS hQ d u g v) (fun _ hx=>hx)
lemma parityed : penS d (fun i=> P.sym.parity _ (u i)) g Q x=penS d u g Q x:= earns hp h hφ _ _ _ _ _ _ id continuous_id (fun _=>id) _ _ hx hx (parityS hQ d u g) (fun _ hx=>hx)
lemma chargeed : penS d (fun i=> P.sym.charge _ (u i)) g Q x=penS d u g Q x:= earns hp h hφ _ _ _ _ _ _ id continuous_id (fun _=>id) _ _ hx hx (chargeS hQ d u g) (fun _ hx=>hx)
end YM.Massive.Tarn.Dispersed
#print axioms YM.Massive.Tarn.Dispersed.adjustF
#print axioms YM.Massive.Tarn.Dispersed.motion_f
#print axioms YM.Massive.Tarn.Dispersed.chargeed
#print axioms YM.Massive.Tarn.Dispersed.spinning
#print axioms YM.Massive.Tarn.Dispersed.flavored
