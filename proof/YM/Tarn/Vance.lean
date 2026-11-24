import YM.Tarn.Stamen
/-! Volume receipt pullback for calibrating family transforms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Dispersed
open Function QCD QCD.Lat QCD.RP QCD.Tide Lyre Grass Wilson Patria Patria.Depth Patria.Hub Patria.Exposure Lattice Cylinder
open TorusPCAC.Geometry TorusPCAC.Geometry.AxisB MeasureTheory Massive.UV MoveR Needle
open Fir YM.Fir Filter
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} (hQ:P.System) {β e:ℝ}(hp:C.Path β e) {n:ℕ}
variable (d:Fin n→ℕ)(u:(i:Fin n)→Label (d i))(g:Fin n→ Averaging)
set_option quotPrecheck false
local notation "R" i:arg=> (C.A i).regulator
abbrev gaze (d:Fin n→ℕ)(u:(i:Fin n)→Label (d i))(g:Fin n→ Averaging)(b: Strings n)(i:ℕ):= Fields.Limit.evaluation C P d u g b i
variable (c:ℕ→ Cover→ Cover)(L: ∀ d,Label d≃ₗ[ℂ]Label d) (K: Averaging→ Averaging)
set_option quotPrecheck false
local notation "Dg" i:arg=> C.S.side (C.R i) (C.N i)
private lemma bout(F: (i:ℕ)→Density (C.S.side (C.R i) (C.N i)) 6→ Density (C.S.side (C.R i) (C.N i)) 6)(HF:∀ i,Nonempty (Crest (R i) (F i)))(HG:∀ᶠ i in atTop, ∀ k:Fin n,∀ b:Cover,F i ⇑(P.physical (g k) i (u k) b)=P.physical (K (g k)) i (L _ (u k)) (c i b)):∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) d (fun i=> L _ (u i)) (K ∘g) (c i∘ b) i= gaze (P:=P) d u g b i:=HG.mono (fun i hi b=>by
      let x(k:Fin n):= P.physical (g k) i (u k) (b k); let y(k:Fin n):= P.physical (K (g k)) i (L _ (u k)) (c i (b k)); obtain ⟨T⟩:=HF i; change (R i).average (List.ofFn y).prod=(R i).average (List.ofFn x).prod; rw[List.ofFn_eq_map,List.ofFn_eq_map]; exact T.skies _ x y (fun j _=>hi j (b j)))
include hQ
lemma pie(z:ℕ→ Cover):∀ᶠ i in atTop,∀ b: Strings n,gaze (P:=P) d u g (b+fun _=>z i) i= gaze (P:=P) d u g b i:=by
    refine bout d u g (fun i b=> b+z i) (fun d=>LinearEquiv.refl ..) id (fun i=> march (z i)) (fun i=>MoveR.marchP (R i) rfl _) (Eventually.of_forall fun i j b=>?_)
    unfold Calibration.physical; let F(k:Cover) (v:Label (d j)):= (show ⇑(P.candidate (d j) (Dg i) k v)=(fun U=>places k (P.localMap _ v) U) from funext fun x=>hQ.sections.localizes (d j) (Dg i) k v x); rw [F,F]; exact Patria.Canvas.stylus ..
lemma pinS (s:Signed)(p:EuPin)(he:p.Lifts s):∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) d (fun j=> P.sym.pin _ p (u j)) (Averaging.permute s∘ g) (s.act ∘ b) i= gaze (P:=P) d u g b i:=by
    refine bout d u g (fun i=> s.act) (fun d=>P.sym.pin d p) _ (fun _=>Action.pin p s) (fun i=>pinP _ rfl _ _ he) ?_; filter_upwards [eventually_all.mpr fun k:Fin n=> hQ.mixing (d k)] with i h k b; unfold Calibration.physical; rw[hQ.sections.pin (d k) _ _ _ p s he,(h k).pin _ _ p s he]
lemma flavorS (p:FlavorTorus) :∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) d (fun j=> P.sym.flavor _ p (u j)) g b i= gaze (P:=P) d u g b i:=by
    refine bout d u g (fun _=> id) (fun d=>P.sym.flavor d p) id (fun _=>Action.flavor p) (fun i=> flavorP _ p) ?_; filter_upwards [eventually_all.mpr fun k:Fin n=> hQ.mixing (d k)] with i h k b; have ht:= DFunLike.congr_fun ((h k).flavor (g k) p) (u k); unfold Calibration.physical; rw [hQ.sections.flavor]; change ⇑(P.candidate (d k) _ b ((P.sym.flavor (d k) p* P.mix (d k) (g k) i) (u k)))=_; rw [ht]; rfl
lemma parityS  :∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) d (fun j=> P.sym.parity _ (u j)) g b i= gaze (P:=P) d u g b i:=by
    refine bout d u g (fun _=> id) (fun d=>P.sym.parity d) id (fun _=>Action.parity) (fun i=> parityP _) ?_; filter_upwards [eventually_all.mpr fun k:Fin n=> hQ.mixing (d k)] with i h k b; have ht:= DFunLike.congr_fun ((h k).parity (g k)) (u k); unfold Calibration.physical; rw [hQ.sections.parity]; change ⇑(P.candidate (d k) _ b ((P.sym.parity (d k)* P.mix (d k) (g k) i) (u k)))=_; rw [ht]; rfl
lemma chargeS  :∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) d (fun j=> P.sym.charge _ (u j)) g b i= gaze (P:=P) d u g b i:=by
    refine bout d u g (fun _=> id) (fun d=>P.sym.charge d) id (fun _=>Action.charge) (fun i=> chargeP _) ?_; filter_upwards [eventually_all.mpr fun k:Fin n=> hQ.mixing (d k)] with i h k b; have ht:= DFunLike.congr_fun ((h k).charge (g k)) (u k); unfold Calibration.physical; rw [hQ.sections.charge]; change ⇑(P.candidate (d k) _ b ((P.sym.charge (d k)* P.mix (d k) (g k) i) (u k)))=_; rw [ht]; rfl
lemma heard (a:Axis) : ∀ᶠ i in atTop,∀ b:Strings n,gaze (P:=P) (fun j=>d j.rev) (fun j=> P.sym.adj _ a (u j.rev)) (fun j=>g j.rev) ((Signed.mirror a).act ∘ b ∘ Fin.rev) i= star (gaze (P:=P) d u g b i):=by
      filter_upwards [eventually_all.mpr fun k:Fin n=> hQ.mixing (d k)] with i h b; let x(k:Fin n):= P.physical (g k) i (u k) (b k); let y(k:Fin n):= P.physical (g k) i (P.sym.adj _ a (u k)) ((Signed.mirror a).act (b k)); have he(k:Fin n):Action.adj a (x k)=y k:=by unfold x y Calibration.physical; rw[hQ.sections.star,(h k).star]; -- cfg
      change (R i).average (List.ofFn (fun k: Fin n=> y k.rev)).prod= star ((R i).average (List.ofFn x).prod); rw [show List.ofFn (fun k:Fin n=>y k.rev)=(List.ofFn y).reverse from UV.Free.Lyre.reversesV y,List.ofFn_eq_map,List.ofFn_eq_map,←List.map_reverse]; exact MoveR.strums _ rfl _ _ _ _ fun j _=> he j
end YM.Massive.Tarn.Dispersed
#print axioms YM.Massive.Tarn.Dispersed.pie
#print axioms YM.Massive.Tarn.Dispersed.pinS
#print axioms YM.Massive.Tarn.Dispersed.chargeS
#print axioms YM.Massive.Tarn.Dispersed.flavorS
#print axioms YM.Massive.Tarn.Dispersed.parityS
#print axioms YM.Massive.Tarn.Dispersed.heard
