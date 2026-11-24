import YM.Bwana.Colors
/- pairs & possible placeholder c. Mark that is translated freely on full cutoff. Tide real. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth.Off
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Plans Display Orientation Exposure Rolls Canvas
variable {S:Scheme}{r:Side}{N J d i j m k:ℕ}(A:Run S N r 6)(H:SourceRead.TaperHol)(sym:RawSym) (B:Bore d)(hf:Rubric sym B) (hA:A.Actual)
variable (u v w:Label d)(b:ℕ→ Cover)(hB:Borders S m N b)(q:Bool)(hp:moored u.val q) (he:moored v.val false) -- c optional
local notation "T"=>S.side r N
local notation "B0"=> B (S.side r N)
noncomputable def comet (c:Side)(N:ℕ)(x:Cover)(z:ℝ): Insertion c 6:= (z:ℂ) • (B c x u * B c (b N+x) v)
variable (z:ℝ)
local notation "F" x:arg=> comet B u v b T N x z
include hf
lemma comet_shift (x y:Cover) : march y (F x)= F (x+y):=by
       have h(x:Cover)(u:Label d):march y (B0 x u)=B0 (x+y) u:=hf.advances T u x y
       let A₀:= TorusPCAC.Geometry.crank 1 1 (wrap T y) (TorusPCAC.Geometry.heat y) (N:=6); funext V
       let x':= pull 1 (wrap T y) V -- pull namespace
       change A₀ ((z:ℂ) •(B0 x u x'* B0 (b N+x) v x'))= _; change A₀.toLinearMap _=_; rw [map_smul] -- likely no pattern via A₀.toLinearMap. use AlgHom map_smul
       change ((z:ℂ) • A₀ _) = _; rw[map_mul]; exact congr_arg ((z:ℂ) • ·) (congr_arg₂ HMul.hMul (congr_fun (h x u) V) (congr_fun (h (b N+x) v) V|>.trans (by rw[add_assoc])))
include hA
lemma activeV (hx:i≤ N): TideT A none i (trolley A (fun x=>comet B u v b (S.side r N) N x z) none):= wingG A hA _ _ hx (fun a c=> comet_shift (N:=N) (r:=r) (S:=S) sym B hf u v b z a c)
local notation "G"=> trolley A (fun x=>comet B u v b (S.side r N) N x z) none
include hp he
lemma homV(x:Cover)(V:Grid (S.side r N)):QCD.Grass.Hom q ((F x) V):=by
       change QCD.Grass.Hom q ((z:ℂ) •(B0 x u V* B0 _ v V)); apply Hom.smul; exact Bool.xor_false q ▸ (Hom.mul (Hub.fade _ _ hf u q hp _ V) (Hub.fade _ _ hf v false he _ V))
omit hp
-- orientation read at any m via Test.Full.Pulse.Sensor.Y.O.P.requires x proper orientation of c & f. Check adjCoef (z ℝ)
variable (a:Axis)(he':i ≤ N)(w_:Label d)(K:Market S r d)(hW:Wager A H B K i)(ht:Tally H 0 w_ (A.density i) (trolley A (fun x=>comet B u v b (S.side r N) N x z) none i 0))
include he' hW ht
set_option maxHeartbeats 560000 in
lemma fluxE : Tally H 0 (sym.adj _ a w_) (A.density i) (trolley A (fun x=> comet B (sym.adj _ a u) (sym.adj _ a v) (fun i=> (Signed.mirror a).act (b i)) (S.side r N) N x z) none i 0):=by
       let g:= T; let x:= b N; let Q:= Signed.mirror a; let U₁:= sym.adj _ a u; let V₁:= sym.adj _ a v
       have hx:Action.adj a ⇑(comet B u v b (S.side r N) N 0 z)=⇑(comet B U₁ V₁ (fun i=> Q.act (b i)) (S.side r N) N 0 z):=by
             let p:=B0 0 u; let q:=B0 (b N+0) v; let Ψ:= eyeP (S.side r N) a; let p1:=B0 0 U₁; let q1:=B0 (Q.act (b N)+0) V₁; have h1:Action.adj a ⇑p=p1:=by have h:=hf.eye g u 0 a; rw[Signed.act_zero] at h; exact h
             have h2:Action.adj a ⇑q=q1:=by unfold q q1; simp only[add_zero]; exact hf.eye g v (b N) a
             funext V; rw [eye_value]; let X:=pull (K:=su.El) Q 0 V; change tilt Ψ ((z:ℂ) •(p X*q X))=(z:ℂ) • (p1 V*q1 V); rw[map_smulₛₗ,Complex.conj_ofReal,tilt_mul, show tilt Ψ (p X)=p1 V from (eye_value ..).symm.trans (congr_fun h1 V), show tilt Ψ (q X)=q1 V from (eye_value ..).symm.trans (congr_fun h2 V)]; exact congr_arg ((z:ℂ) • ·) ((show Plus (q1 V) from Hub.fade B sym hf (sym.adj _ a v) false (Hub.durable _ _ false he a) _ V).central (p1 V)).symm.eq
       let h1:=Canvas.flux H (Y:=⇑(G i 0)) a hW.living _ (fun x:Label d=>⇑(B (S.side r i) 0 x)) ht hW.reading (by rw [pier A hA hW.siteM]; exact (arrives A i hW.siteM).2.1 a) (by rw[pier A hA hW.siteM]; exact (arrives A i hW.siteM).2.2.2.2) (by have h:=hf.eye (S.side r i) w_ 0 a; rw[Signed.act_zero] at h; exact h)
       let p₀:= comet B u v b g N 0 z; let p₁:=comet B U₁ V₁ (fun i=> Q.act (b i)) g N 0 z; let SNν := A.regulator.density -- rename
       have hm: Action.adj a ⇑(SNν*p₀)=SNν*p₁:=by
             funext V; rw [eye_value]; let Ψ:= eyeP g a; let X:=pull (K:=su.El) Q 0 V; change tilt Ψ (SNν X * p₀ X)= SNν V*p₁ V; rw[tilt_mul]; rw[show tilt Ψ (SNν X)=SNν V from (eye_value ..).symm.trans (congr_fun (eye_pivot a _ rfl) V), show tilt Ψ (p₀ X)=p₁ V from (eye_value ..).symm.trans (congr_fun hx V)]; have he : Plus (SNν V):= (congr_fun hA.start V) ▸ hA.even le_rfl _; exact he.central _
       have hX: (G i 0)= AllAt A i (SNν*p₀) :=by unfold trolley Depth.visitor; rw [smul_zero]; rfl
       rw[hX,(eyes A a (SNν*p₀) (SNν*p₁) hm he')] at h1
       unfold trolley Depth.visitor; rw [smul_zero]; exact h1
omit ht
lemma warms (L:List Axis)(hh:Tally H 0 w (A.density i) (G i 0)):Tally H 0 (Hub.spine sym w L) (A.density i) (trolley A (fun x=>comet B (Hub.spine sym u L) (Hub.spine sym v L) (sawC b L) (S.side r N) N x z) none i 0):=by
       induction L with
       | nil=> exact hh
       | cons a k ih=>
          have ht(k:List Axis): moored (Hub.spine sym v k).val false:=by induction k with|nil=> exact he|cons a k ih=> exact Hub.durable _ _ _ ih a
          exact fluxE A H sym B hf hA _ _ (sawC b k) (ht _) z a he' _ K hW ih -- sig
end YM.Massive.Patria.Depth.Off
#print axioms YM.Massive.Patria.Depth.Off.homV
#print axioms YM.Massive.Patria.Depth.Off.activeV
#print axioms YM.Massive.Patria.Depth.Off.warms
