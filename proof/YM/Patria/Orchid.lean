import YM.Patria.Canons
/-! Orientation on averaged candidates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d i m M:ℕ}
variable (A:Run S N r 6)(H:SourceRead.TaperHol) (sym:RawSym)
variable (B: Bore d)
variable (hf:Rubric sym B)
variable (u:Averaging)(hA:A.Actual)(W:Market S r d)(hW:Wager A H B W i)
open Poised Plans Display Orientation Exposure
local notation "Sn" =>A.regulator.density
local notation "Q" => ratioTo S N i
local notation "cn"=> S.side r N
local notation "Bn"=> S.side r i
local notation "bn"=> B (S.side r N)
local notation "X'"=>draft S r B N i u
local notation "FH"=> Fuel A H B
variable (X Y: Label d)(uv: FlavorTorus)(s:Signed)(p:EuPin)(a:Axis)(h:Tally H 0 Y (A.density i) (setS A B i u X))
open Rolls Canvas
local notation "Probe" => setS A B i u
variable (hp:p.Lifts s)
-- equivariant symmetry at origin. uses odd proof all.
lemma permeate {S':Side}(Ψ:Insertion S' 6 →ₗ[ℝ] Fields S' 6)(B C:Cover→Insertion S' 6)(U:Grid S')(he:∀ x, Ψ (B x)= C (s.act x) U)(hi:Odd m) : Ψ (Averaging.filter u m B 0) = (Averaging.filter (Averaging.permute s u) m C 0) U:=by
    let F : Insertion S' 6→ₗ[ℝ] Fields S' 6:= (ContinuousMap.evalCLM ℝ U).toLinearMap; have h:= stage_perm B s Ψ (fun c=>F (C c)) u he hi; refine h.trans ?_; rw [roles,roles]; exact (rollLinear ..).symm -- explicit
private abbrev watch (F:Fields cn 6→ₐ[ℂ] Fields cn 6)(V:Grid cn): Insertion cn 6 →ₗ[ℝ] Fields cn 6:= ((F.toLinearMap).comp (ContinuousMap.evalCLM ℂ V).toLinearMap).restrictScalars ℝ
@[simp] lemma permit_one : Averaging.permute 1 u=u:=by cases u <;> rfl
@[simp] lemma permit_mirror (u): Averaging.permute (Signed.mirror a) u=u:=by cases u<;>rfl
include hW h hA hf
set_option quotPrecheck false
local notation "ψ" => fun x:Label d=> ⇑(B (S.side r i) 0 x)
include hp in
lemma merch : FH i (Averaging.permute s u) (sym.pin d p X) (sym.pin d p Y):=by
    have ht:=pier A hA hW.siteM; let B₁:= Sn*X' X; let Xs:= sym.pin d p X; let B₂:= Sn*draft S r B N i (Averaging.permute s u) Xs
    have hT: Action.pin p s (X' X) = draft S r B N i (Averaging.permute s u) Xs:=by
       funext V; unfold draft visitor; rw [smul_zero]; exact permeate u s (watch (Lining.Temper.shipP cn s p) (pull s 0 V) (S:=S)) _ _ _ (fun k=> congr_fun (hf.pin cn X k s p hp) V) (odd_to (S:=S) hW.siteM)
    have he : Action.pin p s B₁= B₂:=by funext V; exact (map_mul (Lining.Temper.shipP cn s p) ..).trans (congr_arg₂ HMul.hMul (congr_fun (Exposure.pin_pivot s p _ hp (show A.regulator.t=0 from rfl)) V) (congr_fun hT V))
    have hu:= hinge s H p (Probe X) hp hW.living (sym.pin _ _ Y) ψ h hW.reading (by rw [ht]; exact (arrives A i hW.siteM).1 _ _ hp) (by have h:=hf.pin Bn Y 0 s p hp; rw [Signed.act_zero] at h; exact h)
    change Tally H 0 _ (A.density i) (AllAt A i B₂); exact pin_moves A s p B₁ B₂ hp he hW.siteM ▸ hu -- e ▸ issue
lemma rotary : FH i u (sym.flavor d uv X) (sym.flavor d uv Y):=by
    have ht:=pier A hA hW.siteM; let B₁:=Sn* X' X; let Y':= sym.flavor d uv X; let B₂:=Sn *X' Y'
    have hT: Action.flavor uv (X' X)= X' Y':=by
        funext V; unfold draft visitor; rw [smul_zero]; have hu(k):= congr_fun (hf.flavor cn X k uv) V
        have hh:= permeate u 1 (watch (Lining.Temper.stroll cn uv) V (S:=S)) (fun b=>bn b X) (fun b=>bn b Y') V (fun x=>by rw [Signed.act_one]; exact hu _) (odd_to (S:=S) hW.siteM); rw [permit_one u] at hh; exact hh
    have he: Action.flavor uv B₁= B₂:=by funext V; exact (map_mul (Lining.Temper.stroll cn uv) _ _).trans (congr_arg₂ HMul.hMul (congr_fun (flavor_pivot A.regulator uv) V) (congr_fun hT V))
    have hu:= Canvas.arrows H uv (Probe X) (sym.flavor _ _ Y) ψ h hW.reading (by rw [ht]; exact (arrives A i hW.siteM).2.2.1 _) (hf.flavor Bn Y 0 uv); change Tally H 0 _ (A.density i) (AllAt A i B₂); exact strokeP A uv B₁ B₂ he hW.siteM ▸ hu
lemma debit : FH i u (sym.charge d X) (sym.charge d Y):=by
    have ht:=pier A hA hW.siteM; let B₁:= Sn* X' X; let Y':= sym.charge d X; let B₂:=Sn* X' Y'
    have hT: Action.charge (X' X)= X' Y':=by
        funext V; unfold draft visitor; rw [smul_zero]; have hu(k):= congr_fun (hf.charge cn X k) V; have hh:= permeate u 1 (watch (Lining.Temper.eveN cn) (conjugate ∘ V) (S:=S)) (fun b=>bn b X) (fun b=>bn b Y') V (fun x=> by rw [Signed.act_one]; exact hu x) (odd_to (S:=S) hW.siteM); rw [permit_one] at hh; exact hh
    have he:Action.charge B₁=B₂:=by funext V; exact (map_mul (Lining.Temper.eveN cn) _ _).trans (congr_arg₂ HMul.hMul (congr_fun (charge_pivot A.regulator) V) (congr_fun hT V))
    have hu:= swingC H (Probe X) hW.living _ ψ h hW.reading (by rw [ht]; exact (arrives A i hW.siteM).2.2.2.1) (hf.charge Bn Y 0); change Tally H 0 _ (A.density i) (AllAt A i B₂); exact chargery A B₁ B₂ he hW.siteM ▸ hu
lemma grading : FH i u (sym.parity _ X) (sym.parity d Y):=by
    have ht:=pier A hA hW.siteM; let B₁:=Sn* X' X; let Y':= sym.parity d X; let B₂:=Sn* X' Y'
    have hT: Action.parity (X' X)= X' Y':=by
        funext V; unfold draft visitor; rw [smul_zero]; have hu(k):= congr_fun (hf.parity cn X k) V; have hh:= permeate u 1 (watch Grass.grade V (S:=S)) (fun b=>bn b X) (fun b=>bn b Y') V (fun x=> by rw [Signed.act_one]; exact hu x) (odd_to (S:=S) hW.siteM); rw [permit_one] at hh; exact hh
    have he:Action.parity B₁=B₂:=by
        have h:Action.parity Sn=Sn:=by have ht:= (arrives A N le_rfl).2.2.2.2; rw [origin] at ht; exact ht
        funext V; exact (map_mul Grass.grade ..).trans (congr_arg₂ HMul.hMul (congr_fun h V) (congr_fun hT V))
    have hu:=hingeP H (Probe X) _ ψ h hW.reading (by rw [ht]; exact (arrives A i hW.siteM).2.2.2.2) (hf.parity Bn Y 0); change Tally H 0 _ (A.density i) (AllAt A i B₂); exact checkered A B₁ B₂ he hW.siteM ▸ hu
lemma adjFlux : FH i u (sym.adj d a X) (sym.adj d a Y):=by
    have ht:=pier A hA hW.siteM; let B₁:= Sn* X' X; let Y':= sym.adj d a X; let B₂:=Sn*X' Y'; let s:= Signed.mirror a
    have hT: Action.adj a (X' X) = X' Y':=by
        funext V; unfold draft visitor; rw [smul_zero]; let v:=pull (K:=su.El) s 0 V; let L:= ((realTilt (c:=cn) (eyeP cn a)).comp (ContinuousMap.evalCLM ℝ v)).toLinearMap; have h(x) : L (bn x X)=bn (s.act x) Y' V:= (eye_value (bn x X) a V).symm.trans (congr_fun (hf.eye cn X x a) V)
        rw [eye_value]; have hg:= permeate u s L (fun i=>bn i X) (fun i=>bn i Y') _ h (odd_to (S:=S) hW.siteM); unfold s at hg; rw [permit_mirror] at hg; exact hg
    have he: Action.adj a B₁=B₂:=by
        funext V; rw [eye_value]; have h : tilt (eyeP cn a) (A.regulator.density (pull s 0 V))=Sn V:= (eye_value ..).symm.trans (congr_fun (eye_pivot a _ rfl) V)
        let F(V:Grid cn):=(X' X) (pull s 0 V); rw [show B₁ _= _ from ContinuousMap.mul_apply Sn _ (pull s 0 V), tilt_mul, h]; let Z:= tilt (eyeP cn a) (F V); have hν : Z=(X' Y') V:= (eye_value (X' X) a V).symm.trans (congr_fun hT V); have hY: Plus (A.regulator.density V):=by rw [← show A.density N=A.regulator.density from hA.start]; exact hA.even le_rfl _
        change Z* _ = _; rw [hν,hY.central]; rfl
    have hv:= arrives A i hW.siteM; have hu:= Canvas.flux H (Probe X) a hW.living (sym.adj d a Y) ψ h hW.reading (by rw [ht]; exact hv.2.1 a) (by rw [ht]; exact hv.2.2.2.2) (by have he:= hf.eye Bn Y 0 a; rw [Signed.act_zero] at he; exact he); change Tally H 0 _ (A.density i) (AllAt A i B₂); exact eyes A a B₁ B₂ he hW.siteM ▸ hu
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.adjFlux
#print axioms YM.Massive.Patria.Depth.grading
