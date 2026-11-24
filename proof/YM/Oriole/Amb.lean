import YM.Infer.Shack
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise ContDiff Stamp Kronecker Classical
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Romance
local notation "V"=> Lat.Fields n 6
local notation "Fω"=> Insertion n 6
variable (x:Drape)(l:List Axis)(Q:BudgetPoint)(z:ℝ)
variable {p:Label d}(Y: SourceRead.TaperHol)(W:Knot p)(h:Requisite Y p W)
open Depth Canvas Poised Cylinder
-- weighted.Antiseam. symbols via independent test from Pilot. not using β commute here
variable {S: Scheme}{R:Side}{N m:ℕ}
variable (A:Run S N R 6)(sym:RawSym)(B:Bore d)(u:Label d)
variable (hA:A.Actual)(hm:m≤N)(hv:18≤ (S.side R m).val)(hf:Rubric sym B) (hB:∀ i:Label d,Beacon.ActionTest Y 0 (B (S.side R m) 0 i) i.val)
local notation "Bm" => B (S.side R m) (0:Cover)
local notation "fp" => S.side R N
variable (Jp:Massive.Averaging)
local notation "XF" l:arg=>trolley A (evoc x l fp) Jp m 0
local notation "TF" y:arg l:arg=>Tally Y 0 y (A.density m) (XF l)
include hA hm hB hv hf
lemma forgivesR (h:TF u l): TF (sym.adj _ a u) (a::l):=by
    let F:= evoc x l; let T:= evoc x (a::l); let P₀:= A.regulator; let X:=P₀.density*visitor S N m Jp 0 (F fp); let Z:=P₀.density*visitor S N m Jp 0 (T fp)
    have hθ:Action.adj a ⇑(visitor S N m Jp 0 (F fp))= ⇑(visitor S N m Jp 0 (T fp)):=by
         funext U; unfold visitor; rw [smul_zero]
         let s:=Signed.mirror a; let Z:=pull (K:=su.El) s 0 U; let Qb:= ((Patria.Exposure.realTilt (c:=fp) (Patria.Exposure.eyeP fp a)).comp (ContinuousMap.evalCLM ℝ Z)).toLinearMap
         have hy(z:Cover): Qb (F fp z)= T fp (s.act z) U :=by
              change _=T fp _ _; have he:F fp z= F fp ((Signed.mirror a).act ((Signed.mirror a).act z)):=by rw [← Signed.act_mul,show Signed.mirror a*Signed.mirror a=1 from mul_inv_cancel _,Signed.act_one]
              rw[he]; exact (eye_value ..).symm
         rw[Patria.Exposure.eye_value]; have h:=permeate Jp s Qb (F fp) (T fp) U hy (odd_to (S:=S) hm); unfold s at h; rw [permit_mirror] at h; exact h
    let s:=Signed.mirror a; have he : Action.adj a ⇑X = ⇑Z:=by
         funext U; rw [Exposure.eye_value]; have h : tilt (eyeP fp a) (P₀.density (pull s 0 U))=P₀.density U:= (eye_value ..).symm.trans (congr_fun (eye_pivot a _ rfl) U)
         let Kx:= visitor S N m Jp 0 (F fp); let Ky:=visitor S N m Jp 0 (T fp)
         rw [show X _= P₀.density _* Kx _ from ContinuousMap.mul_apply _ _ _, tilt_mul,h, show tilt _ (Kx _)= Ky U from (eye_value ..).symm.trans (congr_fun hθ U)] -- rw metavars
         change Ky U*_=_; exact Plus.central (show Plus (P₀.density U) from ((congr_fun (show A.density N=⇑P₀.density from hA.start) U) ▸ hA.even le_rfl U)) _
    let φ: Label d→Density (S.side R m) 6:=fun k=> ⇑(Bm k); have hv' := arrives A m hm; have ht:= pier A hA hm
    have hu': Action.adj a (φ u)= φ (sym.adj d a u):=by unfold φ; rw [hf.eye,Signed.act_zero]; -- exact
    apply Canvas.flux Y (XF l) a hv _ φ h hB (by rw [ht]; exact hv'.2.1 a) (by rw [ht]; exact hv'.2.2.2.2) hu' |> Eq.mp ?_ -- rewrite via eyes
    exact congr_arg (Tally Y 0 (sym.adj _ a u) (A.density m)) (eyes A a X Z he hm)
omit hA hm hB hv hf
-- wrap in recursive list
include hA hm hB hv hf
lemma passesR (h:TF u []): TF (Hub.spine sym u l) l :=by
    induction l with|nil=> exact h | cons i l ih=>exact forgivesR i x l Y _ _ _ _ hA hm hv hf hB Jp ih
-- causal.B.One
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.passesR
