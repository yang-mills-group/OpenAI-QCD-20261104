import YM.Avian.Stroll
import YM.Gall.Coset
/-! Exact transform of TALLY at origin. Reject charge padding.Perfect. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Rolls
open Function Lattice RG Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Gall Intag MassFields
variable {S:Scheme}{R :Side}{N i m p q d k:ℕ} (A:Run S N R 6) (T:SourceRead.TaperHol) (sym:RawSym) (B:Bore d) (hT:Rubric sym B)(W:Market S R d)(hA:A.Actual)(hW:Wager A T B W 0)
variable (X Y:Cover→Insertion (S.side R N) 6)(s:Signed)(V:Averaging)
local notation "Fℓ"=> S.side R N
local notation "Pℓ"=> Insertion Fℓ 6
local notation "U"=>A.regulator.density
local notation "f" x:arg u:arg=> trolley A x u 0 0
namespace Attain
-- general Φ transformation on cover X under pivot at t.
local notation "pY"=> visitor S N 0 (r:=R)
variable (c:Side)
lemma perpet (Φu:Grid Fℓ→Grid Fℓ)(J: Lat.Fields Fℓ 6→ₐ[ℂ]Lat.Fields Fℓ 6)(M:∀ c:Side, Density c 6→ Density c 6)(he:∀ Z:Insertion Fℓ 6,∀ V': Grid Fℓ,M Fℓ Z V'=J (Z (Φu V')))(hP:∀ x:Cover,M Fℓ (X x)=⇑(Y (s.act x)))(hx:M Fℓ U= ⇑U)(hh:∀ A₁ A₂: Pℓ,M Fℓ ⇑A₁=⇑A₂→ M (S.side R 0) (AllAt A 0 A₁)=⇑(AllAt A 0 A₂)) : M (S.side R 0) (f X V)=⇑(f Y (Averaging.permute s V)):=by
     let L:= V; let C:=pY L 0 X; let D:=pY (Averaging.permute s V) 0 Y; have h: M _ C=⇑D:=by
          funext Z'; rw [he]; let Ψ: Pℓ→ₗ[ℝ] Lat.Fields Fℓ 6:= (J.toLinearMap.comp (ContinuousMap.evalCLM ℂ (Φu Z')).toLinearMap).restrictScalars ℝ
          unfold C D; unfold visitor; rw [smul_zero]; exact Depth.permeate V s Ψ X Y Z' (fun x=> by have h:=congr_fun (hP x) Z'; rw [he] at h; exact h) (odd_to (S:=S) (Nat.zero_le N)) -- order unwrap
     change M _ (AllAt A 0 (U*C))=⇑(AllAt A 0 (_*_)); apply hh; funext i; rw [he]; change J ((U (Φu i))*(C (Φu i)))= U i * D i; rw [map_mul, ←he,← he]; rw [hx,h]
lemma ordered (M:∀ c:Side,Density c 6 → Density c 6)(Φu:Grid Fℓ→Grid Fℓ)(J: Lat.Fields Fℓ 6→ₐ[ℂ]Lat.Fields Fℓ 6) (he:∀ Z:Insertion Fℓ 6,∀ V': Grid Fℓ,M Fℓ Z V'=J (Z (Φu V')))(hP:∀ x:Cover,M Fℓ (X x)=⇑(X x))(hx:M Fℓ U= ⇑U)(hh:∀ A₁ A₂: Pℓ,M Fℓ ⇑A₁=⇑A₂→ M (S.side R 0) (AllAt A 0 A₁)=⇑(AllAt A 0 A₂)): M _ (f X V)= ⇑(f X V) :=by
     have he:=perpet A X X 1 V Φu J M he (fun x=>by rw [Signed.act_one]; exact hP x) hx hh; rwa [Depth.permit_one] at he
lemma gradeS (h:∀ x:Cover, Action.parity (X x)=⇑(X x)): Action.parity (f X V)=⇑(f X V):=by
     refine ordered A X V (fun _=>Action.parity) id QCD.Grass.grade (fun _ _=>rfl) h ?_ (fun x y h=>checkered _ _ _ h (Nat.zero_le _)); have ht:= (arrives A N le_rfl).2.2.2.2; rw [origin] at ht; exact ht
lemma flavorF (u:FlavorTorus)(h:∀ x:Cover,Action.flavor u (X x)=⇑(X x)): Action.flavor u (f X V)= ⇑(f X V):= ordered A X V (fun _=> Action.flavor u) id (Lining.Temper.stroll Fℓ u) (fun _ _=>rfl) h (Exposure.flavor_pivot A.regulator u) (fun _ _ he=> strokeP A u _ _ he (Nat.zero_le _))
lemma chargeG (h:∀ x:Cover,Action.charge (X x)= ⇑(X x)): Action.charge (f X V)=⇑(f X V):=ordered A X V (fun _=> Action.charge) (fun y=> conjugate∘y) (Lining.Temper.eveN Fℓ) (fun _ _=>rfl) h (Exposure.charge_pivot A.regulator) (fun _ _ he=> chargery A _ _ he (Nat.zero_le _))
lemma pinG (p:EuPin)(hp:p.Lifts s)(h:∀ x:Cover,Action.pin p s (X x)=⇑(Y (s.act x))): Action.pin p s (f X V)=⇑(f Y (Averaging.permute s V)):= perpet A X Y s V (pull s 0) (Lining.Temper.shipP Fℓ s p) (fun _=>Action.pin p s) (fun _ _=>rfl) h (Exposure.pin_pivot _ _ A.regulator hp rfl) (fun _ _ he=>pin_moves A s p _ _ hp he (Nat.zero_le _)) -- order
variable (Q:Label d)(hQ:Tally T 0 Q (A.density 0) ⇑(trolley A X V 0 0))
include hW hT hA hQ
local notation "Dℓ"=> fun x:Label d=>⇑(B (S.side R 0) 0 x)
lemma dew (h:∀ x:Cover, Action.parity (X x)=⇑(X x)): sym.parity d Q=Q:=by
    have hz:= Canvas.hingeP T (f X V) (sym.parity _ Q) Dℓ hQ hW.reading (by rw[pier A hA hW.siteM]; exact (Depth.arrives A 0 hW.siteM).2.2.2.2) (hT.parity _ _ _); rw[gradeS A X V h] at hz; exact Canvas.consensus _ _ _ hz Q hQ
lemma eon (u:FlavorTorus)(h:∀ x:Cover, Action.flavor u (X x)=⇑(X x)): sym.flavor d u Q=Q:=by
    have hz:= Canvas.arrows T u (f X V) (sym.flavor _ u Q) Dℓ hQ hW.reading (by rw[pier A hA hW.siteM]; exact (Depth.arrives A 0 hW.siteM).2.2.1 u) (hT.flavor _ _ _ _); rw[flavorF A X V u h] at hz; exact Canvas.consensus _ _ _ hz Q hQ
lemma hour (h:∀ x:Cover, Action.charge (X x)=⇑(X x)): sym.charge d Q=Q:=by
    have hz:= Canvas.swingC T (f X V) hW.living (sym.charge _ Q) Dℓ hQ hW.reading (by rw[pier A hA hW.siteM]; exact (Depth.arrives A 0 hW.siteM).2.2.2.1) (hT.charge _ _ _); rw[chargeG A X V h] at hz; exact Canvas.consensus _ _ _ hz Q hQ
lemma auth (p:EuPin)(hp:p.Lifts s)(h:∀ x:Cover,Action.pin p s (X x)=⇑(Y (s.act x)))(Q':Label d)(hD: Tally T 0 Q' (A.density 0) (f Y (Averaging.permute s V))): sym.pin d p Q= Q' :=by
    have hz:= Canvas.hinge s T p (f X V) hp hW.living (sym.pin _ p Q) Dℓ hQ hW.reading (by rw [pier A hA hW.siteM]; exact (arrives A 0 hW.siteM).1 _ _ hp) (by have h:=hT.pin (S.side R 0) Q 0 s p hp; rw [Signed.act_zero] at h; exact h); rw[pinG A X Y _ _ _ hp h] at hz; exact Canvas.consensus _ _ _ hz _ hD
end Attain
end YM.Massive.Patria.Rolls
#print axioms YM.Massive.Patria.Rolls.Attain.auth
