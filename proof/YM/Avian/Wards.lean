import YM.Avian.Rifts
/-! Param counts → D range, using only full-rank on U intersection
 of nullspace and the authentic curl measurement. Neither UV calibration rank at wrong stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
open Rolls
open StressFlux.Offer (acts marks Vc)
local notation "Xσ"=> RawTensor 1 8
local notation "Xa"=> RawTensor (-1) 8
local notation "A"=> RawVec 10
local notation "T₀"=> Axis × Axis
variable {C:Sequence} {P:Calibration C} {Q: Choir} (T:Pollens P Q) (hP:P.System)(h:Q.Domestic)(hS_:∀ d,∃ n:Side,Injective (P.candidate d n 0))
variable (Ux:∀ d, UV.Free.Symbol d≃ₗ[ℂ] ↥(Q.level d))(hx:∀ d,Prose (Ux d) T)
-- dims API conditional
open Seals LinearMap
lemma raw1 : Module.finrank ℂ ↥Xσ=28:=by have he:= (LinearEquiv.ofBijective poseσ bona.1).finrank_eq; rw [←he,Module.finrank_prod,tolls,Module.finrank_fin_fun]
lemma raw2 : Module.finrank ℂ ↥Xa=12:=by rw [←(LinearEquiv.ofBijective poseα bona.2).finrank_eq,tolls]
lemma rawV : Module.finrank ℂ ↥A=45:=by rw [←(LinearEquiv.ofBijective TableT.plaza certified).finrank_eq,Module.finrank_prod,tolls, Module.finrank_fin_fun] -- plaza ambiguity
lemma setsB:Module.finrank ℂ (Pond ×Pond)=12:=by rw[Module.finrank_prod,show Module.finrank ℂ Pond = 6 from Module.finrank_fin_fun ℂ]
-- ARC(kernel obs) proof needed.Should PureArc rank by weak association proof.Engine later.Pad enough.
-- noncomputable def curlAxis : Pond→ₗ[ℂ] Xa:= poseα ∘ₗ (LinearMap.mk₂ ℂ ..) -- replace!
def CurveQuest (Q:Choir) : Prop := ∀ u:Values 2, obσ (-1) Q (poseα u)=0→ (∀ i,u i 0=0) → u=0
-- pick within Q. U choose tests.P.
def Worth (Q:Choir): Prop:=∃ Φ₁ Φ₂: Memory→ₗ[ℂ] Pond, Surjective ( (tallyF Φ₁ Φ₂).domRestrict (bits Q).ker)
set_option quotPrecheck false
local notation "pA" => (obσ (-1) Q).ker
set_option maxHeartbeats 600000 in
set_option maxRecDepth 4700 in
private lemma harvest (S: Xσ→ₗ[ℂ] A) (U:Xa→ₗ[ℂ]A)(h0:CurveQuest Q)(hS:viewsL ∘ₗ S=viewsX 1)(hU: viewsL ∘ₗ U= viewsX (-1)) : Module.finrank ℂ ((coprod S (U ∘ₗ (pA).subtype)).ker) ≤1:=by
    let K:= (obσ (-1) Q).ker; let R: (Xσ × K) →ₗ[ℂ] A:= (coprod S (U ∘ₗ K.subtype))
    let I:= (LinearEquiv.ofBijective poseσ bona.1)
    have hh {v:R.ker} : (I.symm v.val.1).2 0=0→ v=0:=by
          rcases v with ⟨⟨p,q⟩,hp⟩; intro hd
          obtain ⟨u,rfl⟩:= bona.1.2 p; rcases u with ⟨u,p⟩; let t:= I (u,p); have hg:I.symm t=(u,p):= I.symm_apply_apply (u,p); change (I.symm t).2 0=0 at hd; rw[hg] at hd; change R (t,q)=0 at hp
          obtain ⟨w,hw⟩:=bona.2.2 q.val; have he: viewsX 1 t+viewsX (-1) (poseα w)=0:=by
              rw[←hS,←hU,hw]; change viewsL (S _) + viewsL (U _) =0; rw[← map_add]; change viewsL (R (t,q)) =0; rw [hp,map_zero]
          obtain ⟨hq,h⟩:=skipσ u p w (congr_arg Prod.fst he); have hT: w=0:=h0 _ (by rw[hw]; exact q.property) h
          have hf : q=0:= Subtype.ext (show q.val=0 by rw[←hw,hT,map_zero]); have hp0:= levy u p (fun i=> by have ht : gaugeA 1 t i+ gaugeA (-1) (poseα w) i=0:=congr_fun (congr_arg Prod.snd he) i; rw [hT,map_zero,map_zero] at ht; change gaugeA 1 t i + 0=0 at ht; rw[add_zero,gaugeV] at ht; exact ht)
          have hl:p=0:= by funext i; fin_cases i; exact hd; exact hp0.1; exact hp0.2.1; exact hp0.2.2
          apply Subtype.ext; exact Prod.ext ((congr_arg poseσ (show (u,p)=0 from Prod.ext hq hl)).trans (map_zero _)) hf
    let M:R.ker →ₗ[ℂ]ℂ:= LinearMap.proj (0:Fin 4) ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ I.symm.toLinearMap ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ R.ker.subtype -- syntax
    have hL: Function.Injective M:=(LinearMap.ker_eq_bot (R:=ℂ) (M:=↥R.ker) (M₂:=ℂ) (R₂:=ℂ) (f:=M)).mp (LinearMap.ker_eq_bot'.mpr (fun _ hh'=>hh hh'))
    have hK : Module.finrank ℂ R.ker≤1:=(finrank_le_finrank_of_injective hL).trans_eq (Module.finrank_self ..)
    exact hK
include hx hP hS_ h
set_option maxHeartbeats 600000 in
set_option maxRecDepth 4200 in
lemma till (h0:CurveQuest Q)(H:Worth Q)(hA:Firm Q (-1))(hB:Firm Q 1): ((swingE Q 1).range=(bits Q).range) ∧ Module.finrank ℂ (obσ 1 Q).range=22∧Module.finrank ℂ (bits Q).range=20:=by
    obtain ⟨Φ₁,Φ₂,hY⟩:=H; let X:= obσ 1 Q; let Y:= bits Q
    let F:= tallyF Φ₁ Φ₂; obtain ⟨S,hS,hF,hH⟩:= plea Φ₁ Φ₂ hB; obtain ⟨U,hU,hG,hE⟩:= plea Φ₁ Φ₂ hA
    let K:= (obσ (-1) Q).ker; let R: (Xσ × K) →ₗ[ℂ] A:= (coprod S (U ∘ₗ K.subtype)); have hp : (F ∘ₗ R)=0:=by apply LinearMap.ext; rintro ⟨p,b⟩; change F (_+_)=_; rw [map_add]; change (F ∘ₗ S) _ + (F ∘ₗ U) _ = _; rw [hF,hG, LinearMap.zero_apply, LinearMap.zero_apply,add_zero]; rfl
    have hd:= talent T hP h hS_ Ux hx -- rename; gives dim K=6
    letI : FiniteDimensional ℂ ↥A:= FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=Axis→Label 10) A
    letI : FiniteDimensional ℂ ↥Xσ:=FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=T₀→ Label 8) Xσ
    letI :FiniteDimensional ℂ ↥Xa:=FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=T₀→ Label 8) Xa
    have hv : Module.finrank ℂ K=6:=by have ht := LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=Xa) (obσ (-1) Q); rw [raw2,hd] at ht; unfold K; omega
    let B:Submodule ℂ A:=F.ker; have ht:R.range ≤ B:=by intro x hx; obtain ⟨p,rfl⟩:=hx; change (F ∘ₗ R) p=0; rw[hp]; rfl
    have hr: Module.finrank ℂ B=33:=by
          have H:Surjective F:=fun x=> by obtain ⟨q,hq⟩:= hY x; exact ⟨q.val,hq⟩
          have hp := finrank_range_add_finrank_ker (K:=ℂ) (V:=A) F; rw[rawV,range_eq_top.mpr H,finrank_top,setsB] at hp; unfold B; omega
    have hK:Module.finrank ℂ R.ker ≤ 1:=harvest S U h0 hS hU
    have hg: R.range=B:=Submodule.eq_of_le_of_finrank_le ht ?_; swap
    · have hQ:= LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=(Xσ × K)) R; rw [Module.finrank_prod,raw1,hv] at hQ; rw [hr]; omega
    refine ⟨?_,tinted T hP h hS_ Ux hx,torchV T hP h hS_ Ux hx⟩
    apply le_antisymm; · rw [←hH]; exact LinearMap.range_comp_le_range ..
    intro t ht; obtain ⟨v,rfl⟩:=ht; obtain ⟨p,hp⟩:= hY (F v)
    have hv(v:Xa)(hh:v ∈ K): Y (U v)=0:=by change (bits Q ∘ₗ U) v= _; rw [hE]; unfold swingE; rw [LinearMap.comp_apply,show (obσ (-1) Q) v=0 from hh,map_zero]
    have hE : v-p.val ∈ R.range:=by rw[hg]; change F _=0; rw[map_sub]; change _-F (p.val)=0; rw[show F p.val=F v from hp, sub_self]
    obtain ⟨⟨q,a⟩,ha⟩:= hE; refine ⟨q,?_⟩; rw [←hH]; change Y (S q)= Y v
    have hx:Y (S q+U a.val) = Y (v-p.val):=congr_arg Y ha; rw [map_add,map_sub,hv _ a.prop,show Y (p.val)=0 from p.prop,sub_zero,add_zero] at hx; exact hx
end YM.Massive.Patria.Gall.Onyx
#print axioms YM.Massive.Patria.Gall.Onyx.till
