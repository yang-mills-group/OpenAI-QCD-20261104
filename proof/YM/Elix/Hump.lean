import YM.Elix.Erupt
/-! Curl dimension exact on Q. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx.Gourd
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper SourceRead Oriole Patria.Rolls Tawny Cast Carnal
open YM.MassiveMasses.FreePair Tarn Tarn.Choir Tarn.Choir.Measures YM.Analysis
open YM.Intag.Sprig YM.Intag.Sprig.Canopy YM.Sprig YM.Sprig.Lanterns
variable {C:Sequence}{P:Calibration C}{Q:Choir}{φ:ℕ→ℕ}(T:Pollens P Q)(E:Canopy P φ Q)(J: Lanterns T E)(hQ:Q.Harmony P φ)(hP:P.System)(n:Side)(hk:Injective (P.candidate 6 n 0))
open Matrix
local notation "Ωp"=> Plain beast 6
local notation "fZ"=> Flavor 6
local notation "Λ"=> basis 2
local notation "O"=> polls beast
local notation "X"=> Measures.arm Λ
noncomputable def conic (i:Three): Averaging:= shelC i.val.1 i.val.2.1 i.val.2.2
noncomputable def harbor (a b c:Axis) : (Three → Q.W) →ₗ[ℂ] Q.W:= if h:fresh (c,a,b)=true then Q.arc c ∘ₗ LinearMap.proj ⟨(c,a,b),h⟩ else 0
noncomputable def Maw (Q: Choir) : (Three→Q.W)→ₗ[ℂ] (Axis × Axis→Q.W):= LinearMap.pi fun i=>∑ k:Axis,harbor i.1 i.2 k
noncomputable def peakZ (k:ℕ):Plain beast 6 →ₗ[ℂ] (Three→Q.W):= grab 6 beast (fun _=> proves 6 (J.frame k 6))
lemma faded (a b c:Axis)(h:fresh (a,b,c)=false)(p:fZ): gamma6 p a b c= 0:=by unfold gamma6; rw [trio,if_pos (by have he :¬(a≠ b ∧ b≠c ∧ c≠a):=of_decide_eq_false h; tauto)]; exact Carnal.zeroS ..
lemma harp (k:ℕ)(j:fZ) (a b:Axis): (Maw Q ∘ₗ peakZ T E J k) (lamps j) (a,b)= ∑ i:Axis,Q.arc i (cost T E J k (gamma6 j i a b)):=by
     rw [LinearMap.comp_apply]; dsimp only [Maw,LinearMap.pi_apply]; rw [LinearMap.sum_apply]; refine sum_congr rfl fun i _=>?_ ; unfold harbor; split; rfl
     next h=> unfold cost; rw [faded i a b (Bool.eq_false_iff.mpr h) j,map_zero,map_zero, Submodule.coe_zero,map_zero]; rfl -- fix
lemma help (j:fZ)(a b:Axis): (Maw Q ∘ₗ O 6 conic Q) (lamps j) (a,b)=∑ i:Axis,Q.arc i (Q.focus (shelC i a b) 6 (gamma6 j i a b)):=by
     rw[LinearMap.comp_apply]; dsimp only[Maw,LinearMap.pi_apply]; rw[LinearMap.sum_apply]; refine sum_congr rfl fun i _=>?_ ; unfold harbor; split; rfl
     next h=> rw [faded i a b (Bool.eq_false_iff.mpr h),map_zero,map_zero]; rfl
local notation "pΓ"=> Maw Q ∘ₗ O 6 conic Q ∘ₗ bornT
local notation "pS" k:arg=> Maw Q ∘ₗ peakZ T E J k ∘ₗ bornT
open LinearMap
include hQ hk hP
lemma between (k:ℕ): ((pS k).range = (pΓ).range):=by
    obtain ⟨P',ht⟩:=paddle 6 beast n hP hk; have hv: Veer beast conic:=fun i j=>pays_rotate _ _; have hh:= reach_point T beast 6 conic _ (J.leaders k 6) ht hv (fun _=>rfl) hQ.h; rw [range_comp,range_comp (f:= _ ∘ₗ bornT),range_comp,range_comp,range_eq_top.mpr on_demand]; rw [← range_eq_map,← range_eq_map, hh]; rfl -- inspect
omit hk hP
lemma prizedT (k:ℕ)(hk:IsUnit (moon T E J k)): Injective (pS k):=by
    refine (LinearMap.ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=fZ→ℂ) (M₂:=Axis×Axis→ Q.W) (f:=(pS k))).mp (ker_eq_bot'.mpr ?_); intro x hx
    let r:=(E.B k).r; let l:= peakZ T E J k; let L:= Maw Q; let A:=moon T E J k; have he: A *ᵥ x=0:=by
         funext i; let u:= cost T E J k (gamma6 i 2 0 1); let v:ℂ:= r; let Ω:= v • Measures.topL (r • Λ) u; -- notation shadow
         have hP(j:fZ): (Ω) (((L∘ₗ l) (lamps j)) (0,1)) = A i j:=by
              have h:Λ≠ 0:=by intro h; have ht:=basis_norm 2; rw[h,norm_zero] at ht; exact zero_ne_one ht
              rw [show ((L∘ₗ l) (lamps j)) _ = _ from harp T E J k j 0 1,map_sum]; change _= ∑ i:Axis, _; exact sum_congr rfl fun i' _=> (derivands T E J hQ i j i' _ _ h).symm
         change (∑ j:fZ,A i j*x j)=0; change (L ∘ₗ l) (∑ i:Flavor 6,x i • lamps i)=0 at hx; rw [map_sum] at hx; have ht:=congr_fun hx (0,1); rw [Finset.sum_apply] at ht
         let f(j):= x j • ((L ∘ₗ l) (lamps j) (0,1)); have hz:Ω (∑ j:fZ, f j)=0:=by rw [show (∑ j:fZ,f j)=0 from ?_,map_zero]; unfold f; simp_rw [map_smul] at ht; exact ht
         rw [map_sum] at hz; refine Eq.trans (b:= ∑ j:fZ,Ω (f j)) ?_ hz; unfold f; simp_rw [map_smul,hP]; apply sum_congr rfl; intro j _; exact mul_comm ..
    let Z:= hk.unit; have hv: Z.val=A:= hk.unit_spec; rw[←hv] at he; have hh: (Z⁻¹.val * Z.val)*ᵥ x=0 :=by rw [← Matrix.mulVec_mulVec,he,mulVec_zero]
    rwa [show (Z⁻¹.val) * Z.val=1 from Z.inv_val,one_mulVec] at hh
include hk hP J
lemma lasting : Injective (pΓ):=by
     obtain ⟨k,h⟩:= major T E J hQ; let Q':= pΓ; have hm := LinearMap.finrank_range_add_finrank_ker (K:=ℂ) (V:=Flavor 6→ℂ) Q'; unfold Q' at hm; rw [←between T E J hQ hP n hk,LinearMap.finrank_range_of_inj (prizedT T E J hQ k h)] at hm -- cancel idiomatic??
     exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (show Module.finrank ℂ (pΓ).ker=0 by omega))
-- summit
variable (he:∀ (a:Flavor 6)(j k:Axis), (∑ i:Axis,Q.arc i (Q.focus (shelC i j k) 6 (gamma6 a i j k)))= Q.focus (shelS j k) 8 ((arcS a).val (j,k)))
open TableT
include he
lemma drawing : CurveQuest Q:=by
     intro u hu hk'; let v i := u i 1
     have hv: v=0:=by
          apply lasting T E J hQ hP n hk; rw [map_zero]; change ((Maw Q ∘ₗ O 6 conic Q) (∑ i:Flavor 6,v i • lamps i))=0; rw [map_sum]; rw [show poseα u= ∑ i:Flavor 6,v i • arcS i from ?_] at hu; rw [map_sum] at hu; rw[←hu]; refine sum_congr rfl fun i _=>?_; rw[map_smul,map_smul]; congr 1; ext1 ⟨a,b⟩; exact (help i a b).trans (he ..)
          change (∑ i:Flavor 6,axisα i (u i))=_; apply sum_congr rfl; intro b _; unfold axisα; rw [hk' b,zero_smul,zero_add]
     funext i j; fin_cases j; exact hk' i; exact congr_fun hv i
end YM.Massive.Patria.Gall.Onyx.Gourd
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.drawing
