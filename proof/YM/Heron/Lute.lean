import YM.Heron.Lum
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad)
private lemma bull (φ:E4→ℂ)(he:Continuous φ)(hp:HasCompactSupport φ)(u:E4→ℝ)(hu:Continuous u): Integrable fun x=>u x • φ x:=by
    have hv:Continuous (fun x:E4=> (u x) • φ x):= hu.smul he; have he:HasCompactSupport (fun x:E4=>u x • φ x):=by
         apply IsCompact.of_isClosed_subset hp (isClosed_tsupport _); apply closure_mono; intro x hx; exact fun h=> hx (by change u x • φ x=0; rw[h,smul_zero])
    exact hv.integrable_of_hasCompactSupport he
variable (A:TinG)(hc:TrueC A)(i j k:Axis)(p:E4)(t:ℝ)(ht:0<t)(D₀:Faces){U:Set E4}(hU:IsOpen U)(g:Spins)(v:Drive)(χ:E4→ℝ)(hw:Way A U g)(hv:Seam v)(hs:tsupport χ⊆U)(hχ:ContDiff ℝ ∞ χ)(Hχ:HasCompactSupport χ)
local notation "f"=>bz A p t D₀
local notation "K"=>axon p t
local notation "V"=> aura v g χ D₀
local notation "Y"=>tiers A v g χ D₀
local notation "M"=>vale A v g χ D₀
include hw hv hs hχ Hχ
lemma loft : ContDiff ℝ ∞ M ∧ HasCompactSupport M:=by
    let W(i:Axis):=grad i (Y i); have hp(i): ContDiff ℝ ∞ (W i) ∧HasCompactSupport (W i):=by obtain ⟨h,hq⟩:= skyY A i D₀ g v χ hw hv hs hχ Hχ; exact ⟨contDiff_iff_contDiffAt.mpr (fun x=>Maxwell.grad_smooth _ (h.contDiffAt (x:=x)) (by simp)), hq.fderiv_apply ℝ (basis i)⟩
    have hd:= skyV A D₀ g v χ hw hv hs hχ Hχ; rw [show M = -V - ∑ i:Axis,W i from funext (fun x=>by simp [vale,W]), Fin.sum_univ_four]; exact ⟨hd.1.neg.sub ((((hp 0).1.add (hp 1).1).add (hp 2).1).add (hp 3).1),hd.2.neg.sub ((((hp 0).2.add (hp 1).2).add (hp 2).2).add (hp 3).2)⟩
include ht
include hc hU
lemma bridger : exportFlux (brook A f g v) χ = ∫ y, K y • M y := by
   have hK : ContDiff ℝ ∞ K := contDiff_iff_contDiffAt.mpr fun x=> torso p t ht x
   have hY(i:Axis) := skyY A i D₀ g v χ hw hv hs hχ Hχ; have hV:= skyV A D₀ g v χ hw hv hs hχ Hχ; let P(i:Axis)(y:E4):= K y • grad i (Y i) y; let S(i:Axis)(y:E4):= grad i K y • Y i y; let Q(y:E4):= K y • V y
   have he(i):Integrable (P i):=bull _ (show Continuous _ from (contDiff_iff_contDiffAt.mpr fun x=>Maxwell.grad_smooth _ ((hY i).1.contDiffAt (x:=x)) (m:=∞) (by simp)).continuous) ((hY i).2.fderiv_apply ℝ (basis i)) _ hK.continuous
   have hp(i):Integrable (S i):=bull _ (hY i).1.continuous (hY i).2 _ (gradient_smooth hK i).continuous
   have hq:Integrable Q:=bull _ hV.1.continuous hV.2 _ hK.continuous
   rw [by_parts hχ Hχ];
   · simp_rw [show ∀ y:E4,χ y • ∑ i:Axis,grad i (brook A f g v i) y= -(Q y)+ ∑ i:Axis, S i y from (fun y=> bastion A hc p t ht D₀ hU g v χ hw hv hs y), show ∀ y:E4, K y • M y= -(Q y)-∑ i:Axis,P i y from (fun y=>by unfold Q P vale; rw[smul_sub,Finset.smul_sum,smul_neg])]; rw [show (∫ x:E4,-(Q x)+(∑ i:Axis,S i x))=(∫ x:E4,-(Q x))+ (∫ x:E4, ∑ i:Axis,S i x) from integral_add (show Integrable (fun x=> -Q x) from hq.neg) (show Integrable (fun x:E4=>∑ i:Axis,S i x) from integrable_finsetSum _ fun i _=>hp i), show (∫ x:E4,-(Q x)-(∑ i:Axis,P i x))=(∫ x:E4,-(Q x))- (∫ x:E4, ∑ i:Axis,P i x) from integral_sub (show Integrable (fun x=> -Q x) from hq.neg) (show Integrable (fun x:E4=>∑ i:Axis,P i x) from integrable_finsetSum _ fun i _=>he i), integral_finsetSum _ fun i _=>hp i, integral_finsetSum _ fun i _=>he i]
     have h(i): (∫ y,S i y) = - (∫ y,P i y):=by rw[show (∫ y,P i y)= -(∫ y,S i y) from integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hp i) (he i) (bull _ (hY i).1.continuous (hY i).2 K hK.continuous) (fun x _=> hK.differentiable (by simp) x) (fun x _=>(hY i).1.differentiable (by simp) x), neg_neg]
     simp_rw [h,Finset.sum_neg_distrib]; abel
   intro a x hx; exact bow A a g f x v hv (tinge A p D₀ t ht x) (hw.live x (hs hx))
end YM.Heron
#print axioms YM.Heron.bridger
