import YM.Mako.Elate
set_option maxHeartbeats 700000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis×Axis→ K.W}
variable {A:Axle K (fun a b=>W (a,b))}(HK:K.Domestic){R:Roof P.sym}
variable (h:∀ d:ℕ,∀ hd:8 ≤ d,∃ F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d),Flyers A d hd T F)
variable {p:EuPin →* (K.W≃ₗ[ℂ] K.W)}(H: Steps (A:=A) T R p)
local instance choirR (K: Choir): NormedSpace ℝ K.W:=NormedSpace.restrictScalars ℝ ℂ _
include HK h H
namespace Steps
lemma dizzy {d:ℕ}(w: K.W)(hd:8 ≤d)(hw:w∈K.level d)(g:EuPin): p g w∈K.level d:=by
     obtain ⟨F,hF⟩:= h d hd; obtain ⟨v,hv⟩:= F.surjective ⟨w,hw⟩; rw [← show (F v).val=w from congr_arg Subtype.val hv,H.tones _ _ F hF]; exact Subtype.property _
lemma toll (w:K.W):∃ d:ℕ,8≤d ∧ w∈ K.level d:=by obtain ⟨d,hd⟩:=HK.absorbs w; exact ⟨max d 8,le_max_right ..,HK.slope (le_max_left ..) hd⟩
lemma acts (t:EuPin)(s:Signed)(ht:t.Lifts s): p t=T.spin t:=by
     ext1 x; obtain ⟨d,hd,hx⟩:= H.toll HK h x; obtain ⟨F,hF⟩:=h _ hd; let v:=F.symm ⟨x,hx⟩; rw [← show (F v).val=x from congr_arg Subtype.val (F.apply_symm_apply _), H.tones d hd F hF, colgate R hd F hF t s ht]
lemma plum (t:EuPin)(x:K.W)(q:FlavorTorus): T.flavor q (p t x)= p t (T.flavor q x):=by
     -- descent free from basis. full pin commute because flavorAct across any mode. need prove on Label.all
     obtain ⟨d,hd,hx⟩:= H.toll HK h x; obtain ⟨F,hF⟩:=h _ hd; let v:=F.symm ⟨x,hx⟩; rw[← show (F v).val=x from congr_arg Subtype.val (F.apply_symm_apply _),H.tones _ _ F hF]; obtain ⟨w,hw⟩:= Free.onto v; rw [←hw,clanP,hF.turns,hF.turns,H.tones _ _ F hF, clanP]; refine congr_arg (fun x:Label d=> (F (projection x)).val) (Subtype.ext ?_); rw [P.sym.flavorActs,P.sym.pinActs,P.sym.pinActs,P.sym.flavorActs]
     induction w.val using TensorProduct.induction_on with
     | zero => simp
     | add x y hx hy=> simp only [map_add,hx,hy]
     | tmul x y=> unfold flavorAct pinAct; simp_rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, QCD.Grass.adapt_together,(classic (d:=d) q t _).eq,(classic (d:=d) q⁻¹ t _).eq]; rfl
lemma fling (x:K.W):Continuous (fun t=> p t x):=by
     obtain ⟨d,hd,hx⟩:= H.toll HK h x; obtain ⟨F,hF⟩:= h _ hd; let v:=F.symm ⟨x,hx⟩; rw[← show (F v).val=x from congr_arg Subtype.val (F.apply_symm_apply _)]; simp_rw [H.tones _ _ F hF]; exact ((K.level d).subtype.comp F.toLinearMap).continuous_of_finiteDimensional.comp (howls R v)
lemma smooths (x:K.W)(g:Ortho.Skew)(f:ℝ→EuPin)(ht:EuPin.Path g f)(r:ℝ): HasDerivAt (fun t=> p (f t) x) (A.jet g (p (f r) x)) r:=by
     obtain ⟨d,hd,hx⟩:= H.toll HK h x; obtain ⟨F,hF⟩:=h _ hd; let v:=F.symm ⟨x,hx⟩; rw [← show (F v).val=x from congr_arg Subtype.val (F.apply_symm_apply _)]; simp_rw [H.tones _ _ F hF]
     let P:= ((K.level d).subtype.comp F.toLinearMap).toContinuousLinearMap.restrictScalars ℝ; have hh:=P.hasFDerivAt.comp_hasDerivAt r (music g ht R v r); refine hh.congr_deriv ?_; change (F _).val= _; rw [hF.revenue]; rfl
end Steps
end YM.Mako
#print axioms YM.Mako.Steps.fling
#print axioms YM.Mako.Steps.dizzy
#print axioms YM.Mako.Steps.smooths
#print axioms YM.Mako.Steps.plum
#print axioms YM.Mako.Steps.acts
