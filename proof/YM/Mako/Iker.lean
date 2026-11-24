import YM.Mako.Ease
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}
variable {W:Axis×Axis→ K.W}{A: Axle K (fun a b=>W (a,b))}(H:Foil P K T)(HK:K.Domestic)(R:Roof P.sym){d j:ℕ}(hd:8≤d)(F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d))(hF: Flyers A d hd T F) (L:Free.Symbol j≃ₗ[ℂ] ↥(K.level j))(hj:8≤j)(hL: Flyers A j hj T L)
set_option quotPrecheck false
local notation "Ω"=> Free.Symbol d
open Ortho (Skew)
-- ODE uniqueness across horizons after pull through frame≥
lemma allied (z:Free.Symbol d→ₗ[ℂ] Free.Symbol j)(t:EuPin)
     (hz: ∀ p s (h:p.Lifts s) x, z (caravan R d p x)= caravan R j p (z x))
     (hx:∀ (v:Ortho.Skew) x,z (rain v d x)= rain v j (z x)) (x: Free.Symbol d): z (caravan R d t x)= caravan R j t (z x):=by
     let W(p:EuPin):Prop:=∀ x,z (caravan R d p x) = caravan R j p (z x)
     let U:Subgroup EuPin := {
          carrier:={i|W i}
          one_mem':=fun i=>by simp
          mul_mem':=by intro a b (hp:W a)(hq: W b) x; rw[map_mul,map_mul,LinearEquiv.mul_apply,hp,hq]; rfl
          inv_mem':=by
               rintro a (hp:W a) i; apply (caravan R j a).injective; rw [←hp,← LinearEquiv.mul_apply,←map_mul]; simp [W] }
     have ht : t∈U:= by
          apply engenders U hz
          intro p r i; let Tt:= (LinearMap.toContinuousLinearMap (rain p j)).restrictScalars ℝ; let P(t:ℝ):= caravan R d (oathU p t) i; let L(t:ℝ):= z (P t); let Q(t:ℝ):= caravan R j (oathU p t) (z i)
          have hh: ∀ t, HasDerivAt L (Tt (L t)) t:=by intro t; change HasDerivAt L (rain p j _) t; rw[show L t=z (P t) from rfl,← hx]; exact (z.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (music p (tour p) R i t)
          change L r=Q r; rw[reaps Tt L hh r,reaps Tt Q (music p (tour p) R _ ) r]; congr 1; unfold L P Q; rw[(tour p).1,map_one,map_one]; rfl
     exact (show W t from ht) x
include hF
lemma colgate(p:EuPin)(s:Signed)(h:p.Lifts s) (v:Free.Symbol d):T.spin p (F v)= (F (caravan R d p v)).val:=by obtain ⟨t,rfl⟩:= Free.onto v; rw [hF.rotates t p s h,clanP]
include HK hL
lemma tones (hh:d≤j)(t:EuPin)(x:Free.Symbol d): (L (caravan R j t (L.symm ⟨(F x).val, HK.slope hh (F x).property⟩))).val=(F (caravan R d t x)).val:=by
    let M:= Submodule.inclusion (HK.slope hh); let Q:= L.symm.toLinearMap ∘ₗ M ∘ₗ F.toLinearMap; change (L (caravan R j t (Q x))).val=_; rw[← allied R Q t ?_ ?_ x]; · unfold Q; simp; rfl
    · intro p s h x; apply L.injective; apply Subtype.ext; rw [← colgate R hj L hL p s h (Q x)] -- order issue implicit by variable order hd F. for d all hd F
      unfold Q; simp only[LinearMap.comp_apply,LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact (colgate R hd F hF p s h _).symm
    intro g v; apply L.injective; apply Subtype.ext; unfold Q; simp only[LinearMap.comp_apply,LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,hF.revenue,hL.revenue]; -- mismatch revenue hF g -> rewrites F in v
    rfl
end YM.Mako
#print axioms YM.Mako.tones
