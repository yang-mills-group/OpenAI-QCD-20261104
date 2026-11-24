import YM.Mako.Veer
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
open Ortho (plane Skew)
open Org
section
variable {W:Type*}[Ring W][Algebra ℂ W](L:Skew→ W) (D P:Axis → W)
variable (H:∀ p q,clip (L p) (L q) = L (bracket p q))
variable (h:∀ p i,clip (L p) (D i)=∑ j:Axis, (p.val j i:ℂ) • P j)
lemma sky{V:Type*}[AddCommGroup V][Module ℂ V] (P:Axis→ V)(a b:Axis)(h:a≠b): (∑ j:Axis,((plane a b).val j b:ℂ) • P j)= P a:=by
       rw[Finset.sum_eq_single a]; · simp [plane,Matrix.single_apply,h,Ne.symm h]
       · intro i _ hi; simp [plane,Matrix.single_apply,h,Ne.symm h, hi,Ne.symm hi]
       simp
include h H
lemma otherΨ (a b k:Axis): clip (L (plane a b)) (P k) = ∑ j:Axis, ((plane a b).val j k:ℂ) • P j:=by
      obtain ⟨c,ha,hb,hc⟩:= outside a b k; let p:=plane a b; let q:=plane k c; have hq : clip (L q) (D c)= P k:= (h q c).trans (sky P k c hc)
      have hh(i): p.val i c=0:=by simp [p,plane,Matrix.single_apply,ha,hb,Ne.symm ha, Ne.symm hb]
      have hp : clip (L p) (D c)=0:= by rw [h]; simp[hh]
      have he(i): (bracket p q).val i c=p.val i k:=by
              change (p.val*q.val-q.val*p.val) i c=p.val i k
              simp_rw[Matrix.sub_apply,Matrix.mul_apply,hh,mul_zero,Finset.sum_const_zero,sub_zero]; rw[Finset.sum_eq_single k]; · simp[q,plane,hc,Ne.symm hc,Matrix.single_apply]
              · intro j _ hj; simp [q,plane,hj,hc,Ne.symm hj,Matrix.single_apply]
              simp
      have hv:= jac (L p) (L q) (D c); rw [H,h,hq,hp,show ∀ x:W,clip 0 x=0 from (fun x=>by simp [clip]),zero_add] at hv; change clip (L p) (P k)=_; rw[← hv]; simp_rw[he]; rfl -- change LHS p def
lemma venus (a b k:Axis): Commute (L (plane a b)) (D k-P k):= sub_eq_zero.mp (by
      change clip _ _=0; rw[show clip (L (plane a b)) (D k-P k)=clip (L (plane a b)) (D k)-clip (L (plane a b)) (P k) from (by unfold clip; noncomm_ring), h,otherΨ L D P H h a b k,sub_self])
end
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis×Axis→ K.W} {A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S: Steps (A:=A) T R ρ)
include H J JQ B R
lemma feathers :∀ p i,clip (A.jet p) (K.arc i)=∑ j:Axis,(p.val j i:ℂ) • B.edge j:=by
      intro p i; ext1 x; rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply]; exact B.sparks H JQ.h A x i p -- maybe order
lemma connect (a b i:Axis): Commute (A.jet (plane a b)) (K.arc i-B.edge i):= venus _ _ _ (stake J H JQ B R) (feathers J H JQ B R) a b i
lemma limb (a b:Axis) (h:a≠b): clip (A.jet (plane a b)) (K.arc b)=B.edge a:=by rw[feathers J H JQ B R,sky B.edge a b h]
lemma hems (k d:ℕ)(h:8≤d)(a:Axis)(x:K.W)(hx:x∈ K.level d):B.edge a x∈ K.level (d+2):=by obtain ⟨b,hb⟩:=exists_ne a; rw [←limb J H JQ B R a b hb.symm]; exact (K.level _).sub_mem (A.landed _ (h.trans (by omega)) _ _ (JQ.h.graded b d _ hx)) (JQ.h.graded b _ _ (A.landed d h _ _ hx)) -- can remove k
include S
-- exact flow of commutant by finite-dimensional differential. choose x in domain.
-- covariance under p_t along one specific plane only (later p proper). given maps commute infinitesimal
lemma locks {d j:ℕ}(hd:8 ≤d)(hj:8 ≤j)(F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d))(Y:Free.Symbol j≃ₗ[ℂ] ↥(K.level j))(hf: Flyers A d hd T F)(hY: Flyers A j hj T Y)(z:Module.End ℂ K.W)(hz:∀ x∈K.level d,z x∈ K.level j)(p:Ortho.Skew)(h:Commute (A.jet p) z)(x:K.W)(hx:x∈ K.level d)(t:ℝ): z (ρ (oathU p t) x)=ρ (oathU p t) (z x):=by
      let M:= Y.symm.toLinearMap ∘ₗ (((z.comp (K.level d).subtype).codRestrict (K.level j) (fun v=>hz v.val v.property)) ∘ₗ F.toLinearMap); have h0(v): (Y (M v)).val=z (F v).val:=by unfold M; simp
      have ht(v: Free.Symbol d):M (rain p d v)= rain p j (M v):=by apply Y.injective; apply Subtype.ext; rw [h0,hf.revenue,hY.revenue]; change z (A.jet p _) =A.jet p (Y _).val; rw[h0]; exact DFunLike.congr_fun h.symm.eq _ -- h.symm commute
      obtain ⟨v,hv⟩:= F.surjective ⟨x,hx⟩; rw[← show (F v).val=x from congr_arg Subtype.val hv,S.tones _ _ F hf, ←h0,←h0,S.tones _ _ Y hY]; suffices hm:M (caravan R d (oathU p t) v)= caravan R j (oathU p t) (M v) by rw [hm]
      let L:= (LinearMap.toContinuousLinearMap (rain p j)).restrictScalars ℝ; let a(r:ℝ):= M (caravan R d (oathU p r) v); let q(r:ℝ):= caravan R j (oathU p r) (M v); change a t=q t
      have hh(r:ℝ):HasDerivAt a (L (a r)) r:=by change HasDerivAt a (rain p j _) _; unfold a; rw[←ht]; exact ((LinearMap.toContinuousLinearMap M).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (music p (tour p) R v r)
      rw [reaps L a hh t,reaps L q (music p (tour p) R _) t]; congr 1; unfold a q; simp[(tour _).1]
end YM.Mako
#print axioms YM.Mako.locks
#print axioms YM.Mako.connect
#print axioms YM.Mako.hems
