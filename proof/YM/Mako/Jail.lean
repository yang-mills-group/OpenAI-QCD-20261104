import YM.Mako.Obj
import YM.Mako.Matte
import YM.Vern.Climb
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
noncomputable def rain (u:Ortho.Skew)(d:ℕ):Module.End ℂ (Free.Symbol d):= reachΩ u (oathU u) (tour u) (fun _=>1) d
variable {d:ℕ}(p:Ortho.Skew){f:ℝ→EuPin}(hf:EuPin.Path p f){σ:RawSym}(R:Roof σ) (x:Free.Symbol d)
include R hf
lemma iris : rain p d= reachΩ p f hf (fun _=>1) d:=by
     have he:f=oathU p:= SpinPath.covering.eq_of_comp_eq hf.2.1 (tour p).2.1 (funext fun t=> (hf.2.2 t).trans ((tour p).2.2 t).symm) 0 (hf.1.trans (tour p).1.symm)
     subst f; rfl
lemma music (r:ℝ) : HasDerivAt (fun t=> caravan R d (f t) x) (rain p d (caravan R d (f r) x)) r:= by rw [iris p hf R]; exact grace _ _ _ _
lemma chime : HasDerivAt (fun t=> caravan R d (f t) x) (rain p d x) 0 :=by simpa [hf.1] using music p hf R x 0
omit hf
lemma fang(s:EuPin) : rain (conjSkew s.coord p) d (caravan R d s x) = caravan R d s (rain p d x):=by
     let F:=caravan R d; let g:= oathU p; let q(t:ℝ):=s*g t*s⁻¹; have ht:= chime _ (show EuPin.Path (conjSkew s.coord p) q from conjug p g (tour p) s) R (F s x); let L:= (F s).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; apply ht.unique; apply (L.hasFDerivAt.comp_hasDerivAt 0 (chime _ (tour p) R x)).congr_of_eventuallyEq; apply Eventually.of_forall; intro y; change F (q y) (F s x)= F s (F (g y) x); simp_rw [←LinearEquiv.mul_apply,←map_mul]; simp [q]
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{K:Choir}{T:Pollens P K}
variable {E:Canopy P φ K}{X:Lanterns T E}{W:Axis×Axis→ K.W} {A: Axle K (fun a b=>W (a,b))}{I:ℕ→ℕ} (J:Glacier T E X W A I)(H:Foil P K T)(HK:K.Domestic)(hd:8 ≤ d)
omit R
include J
lemma goes(p:Ortho.Skew) (v:Free.Symbol d): Tendsto (fun t=> steel W E X A hd p (I t) v) atTop (𝓝 (rain p d v)):= J.angV d hd p _ (tour p) v -- include
include H HK hd
lemma e_add (u v:Ortho.Skew):rain (u+v) d =rain u d+rain v d:=by
    apply LinearMap.ext; intro x; apply tendsto_nhds_unique (goes J hd (u+v) x); apply ((goes J hd u x).add (goes J hd v x)).congr'; apply Eventually.of_forall; intro t; dsimp only; apply (X.frame (I t) d).injective; rw [map_add]; unfold steel; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; apply Subtype.ext; change A.jet u _+A.jet v _=A.jet (u+v) _; rw[A.addP H HK]; rfl
lemma e_scal (r:ℝ)(u:Ortho.Skew):rain (r • u) d=(r:ℂ) • rain u d:=by
    ext1 x; apply tendsto_nhds_unique (goes J hd (r • u) x); apply ((tendsto_const_nhds (x:=(r:ℂ))).smul (goes J hd u x)).congr'; apply Eventually.of_forall; intro t; dsimp only; apply (X.frame (I t) d).injective; rw[map_smul]; unfold steel; simp only[LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; apply Subtype.ext; change (r:ℂ) • (A.jet u _)= (A.jet (r • u) _); rw[A.scaleP H]; rfl
noncomputable def chorus: Ortho.Skew →L[ℝ] (Free.Symbol d →L[ℝ] Free.Symbol d):= LinearMap.toContinuousLinearMap {
    toFun p:= (LinearMap.toContinuousLinearMap (rain p d)).restrictScalars ℝ
    map_add' u v:= by apply ContinuousLinearMap.ext; intro x; change rain (u+v) d x=_; rw [e_add J H HK hd]; rfl
    map_smul' r u:=by apply ContinuousLinearMap.ext; intro x; change rain (r • u) d x=_; rw[e_scal J H HK hd]; rfl }
omit H HK J hd
lemma comet {Z:Type*}[NormedAddCommGroup Z][NormedSpace ℂ Z][NormedSpace ℝ Z][IsScalarTower ℝ ℂ Z](Q:Ortho.Skew →L[ℝ] (Z →L[ℝ] Z))(F:EuPin →* (Z≃ₗ[ℂ]Z)) (h:∀ p x,HasDerivAt (fun t=> F (oathU p t) x) (Q p x) 0)(hs:∀ v x s,Q (conjSkew s.coord v) (F s x)= F s (Q v x))(u v:Ortho.Skew)(x:Z):Q u (Q v x)-Q v (Q u x)=Q (Org.bracket u v) x:=by
    let L:= oathU u; have he: L 0=1:=(tour u).1
    let g(t):=conjSkew (Ortho.oneParameter u t) v; have hh: HasDerivAt g (Org.bracket u v) 0:= conj_deriv ..
    have hQ:g 0=v:=by unfold g; rw[oneParameter_zero]; apply Subtype.ext; change (1:M4)*v.val*star 1=v.val; simp
    have hv:= ((Q.hasFDerivAt.comp_hasDerivAt 0 hh)).clm_apply (h u x); change HasDerivAt (fun t:ℝ=> Q (g t) (F (L t) x)) (Q (Org.bracket u v) (F (L 0) x)+Q (g 0) (Q u x)) 0 at hv
    rw [hQ,he,map_one,show (1: Z≃ₗ[ℂ]Z) x=x from rfl] at hv
    have ht : (fun t:ℝ=> Q (g t) (F (L t) x))=(fun t=> F (L t) (Q v x)):=by funext t; unfold g; rw [← show (L t).coord=Ortho.oneParameter u t from (tour u).2.2 t]; exact hs ..
    rw[ht] at hv; have he':=(h u (Q v x)).unique (show HasDerivAt (fun t=> F (oathU u t) (Q v x)) _ 0 from hv); rw [he',add_sub_cancel_right]
include H HK J hd
lemma rue(u v:Ortho.Skew)(RoofP:Roof P.sym): rain u d*rain v d-rain v d*rain u d=rain (Org.bracket u v) d:=by
    apply LinearMap.ext; intro x; exact comet (chorus J H HK hd) (caravan RoofP d) (fun u y=> chime u (tour u) RoofP y) (fun v x p=> fang v RoofP x p) u v x
end YM.Mako
#print axioms YM.Mako.rue
