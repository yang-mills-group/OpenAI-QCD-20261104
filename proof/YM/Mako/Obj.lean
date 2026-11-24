import YM.Mako.Shad
import YM.Mako.Seed
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
open Heron Iceberg Intag.Sprig Sprig Massive.Poised.Plans.Stamp MassiveTwoEstimates
open scoped YM.Iceberg YM.Massive.Poised.Plans.Stamp
private lemma seed (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousSMul ℝ V:=inferInstance
local instance (d:ℕ):NormedSpace ℝ (Label d):=NormedSpace.restrictScalars ℝ ℂ _
local instance (d:ℕ) : ContinuousSMul ℝ (Label d) := by exact seed (Label d)
noncomputable scoped instance lore (d:ℕ):NormedSpace ℝ (Free.Symbol d):=NormedSpace.restrictScalars ℝ ℂ _
noncomputable scoped instance mayor (d:ℕ) : ContinuousSMul ℝ (Free.Symbol d) := by exact seed (Free.Symbol d)
lemma sidle {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{f:ℝ→V}{v:V}(h: HasDerivAt f v 0)(r:ℝ): HasDerivAt (fun t:ℝ=> f (t-r)) v r:=by
     have ht: HasDerivAt (fun t:ℝ=> t-r) 1 r:=(hasDerivAt_id r).sub_const r; exact (h.scomp_of_eq r ht (by simp)).congr_deriv (one_smul ..)
variable {C: Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{φ:ℕ→ℕ}
variable (E:Canopy P φ K)(X:Lanterns T E)
variable {d:ℕ}{σ:RawSym}(h:Hail.RightAuth σ)
variable {g:ℝ→EuPin}{Δ:Ortho.Skew}(hg:EuPin.Path Δ g)(v: Label d)
include h
lemma trot(r:ℝ):HasDerivAt (fun t=> projection (FullL d (g t) v)) (reachΩ Δ g hg (fun _=>1) d (projection (FullL d (g r) v))) r:=by
    let x:= FullL d (g r) v; let L:= (@projection d).toContinuousLinearMap.restrictScalars ℝ; have ht:=L.hasFDerivAt.comp_hasDerivAt 0 (full_d x Δ g hg); have hi : HasDerivAt (fun t:ℝ=> t-r) 1 r:=(hasDerivAt_id r).sub_const r; have he:= sidle ht r
    have h':∀ z:ℝ,L (FullL d (g (z-r)) x)=projection (FullL d (g z) v):=by
          intro z; unfold x; rw[←LinearEquiv.mul_apply, ←map_mul,← SpinParity.additive hg,sub_add_cancel]; rfl
    refine (he.congr_of_eventuallyEq (f₁:=fun t:ℝ=> projection (FullL d (g t) v)) (Eventually.of_forall fun i=>(h' i).symm)).congr_deriv ?_ -- argument name likely wrong.
    change projection _=_; rw[map_sum]; unfold reachΩ; simp only [LinearMap.sum_apply,LinearMap.smul_apply,Complex.ofReal_one,one_smul]; apply Finset.sum_congr rfl; intro i _; exact (joins g Δ hg i σ h x).symm
include hg
lemma stead (x:Label d)(H:projection x=0)(r:ℝ): projection (FullL d (g r) x)=0:=by
     let L:= (LinearMap.toContinuousLinearMap (reachΩ Δ g hg (fun _=>1) d)).restrictScalars ℝ; have ht:= reaps L _ (trot h hg x) r; rw[hg.1,map_one,show (1:Label d≃ₗ[ℂ] Label d) x=x from rfl,H,map_zero] at ht; exact ht
omit h hg
-- signed rotations preserve kernel, enough for improper action
structure Roof (σ:RawSym):Prop where
    right : Hail.RightAuth σ
    stable(p:EuPin)(s:Signed) (H:p.Lifts s) (d:ℕ)(x:Label d)(h:projection x=0): projection (σ.pin d p x)=0
include X in
lemma assure(h:Hail.RightAuth P.sym): Roof P.sym:=by -- use X.any k
    refine ⟨h,fun p s H d x h=>?_⟩
    let F:=X.frame 0 d; apply F.injective; rw [map_zero]; apply Subtype.ext; change (X.frame 0 d _).val= (0:K.W); rw[← (X.leaders 0 d).rotates x p s H,h,map_zero]; exact map_zero _
-- kernel downstairs
variable (R:Roof σ)
include R
lemma basin(p:EuPin) (h:projection v=0): projection (FullL d p v)=0:=by
    let B(r:EuPin):=∀ z:Label d,projection z=0→ projection (FullL d r z)=0
    have hp(r s:EuPin)(H:B r)(J:B s): B (r*s):=by intro i h; rw[map_mul,LinearEquiv.mul_apply]; exact H _ (J i h)
    let U:Subgroup EuPin:= { carrier:={r|B r ∧ B r⁻¹},one_mem':=by
                                have h:B 1:=fun x hx=>by simp [hx]
                                exact ⟨h,(by simp[h])⟩
                             mul_mem':= fun {a b} ⟨h,j⟩ ⟨h',j'⟩=> ⟨hp a b h h', (mul_inv_rev a b).symm ▸ hp b⁻¹ a⁻¹ j' j⟩
                             inv_mem':= fun {a} ⟨h,j⟩=> ⟨j,(inv_inv a).symm ▸ h⟩ }
    have hm: p∈U:=by
              apply engenders; · intro p s hs; have hf(p:EuPin)(s:Signed)(h:p.Lifts s): B p:=by intro z H; rw [auth]; exact R.stable p s h d z H -- auth sigma evar
                                 refine ⟨hf p s hs,hf p⁻¹ s⁻¹ ?_⟩; change euca (p⁻¹)=Signed.inclusionO (s⁻¹); rw [map_inv,map_inv,show euca p=Signed.inclusionO s from hs]
              intro g t; refine ⟨fun i hi=>stead R.right (tour g) i hi t,fun i hi=>?_⟩; rw[← curve_i (tour g)]; exact stead R.right (tour g) i hi _
    exact hm.1 v h
def haul(d:ℕ)(p:EuPin):Module.End ℂ (Free.Symbol d):= projection ∘ₗ (FullL d p).toLinearMap ∘ₗ (fork d).val
lemma tall(p:EuPin): haul d p (projection v)=projection (FullL d p v):=by
     let w:=(fork d).val (projection v); have ht:projection w=projection v:= DFunLike.congr_fun (fork d).property (projection v); have h:= basin (w-v) R p (by rw [map_sub,ht,sub_self]); rwa [map_sub,map_sub,sub_eq_zero] at h
lemma walk (u:Free.Symbol d)(p q:EuPin): haul d (p*q) u=haul d p (haul d q u):=by
    obtain ⟨x,rfl⟩:= Free.onto u; rw[tall x R,tall x R,tall _ R,map_mul,LinearEquiv.mul_apply]
lemma foss(u:Free.Symbol d): haul d 1 u=u:=by obtain ⟨x,rfl⟩:=Free.onto u; rw[tall x R,map_one]; rfl
def cell(d:ℕ)(p:EuPin): Free.Symbol d≃ₗ[ℂ] Free.Symbol d:=
    { haul d p with
      invFun:= haul d p⁻¹
      left_inv:= fun u=> by change haul d p⁻¹ (haul d p u)=u; rw[←walk R,inv_mul_cancel, foss R]
      right_inv:=fun u=>by change haul d p (haul d p⁻¹ u)=u; rw[←walk R,mul_inv_cancel, foss R] }
def caravan(d:ℕ): EuPin →* (Free.Symbol d≃ₗ[ℂ]Free.Symbol d):=
    ⟨⟨cell R d,LinearEquiv.ext (foss R)⟩,fun p q=>LinearEquiv.ext (fun u=>walk R u p q)⟩
lemma clanP (p:EuPin): caravan R d p (projection v)=projection (σ.pin d p v):= Eq.trans (tall v R p) (congr_arg _ (auth p v σ))
lemma howls(u:Free.Symbol d):Continuous (fun p:EuPin=> caravan R d p u):=by
     obtain ⟨v,rfl⟩:=Free.onto u; refine ((@projection d).continuous_of_finiteDimensional.comp (canvas v)).congr (fun i=>(tall v R i).symm)
include hg
lemma grace (u:Free.Symbol d) (r:ℝ):HasDerivAt (fun t=> caravan R d (g t) u) (reachΩ Δ g hg (fun _=>1) d (caravan R d (g r) u)) r:=by
     obtain ⟨v,rfl⟩:=Free.onto u; simp_rw [show ∀a:EuPin,caravan R d a (projection v)=projection (FullL d a v) from fun i=> tall v R i]; exact trot R.right hg v r
end YM.Mako
#print axioms YM.Mako.assure
#print axioms YM.Mako.grace
#print axioms YM.Mako.caravan
#print axioms YM.Mako.howls
