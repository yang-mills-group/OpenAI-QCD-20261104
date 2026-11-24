import YM.Sprig.Spike
/-! A simultaneous intertwiner at all finite signed rotations and internal charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
open Compass
variable {β e:ℝ}(hc:C.Path β e)(hφ:Tendsto φ atTop atTop)(hP:P.System)(hQ:Q.Harmony P φ)(hv:Foil P Q T)
variable (n:Side)(he:Injective (P.candidate d n 0))
-- Preserve Unit. important off-horizon.
open Massive.Patria.Exposure
local notation "Bn"=> (P.candidate d n 0)
include he hP
lemma seed (K:Submodule ℂ (Label d)) (a:Label d) (hx: a∉K) :∃ S:Submodule ℂ (Label d), IsCompl K S∧ a∈ S ∧∀ F s,Holds _ a K F s→(∀ x y,Chloe.pollen P n (F x) (F y)= s (Chloe.pollen P n x y))→∀ v∈ S,F v∈ S:=by
    let e:InnerProductSpace.Core ℂ (Label d):={
        inner:=Chloe.pollen P n
        conj_inner_symm x y:= Chloe.sparks P n y x
        re_inner_nonneg x:= Chloe.pp0 P n x
        add_left x y z:= Chloe.timely P n x y z
        smul_left x y r:= Chloe.money P n r x y
        definite x h:=by by_contra hp; exact (Chloe.ppU P n x he hp).ne' (congr_arg Complex.re h)
    }
    exact spectrumL e K a hx
noncomputable abbrev nulls (d:ℕ):= LinearMap.ker (@UV.Free.projection d)
local notation "Kz"=> (nulls d)
local notation "a"=> P.sym.unit d
include hQ E hc hφ hv
lemma owing : ∃ S:Submodule ℂ (Label d),IsCompl (nulls d) S ∧ P.sym.unit d ∈ S∧ ∀ x:Label d, x∈ S→ ((∀ p:EuPin,∀ s:Signed,p.Lifts s→ P.sym.pin d p x∈S)∧ (∀ u,P.sym.flavor d u x∈S)∧ P.sym.charge d x∈S∧ (∀ t,P.sym.adj d t x∈ S)∧ P.sym.parity d x∈S):=by
    obtain ⟨S,hS,hA,H⟩:= seed hP n he Kz a (unitV T E hc hφ hP hQ hv); refine ⟨S,hS,hA,fun x hx=> ⟨fun p s h=>?_,fun u=>?_,?_,fun t=>?_,?_⟩⟩; -- holdings
    · exact H (P.sym.pin d p) (RingEquiv.refl _) ⟨(P.sym.pin d p).surjective,map_add _,map_smul _, sendsU hP n he _ _ h,fun x=> (rotateP T E hQ hv x p s h).symm⟩ (fun x y=> Chloe.brood P n x y hP p s h) _ hx
    · exact H (P.sym.flavor d u) (RingEquiv.refl _) ⟨(P.sym.flavor d u).surjective,map_add _,map_smul _, sendsFlavor hP n he _,fun x=> (flavorV T E hQ hv x u).symm⟩ (fun x y=> Chloe.fauna P n x y hP u) _ hx
    · exact H (P.sym.charge d) (RingEquiv.refl _) ⟨(P.sym.charge d).surjective,map_add _,map_smul _, sendsCharge hP n he,fun x=> (chargeV T E hQ hv x).symm⟩ (fun x y=> Chloe.gloss P n x y hP) _ hx
    · exact H (P.sym.adj d t) starRingAut ⟨(P.sym.adj d t).surjective,map_add _,map_smulₛₗ _, sendsAdj hP n he _,fun x=> (adornV T E hc hφ hP hQ hv x t).symm⟩ (fun x y=> Chloe.figurine P n x y hP t) _ hx
    exact H (P.sym.parity d) (RingEquiv.refl _) ⟨(P.sym.parity d).surjective,map_add _,map_smul _, sendsParity hP n he,fun x=> (parityV T E hQ hv x).symm⟩ (fun x y=> Chloe.parityE P n x y hP) _ hx
omit E hc hφ hv hP hQ he
-- equivariance correcting raw form. On Omega all tags present. eventual atlas.Sensor.Real.System.
structure Qua (P:Calibration C)(d:ℕ) where
    liftS : UV.Free.Symbol d →ₗ[ℂ] Label d
    right x : projection (liftS x)=x
    aligned : Skin P.sym d (liftS.comp projection)
variable (So:Submodule ℂ (Label d))(J: IsCompl (nulls d) So)
section xyz
variable {X Y: Type}[AddCommGroup X][AddCommGroup Y][Module ℂ X][Module ℂ Y](p:Y→ₗ[ℂ]X)(Z:Submodule ℂ Y)(hJ:IsCompl p.ker Z)(hOnt:Surjective p)
include hJ hOnt
lemma finds :∃ liftS:X→ₗ[ℂ] Y, (∀ x,p (liftS x)=x)∧∀ x:Y, liftS (p x)∈ Z∧x-liftS (p x)∈ p.ker:=by
     let Kb:= p.domRestrict Z; have hc: Function.Bijective Kb:=⟨LinearMap.injective_domRestrict_iff.mpr hJ.disjoint.symm,(LinearMap.surjective_domRestrict_iff hOnt).mpr hJ.symm.codisjoint⟩
     let Y' := LinearEquiv.ofBijective Kb hc; let g:= Z.subtype ∘ₗ Y'.symm.toLinearMap; have hg (x):p (g x)=x:= Y'.apply_symm_apply x
     exact ⟨g,hg,fun x=>⟨(Y'.symm _).property,(LinearMap.mem_ker.mpr (by rw [map_sub,hg,sub_self]))⟩⟩
omit hJ hOnt
lemma hereG(S:Submodule ℂ (Y))(K:IsCompl (p.ker) S)(g:Y→ₗ[ℂ] Y)(hk :∀ x,g x∈ S∧ x-g x∈ p.ker)(F:Y≃+Y)(hF:∀ v∈ S,F v∈ S)(h:∀ v∈ p.ker,F v∈ p.ker)(x:Y): g (F x)=F (g x):=by
        apply sub_eq_zero.mp; apply Submodule.disjoint_def.mp K.disjoint _ _ (by exact S.sub_mem (hk (F x)).1 (hF _ (hk x).1)); have he: g (F x)-F (g x)=F (x-g x)-(F x-g (F x)):=by rw [map_sub]; abel
        rw[he]; exact (p.ker).sub_mem (h _ (hk _).2) (hk _).2

lemma unitSplit(u:Y)(h:u∈ Z)(aK:Y→Y)(hk:∀ x,aK x∈Z∧x-aK x∈p.ker)(hJ:IsCompl p.ker Z) : aK u=u:=Eq.symm (sub_eq_zero.mp (Submodule.disjoint_def.mp hJ.disjoint _ (hk u).2 (Z.sub_mem h (hk _).1)))
end xyz
include E hc hφ hP hQ he hv
set_option maxHeartbeats 770000
lemma funds :Nonempty (Qua P d):=by
     obtain ⟨Y,hY,hA,hp⟩:=owing T E hc hφ hP hQ hv n he
     obtain ⟨L,hL,hL'⟩:= finds (X:=UV.Free.Symbol d) (Y:=UV.Label d) (@UV.Free.projection d) Y hY (UV.Free.onto (d:=d)); let g:=L.comp projection
     have hm(v):g v∈ Y ∧v-g v∈ nulls d:=hL' v
     refine ⟨L,hL,?_,?_,?_,?_,?_,?_⟩ -- flatten
     · intro x p s h; exact hereG (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y hY g hm (P.sym.pin d p).toAddEquiv (fun v hv=>(hp v hv).1 _ _ h) (fun v he=>by exact (rotateP T E hQ hv v p s h).2 he) x
     · intro x t; exact hereG (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y hY g hm (P.sym.adj d t).toAddEquiv (fun v h=>(hp v h).2.2.2.1 _) (fun v he=>by exact (adornV T E hc hφ hP hQ hv v t).2 he) x
     · intro x; exact hereG (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y hY g hm (P.sym.charge d).toAddEquiv (fun v h=>(hp v h).2.2.1) (fun v h=>by exact (chargeV T E hQ hv v).2 h) x
     · intro x u; exact hereG (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y hY g hm (P.sym.flavor d u).toAddEquiv (fun v h=>(hp v h).2.1 u) (fun v h=>by exact (flavorV T E hQ hv v u).2 h) x
     · intro x; exact hereG (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y hY g hm (P.sym.parity d).toAddEquiv (fun v h=>(hp v h).2.2.2.2) (fun v h=>by exact (parityV T E hQ hv v).2 h) x
     exact unitSplit (X:=UV.Free.Symbol d) (Y:=Label d) (@UV.Free.projection d) Y a hA g hm hY
end YM.Sprig
#print axioms YM.Sprig.funds
#print axioms YM.Sprig.seed
