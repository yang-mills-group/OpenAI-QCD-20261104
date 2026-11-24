import YM.Sprig.HelenB
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
lemma sendsU(s:Signed)(p:EuPin)(h:p.Lifts s):P.sym.pin d p (P.sym.unit d)=P.sym.unit d:=by
     apply he; have ht:= hP.sections; have hp:= ht.pin d n 0 (P.sym.unit d) p s h; rw [Signed.act_zero, hP.sections.unit] at hp; apply ContinuousMap.coe_injective; rw[←hp,hP.sections.unit]; funext U; exact map_one _
lemma sendsAdj(a:Axis):P.sym.adj d a (P.sym.unit d)=P.sym.unit d:=by
     apply he; have ht:= hP.sections.star d n 0 (P.sym.unit d) a; rw [Signed.act_zero,hP.sections.unit] at ht; apply ContinuousMap.coe_injective; rw[←ht,hP.sections.unit]; funext U; rw[eye_value]; exact tilt_one ..
lemma sendsFlavor(u: FlavorTorus):P.sym.flavor d u (P.sym.unit d)=P.sym.unit d:=by
     apply he; have ht:= hP.sections.flavor d n 0 (P.sym.unit d) u; rw [hP.sections.unit] at ht; apply ContinuousMap.coe_injective; rw[←ht,hP.sections.unit]; funext U; exact map_one _
lemma sendsCharge:P.sym.charge d (P.sym.unit d)=P.sym.unit d:=by
     apply he; have ht:=hP.sections.charge d n 0 (P.sym.unit d); rw[hP.sections.unit] at ht; apply ContinuousMap.coe_injective; rw[←ht,hP.sections.unit]; funext U; exact map_one _
lemma sendsParity:P.sym.parity d (P.sym.unit d)=P.sym.unit d:=by
     apply he; have ht:=hP.sections.parity d n 0 (P.sym.unit d); rw[hP.sections.unit] at ht; apply ContinuousMap.coe_injective; rw[←ht,hP.sections.unit]; funext U; exact map_one _
omit he hP
section Complement
open Submodule
variable {X:Type*} [AddCommGroup X][Module ℂ X][FiniteDimensional ℂ X]
variable (e:InnerProductSpace.Core ℂ X)
variable (K W: Submodule ℂ X)(a:X)(h:a∉ K)
set_option quotPrecheck false
local notation "Kτ"=> Submodule.span ℂ ({a}:Set X)
-- Splitting complement avoiding unit solubility.Le qualifications commute including semilinear.
include h
lemma rates (S:Submodule ℂ X)(hp: IsCompl (K ⊔ Submodule.span ℂ {a}) S): IsCompl K (Kτ ⊔ S):=by
     have hk: Disjoint (K ⊔ Kτ) S:=hp.1
     have hh: Disjoint K Kτ:=by
           rw[Submodule.disjoint_def]; intro x hx he; obtain ⟨d,rfl⟩:=mem_span_singleton.mp he; by_cases hv:d=0; · rw[hv,zero_smul]
           exfalso; exact h (inv_smul_smul₀ hv a ▸ K.smul_mem d⁻¹ hx)
     refine ⟨Submodule.disjoint_def.mpr (fun x hx hp=>?_),codisjoint_iff.mpr ?_⟩
     · obtain ⟨r,hr,s,hs,h⟩:= Submodule.mem_sup.mp hp; have ht:s∈ K ⊔ Kτ:=by rw[show s=x-r from (by rw [←h]; abel)]; exact (K ⊔ Kτ).sub_mem ((show K ≤ K ⊔ Kτ from le_sup_left) hx) ((show Kτ ≤ K ⊔ Kτ from le_sup_right) hr)
       obtain rfl := Submodule.disjoint_def.mp hk s ht hs; rw[add_zero] at h; exact Submodule.disjoint_def.mp hh x hx (h ▸ hr)
     rw [←sup_assoc]; exact hp.sup_eq_top
omit h
structure Holds (X:Type*) [AddCommGroup X][Module ℂ X](Y:X)(K:Submodule ℂ X) (F: X→X) (s:ℂ ≃+* ℂ) : Prop where
    allF : Surjective F
    add p q: F (p+q)=F p+F q
    imp p q:F (p • q)=s p • F q
    unit : F Y=Y
    live x: x∈K ↔ F x∈K
#check Holds
lemma vote {F:X→X}{s:ℂ≃+*ℂ}(hF:Holds X a K F s) (w:Submodule ℂ X)(hw: ∀ v,v∈w ↔ ∀ y∈K⊔ Submodule.span ℂ {a},e.inner y v=0)(hf:∀ x y,e.inner (F x) (F y) = s (e.inner x y)):∀ v∈Kτ⊔w,F v∈Kτ⊔w:=by
      let W:= Kτ; let H:=K ⊔ W
      have hW(p:X)(hp:p∈W): F p∈W:=by obtain ⟨u,rfl⟩:= mem_span_singleton.mp hp; exact mem_span_singleton.mpr ⟨s u, (by rw [hF.imp,hF.unit])⟩
      have hv(y:X)(hy:y∈H):∃ x∈ H,y=F x:=by
           obtain ⟨p,hp,q,hq,rfl⟩:= Submodule.mem_sup.mp hy
           obtain ⟨r,hr⟩:= hF.allF p; have ht:r∈K:=(hF.live r).2 (hr.symm ▸ hp); obtain ⟨b,rfl⟩:= mem_span_singleton.mp hq; obtain ⟨w,rfl⟩:=s.surjective b; refine ⟨r+w • a,Submodule.mem_sup.mpr ⟨_,ht,_,mem_span_singleton.mpr ⟨w,rfl⟩,rfl⟩,?_⟩; rw [hF.add,hF.imp,hF.unit,hr]
      intro x hx; obtain ⟨p,hp,q,hq,rfl⟩:= Submodule.mem_sup.mp hx; rw[hF.add]; refine add_mem_sup (hW p hp) ((hw _).mpr fun y hy=>?_) -- args
      obtain ⟨w,hw',rfl⟩:= hv y hy; rw [hf,(hw q).mp hq w hw',map_zero]
include h
lemma spectrumL :∃ S:Submodule ℂ X, IsCompl K S ∧ a∈S ∧∀ F s,Holds X a K F s→(∀ x y,e.inner (F x) (F y)= s (e.inner x y))→∀ v∈ S,F v∈ S:=by
    letI : InnerProductSpace.Core ℂ X:=e
    letI : NormedAddCommGroup X:= e.toNormedAddCommGroup
    letI : PreInnerProductSpace.Core ℂ X := e.toCore
    letI : InnerProductSpace ℂ X:= .ofCore e.toCore
    let W:=Kτ; let Q:Submodule ℂ X:= K⊔ W; letI :CompleteSpace Q:= FiniteDimensional.complete ℂ _
    refine ⟨W ⊔ Qᗮ,rates K a h Qᗮ Q.isCompl_orthogonal, (show W ≤ W⊔Qᗮ from le_sup_left) (mem_span_singleton_self a),fun F s hF hg=> vote _ _ _ hF _ ?_ hg⟩
    intro v; exact Q.mem_orthogonal v
omit h
end Complement
end YM.Sprig
#print axioms YM.Sprig.spectrumL
