import YM.Plateau.Snow
import YM.Plateau.Peak
import YM.Sprig.Echoes
import YM.Plateau.Belt
import YM.Plateau.Curl
/-
All shape rotations use public label metric at reference, get uniform before L.
We exploit existence of an invariant core from ANY earlier shelf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (hP:P.System)
variable (n: Side)(he:Injective (P.candidate d n 0))
open Massive.Oriole
open LinearMap
-- character tags. NoneSigned vac flavor.L upstairs.C.Cal.T.

open Compass Submodule
variable (p q: Flavor 6)(g t:Bool)
variable {J:Label d→ₗ[ℂ] Label d}(hJ:Ami d p q g t J) (Z:Label d→ₗ[ℂ]Q.W)
noncomputable abbrev ZΦ (i:Vesta g t): Q.W ≃ₗ[ℂ] Q.W:= Sum.elim (fun i=>T.flavor i) (fun i=>T.spin i.1.val.1) i
noncomputable def lensP :Submodule ℂ Q.W where
     carrier := {x|∀ i: Vesta g t,ZΦ T g t i x=(quip p q g t i) • x}
     zero_mem' :=fun i=> (map_zero _).trans (smul_zero _).symm
     add_mem' :=by intro x y hx hy i; rw [map_add,hx i,hy i,smul_add]
     smul_mem' :=by intro c x h i; rw [map_smul,h i, smul_comm]
local notation "V"=>ZΦ T g t
local notation "W"=> viewS g t P.sym d
local notation "A" => bluff p q g t d
local notation "C"=> lensP T p q g t
local notation "S"=> C ⊓ Q.level d
variable (hz: LinearMap.range Z= Q.level d)(hZ:∀ (i:Vesta g t)x,Z (viewS g t P.sym d i x)=ZΦ T g t i (Z x))
include hJ hZ hz
lemma habitats : Submodule.map Z A=lensP T p q g t ⊓ Q.level d:=by
      have hH(x:Label d)(i:Vesta g t): x∈LinearMap.ker Z ↔ W i x∈ LinearMap.ker Z:= (by simp only [LinearMap.mem_ker, hZ]; exact (map_eq_zero_iff _ (V i).injective).symm)
      apply le_antisymm; · rintro _ ⟨x,hx,rfl⟩; refine ⟨fun i=> ?_,?_⟩; rw [← hZ, (gateL p q g t _ x).1 hx, map_smul]; exact hz ▸ ⟨x,rfl⟩
      intro x h; obtain ⟨hx,hp⟩:= Submodule.mem_inf.mp h; obtain ⟨w,rfl⟩:= (show x∈ LinearMap.range Z from hz.symm ▸ hp); refine ⟨J w,hJ.root w,Eq.symm (sub_eq_zero.mp ?_)⟩; rw [← map_sub]; refine (hJ.pays (ker Z) P.sym hH).2 w ?_; intro i; change Z (_-_) = 0; rw [map_sub,hZ,map_smul,hx i,sub_self]
variable (F: Free.Symbol d ≃ₗ[ℂ] (Q.level d))(hf: YM.Sprig.Prose F T)(hQ:Domestic Q)
omit hZ hz
noncomputable def prismT (F:Free.Symbol d≃ₗ[ℂ](Q.level d)): Label d→ₗ[ℂ] Q.W:= (Q.level d).subtype ∘ₗ (F.toLinearMap ∘ₗ UV.Free.projection)
include hf
lemma pump : Submodule.map (prismT F) A = lensP T p q g t ⊓ Q.level d:=by
     apply habitats T p q g t hJ
     · apply le_antisymm; · rintro _ ⟨x,rfl⟩; exact (F _).property
       intro x hx; obtain ⟨y,hy⟩:= UV.Free.onto (F.symm ⟨x,hx⟩); exact ⟨y, congr_arg Subtype.val ((congr_arg F hy).trans (F.apply_symm_apply _))⟩
     rintro (i|u) x; exact (hf.turns x i).symm; exact (hf.rotates x _ _ u.1.prop.1).symm
omit hf
variable (R:Averaging)(hR:t=true→∀ s: Signed, Averaging.permute s R=R)
include hJ hQ hR
lemma raysW : Submodule.map (Q.focus R d) A = lensP T p q g t ⊓ Q.level d:=by
     refine habitats T p q g t hJ _ (hQ.tops R d) ?_
     rintro (i|u) x; exact (T.f i d R x).symm; have hh:=T.w _ _ u.1.prop.1 d R x; rw[hR u.2.prop] at hh; exact hh.symm -- signature?
omit hJ hR
variable {J6:Label 6→ₗ[ℂ]Label 6}(h6:Ami 6 p q g false J6)(h:p ≠ q)
variable {F6:Free.Symbol 6≃ₗ[ℂ](Q.level 6)} (hf6:Prose F6 T)
include h6 h hf6
lemma vivid : Injective ((Q.focus R 6).domRestrict (bluff p q g false 6)):=by
    let X:= bluff p q g false 6; let Wk:=lensP T p q g false ⊓ Q.level 6; let F:= prismT F6; let f:=Q.focus R 6
    have hb : LinearMap.range (F.domRestrict X)=Wk:=(LinearMap.range_domRestrict X F).trans (pump T p q g false h6 _ hf6)
    have hK: LinearMap.range (f.domRestrict X)=Wk:=(LinearMap.range_domRestrict X f).trans (raysW T p q g false h6 hQ R fun h=>Bool.noConfusion h)
    have hz_:Injective (F.domRestrict X):=by
         refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun i hi=>?_) -- ker_eq_bot.mpr? check
         obtain ⟨M,hM⟩:= bud6 p q h i.val i.prop.1; let v:= mesonCode 6 p q M le_rfl; have hV : F6 (projection i.val)=0:=Subtype.ext hi; rw [map_eq_zero_iff _ F6.injective,show i.val=v from Subtype.ext hM] at hV
         have hM' : M=0:=by by_contra hv; exact UV.Free.Harbor.meson_visible p q M le_rfl hv hV
         apply Subtype.ext; apply Subtype.ext; rw [hM,hM',bilinear]; simp -- goal cast X
    have he: Module.finrank ℂ X=Module.finrank ℂ ↥(LinearMap.range (f.domRestrict X)):= by rw [hK,←hb]; exact (LinearEquiv.ofInjective _ hz_).finrank_eq
    let T':= (f.domRestrict X).rangeRestrict; have hT := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr (f.domRestrict X).surjective_rangeRestrict; exact fun i j hh=> hT (Subtype.ext hh)
local notation "U"=>MassFields.isotropic
local notation "Ω"=> flame p q g
lemma rate6 (M: Spike)(hM:M≠0): Q.focus R 6 (mesonCode 6 p q M (by decide))≠0:=by
     let x:=mesonCode 6 p q M le_rfl; have hx: x∈ bluff p q g false 6:= ⟨charm p q 0 0 M,fun h=> Bool.noConfusion h⟩
     intro ht; have ht':(⟨x,hx⟩:↥(bluff p q g false 6))=0:=vivid T p q g hQ R h6 h hf6 (ht.trans (map_zero (Q.focus R 6)).symm); exact UV.Free.Harbor.meson_visible p q M le_rfl hM ((congr_arg UV.Free.projection (show x=0 from congr_arg Subtype.val ht')).trans (map_zero _))
omit h6 hf6
variable {J8: Label 8→ₗ[ℂ]Label 8}(h8:Ami 8 p q g true J8) {F8:Free.Symbol 8≃ₗ[ℂ] (Q.level 8)}(hf8:Prose F8 T)
local notation "Fp"=>prismT F8
local notation "Ω'"=> flame p q g 8 (by decide)
lemma heartL (x:Label d) (hp:6≤d)(hg:x=flame p q g d hp) : x∈bluff p q g true d:=by
     subst x; refine ⟨charm p q 0 0 _,fun _ w s h z hz=> ?_⟩; change pinAct w (bilinear p q _ 0 0)=_; rw [acclaim p q s w h,hem_ground,marked_root,hz,Massive.Oriole.nourish]; simp only [one_mul,Complex.ofReal_one,one_smul]; rfl
include hf8 h8
lemma reachR : lensP T p q g true ⊓ Q.level 8= Submodule.span ℂ ({Fp (Ω')}:Set Q.W):=by
     rw [← pump T p q g true h8 _ hf8]; apply le_antisymm
     · rintro _ ⟨x,hx,rfl⟩; obtain ⟨t,y,z,h⟩:= Massive.Oriole.rose p q g x h hx.1 (hx.2 rfl)
       refine Submodule.mem_span_singleton.mpr ⟨t,?_⟩; have hb(t:Bool):Fp (arbor p q g t)=0:=by change (F8 (projection _)).val=0; rw[projection_void,map_zero]; rfl
       rw[h,map_add,map_add,map_smul,map_smul,map_smul,hb,hb,smul_zero,smul_zero,add_zero,add_zero]
     apply Submodule.span_le.mpr; rintro x (rfl) -- singleton
     exact ⟨_,heartL p q g hQ h (Ω') (by omega) rfl,rfl⟩ -- order
end YM.Sprig
#print axioms YM.Sprig.vivid
#print axioms YM.Sprig.rate6
#print axioms YM.Sprig.reachR
