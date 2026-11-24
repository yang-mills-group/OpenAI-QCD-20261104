import YM.Plateau.Hero
import YM.Plateau.Crake
import YM.Plateau.Rock
import YM.Plateau.Phlox
/-! # Rank and the two equations. Genuine small gaps vs margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (p q:Flavor 6)(g:Bool)
open Massive.Oriole Compass Submodule
variable {J8:Label 8→ₗ[ℂ]Label 8}{J6:Label 6→ₗ[ℂ] Label 6} (h8:Ami 8 p q g true J8)(h6:Ami 6 p q g false J6)
variable {F8: UV.Free.Symbol 8≃ₗ[ℂ](Q.level 8)}(hf8:Prose F8 T){F6: UV.Free.Symbol 6≃ₗ[ℂ](Q.level 6)}(hf6:Prose F6 T)
local notation "V"=>MassFields.isotropic
local notation "Z"=> Q.focus MassFields.isotropic 8
local notation "K"=> p
local notation "M"=> flame p q g 8 (by decide)
local notation "U"=> arbor p q g true
local notation "W₀"=> arbor p q g false
local notation "P★"=> prismT F8 M
variable (H: Q.Domestic)(hp:p≠q)

-- analytic weights in original calibration metrics. independent of β and Omega geometry.Chi.
noncomputable def faceL : (ℂ × ℂ × ℂ) →ₗ[ℂ] Label 8 where
   toFun x:= Style p q g x.1 x.2.1 x.2.2
   map_add' x y:= by dsimp only [Prod.fst_add, Prod.snd_add, Style]; rw [add_smul,add_smul,add_smul]; abel
   map_smul' x y:= (eq_mul p q g _ _ _ x).symm
lemma face_cost :∃ A:ℝ,0<A ∧∀ x y z:ℂ, ‖x‖+‖y‖+‖z‖≤ A*‖Style p q g x y z‖:=by
    let L:=faceL p q g; have hi:Injective L:=by
         refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_); rintro ⟨x,y,z⟩ h; change Style p q g x y z=0 at h
         have h1:Poised.Plans.Stamp.Stair.laps 8 (Style p q g x y z)=0:=by rw[h]; unfold Poised.Plans.Stamp.Stair.laps; apply Finset.sum_eq_zero; intro v _; split; change ‖Poised.Stative.coord _ (0:Pol 8)‖=_; rw [map_zero,norm_zero]; rfl
         have hh:=Massive.Oriole.mission p q g true x y z; have hp:=Massive.Oriole.mission p q g false x y z; rw[h1,mul_zero,norm_le_zero_iff] at hh hp; obtain rfl:=show y=0 from hh; obtain rfl:=show z=0 from hp
         unfold Style at h; rw[zero_smul,zero_smul,add_zero,add_zero] at h; obtain rfl:= (smul_eq_zero.mp h).resolve_right (fun hz=>Harbor.meson_visible p q _ (d:=8) (by omega) (quPul g) ((congr_arg UV.Free.projection hz).trans (map_zero _))); rfl
    let P:= LinearEquiv.ofInjective _ hi; let F:= P.symm.toLinearMap.toContinuousLinearMap
    refine ⟨3*‖F‖+1,by positivity,fun x y z=>?_⟩; let t:=(x,y,z); let i:= Style p q g x y z; have hx: ‖t‖ ≤ ‖F‖* ‖i‖:= calc
         ‖t‖=‖F (P t)‖:= by rw [show F (P t)=t from P.symm_apply_apply _]
         _ ≤ _:= F.le_opNorm _
    have hh: ‖x‖ ≤ ‖t‖:= le_max_left ..; have hP: ‖(y,z)‖≤ ‖t‖:= le_max_right ..; have hv: ‖y‖≤‖(y,z)‖:= le_max_left ..; have hz: ‖z‖≤‖(y,z)‖:=le_max_right ..; change _ ≤ _*‖i‖; linarith only [hx,hh,hP,hv,hz,norm_nonneg i]
variable (A:ℝ)(hA:∀ x y z:ℂ,‖x‖+‖y‖+‖z‖≤ A*‖Style p q g x y z‖)(ht:0 < A)
include h8 hp hA ht T
lemma arms (x y z:ℂ) (Y:Label 8)(hh:Q.focus V 8 Y=0)(B C:ℝ)(hb:‖Style p q g x y z-Y‖ ≤ B)(hC:A*(‖J8.toContinuousLinearMap‖*B) ≤ C):∃ x' y' z':ℂ,Q.focus V 8 (Style p q g x' y' z')=0 ∧ ‖x-x'‖+‖y-y'‖+‖z-z'‖ ≤ C:=by
    let F:=J8.toContinuousLinearMap; let X:=Style p q g x y z; let N:= LinearMap.ker (Q.focus V 8); have he:Y∈N:=hh; obtain ⟨x',y',z',h⟩:= Massive.Oriole.rose p q g (F Y) hp (h8.root Y).1 ((h8.root Y).2 rfl)
    have hw :∀ v i,v∈N ↔ viewS g true P.sym 8 i v∈N:=by
         rintro v (i|s); · change Z v=0 ↔ Z (P.sym.flavor _ i v)=0; rw [← T.f]; exact (map_eq_zero_iff _ (T.flavor i).injective).symm
         have hp:Z (P.sym.pin 8 s.1.val.1 v)= T.spin s.1.val.1 (Z v):=(T.w _ _ s.1.prop.1 8 V v).symm
         change Z v=0 ↔ Z (P.sym.pin _ s.1.val.1 v)=0; rw [hp]; exact (map_eq_zero_iff _ (T.spin s.1.val.1).injective).symm
    refine ⟨x',y',z', (show F Y=Style p q g x' y' z' from h) ▸ (show Z (F Y)=0 from (h8.pays _ _ hw).1 _ he),?_⟩ -- ▸ note if h eq Style expression def
    have hP : ‖X-J8 Y‖ ≤ ‖F‖*B :=by rw [← show J8 X=X from h8.same _ (worthM ..),← map_sub]; exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    have he: X-J8 Y= Style p q g (x-x') (y-y') (z-z'):=by rw [show J8 Y= _ from h]; exact eq_diff ..
    rw [he] at hP; exact (hA ..).trans ((mul_le_mul_of_nonneg_left hP ht.le).trans hC)
end YM.Sprig
#print axioms YM.Sprig.face_cost
#print axioms YM.Sprig.arms
