import YM.Elms.Bracken
import YM.Patria.Odors
/-!
# Kinetic comparison at birth over a ready basis.
Pure overdispersion separately and explicitly absorbs the unprepared spherical reach comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate -- shadow moon.Q.F.
open Cove Creek
variable {Y:SourceRead.TaperHol}{p:Label d}{V:Knot p}{l m k n0 j:ℕ}
lemma crestBorn (X:Drape)(h:X∈ phrase k j): Draft X k j:=whereby_self X ▸ (shelf h).draws 1
lemma shiftCorrespond (X:Drape)(h:X∈phrase k j):∀ (n:Side)(x y:Cover), Patria.march y (X n x)=X n (x+y):=by
    obtain ⟨S,ht⟩:=(crestBorn X h).exists; obtain ⟨F,rfl,hF,hK⟩:=ht.funded; exact fun n a b=> Patria.Canvas.stylus b _ _ _
lemma moonF (h: Requisite Y p V): moon (polarity V.s) (V.tool P n o):=by
    intro U; change Grass.Hom (polarity V.s) (_+_); refine (affinity o h.mantle U).add (Grass.Hom.smul ?_ _); rw [← h.finance]; exact affinity o h.rent U
lemma lawEv (h:Requisite Y p V)(l:List Axis): evoc (V.tool P) l = evoc V.X l+(V.c P:ℂ) • evoc V.Y l:=by unfold Knot.tool; rw [emanated,layered]
lemma uproot(x y:Drape)(f g s t:ℕ)(hX:Draft x g s)(hY: Draft y f t) : ∃ C:ℝ,0≤ C ∧ ∀ᶠ r:ℕ in atTop,∀ k m d₀ j:ℕ,∃ D:ℝ,1≤D∧ ∀ (P:BudgetPoint)(K:Side)(p:Cover)(α β:ℝ), 0<α → P.order=k→P.power=m→2*(r+1)<K.val → |β| * levy f t P.threshold α ≤ levy g s P.threshold α → (let Y := (x+(β:ℂ) • y) K p; let a:ℝ:= (levy g s P.threshold α)⁻¹; Flame ⇑((a:ℂ) • Y) P (pot (r+1) K p) (wrap K p) α d₀ j D ∧ ∀ U:Grid K, Creek.load (fun _=>α) (((a:ℂ) • Y :Insertion K 6) U)≤ C*( (P.threshold^g)⁻¹+(P.threshold^f)⁻¹)):=by
      obtain ⟨A,hA,h⟩:=lantern x g s hX; obtain ⟨B,hB,h'⟩:= lantern y f t hY; refine ⟨A+B,add_nonneg hA hB,?_⟩; filter_upwards [lease_flame x g s hX,lease_flame y f t hY] with r hs ht k m d j; obtain ⟨D,hD,hG⟩:=hs k m d j; obtain ⟨E,hE,hW⟩:= ht k m d j; refine ⟨1+(D+E),le_add_of_nonneg_right (add_nonneg hD hE), fun P K p u v hu hk hm hr hV=>?_⟩; let Vc:= levy g s P.threshold u; let Vr:= levy f t P.threshold u; have hp:=P.threshold_pos; have hv:0<Vc:=by unfold Vc levy; positivity
      have hw:0<Vr:=by unfold Vr levy; positivity
      let Z : Insertion K 6:= x K p + (v:ℂ) • y K p; let mC:= (Vc⁻¹:ℝ); let m':= Vc⁻¹*v; let p':= (pot (r+1) K p); have ht:mC*|v| ≤ Vr⁻¹:=by rw [← one_div]; apply (le_div_iff₀ hw).mpr; unfold mC; rw [mul_assoc,inv_mul_le_iff₀ hv]; exact hV.trans_eq (mul_one Vc).symm
      have hQ:(↑(Vc⁻¹):ℂ) • Z= ((↑mC:ℂ) • x K p)+(↑m':ℂ) • y K p :=by unfold Z m' mC; rw [smul_add,smul_smul,Complex.ofReal_mul]
      have hc:|m'| ≤ Vr⁻¹:=by unfold m'; rw [abs_mul,abs_of_pos (inv_pos.mpr hv)]; exact ht
      change Flame ⇑((↑mC:ℂ) • Z:Insertion K 6) P _ _ _ _ _ _∧ ∀ U,Creek.load _ (((↑mC:ℂ) • Z:Insertion K 6) U) ≤ _
      rw [hQ]; constructor
      · let F:= hG P K p u hu hm hk hr; have H:=hW P K p u hu hm hk hr; have hX:= Girdle.flare_add _ _ _ _ (Girdle.flare_by _ _ _ F (↑mC:ℂ)) (Girdle.flare_by _ _ _ H (↑m':ℂ)) hu.le
        apply leFlame hX; rw [Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ mC from inv_nonneg.mpr hv.le),Real.norm_eq_abs]; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hc (mul_nonneg hE hw.le)) _); rw [mul_left_comm (Vr⁻¹), inv_mul_cancel₀ hw.ne',mul_one,mul_left_comm mC, inv_mul_cancel₀ hv.ne',mul_one]; linarith
      intro U; let Y:= y K p; apply le_trans (Stamp.floss_add u ((↑mC:ℂ) • (⇑(x K p):Density K 6)) ((↑m':ℂ) • (⇑Y:Density K 6)) _)
      rw [Pi.smul_apply,Pi.smul_apply, Creek.load_scale, Creek.load_scale,Complex.norm_real,Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hv.le),Real.norm_eq_abs]
      apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (h u hu K p U) (inv_nonneg.mpr hv.le)) (mul_le_mul hc (h' u hu K p U) (Creek.load_nn ..) (inv_nonneg.mpr hw.le)))
      calc _= A*(P.threshold^g)⁻¹+B*(P.threshold^f)⁻¹:=by unfold Vc Vr levy; field_simp <;> ring
           _≤ _ :=by rw [add_mul, mul_add,mul_add]; linarith [show 0≤ A* (P.threshold^f)⁻¹ by positivity, show 0≤ B*(P.threshold^g)⁻¹ by positivity]
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
