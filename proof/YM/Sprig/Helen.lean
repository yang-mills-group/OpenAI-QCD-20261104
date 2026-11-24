import YM.Sprig.Poste
import YM.Sprig.Moats
/-!
  Simultaneous kernel invariance on the actual signed symmetries (eventually). Splitting.Bases use after this stage without loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig.Canopy
open Function Filter Set Matrix Finset MeasureTheory
open Massive QCD QCD.Lat Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open _root_.YM.Fir Massive.Fir Choir Pollens HarmonyF
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
open Compass
variable {β e:ℝ}(hc:C.Path β e)(hφ:Tendsto φ atTop atTop)(hP:P.System)(hQ:Q.Harmony P φ)(hv:Foil P Q T)
variable (x y: Label d)(i:Points 2)(hi:i∈conf 2)(p:EuPin)(s:Signed)(ht:p.Lifts s)
noncomputable abbrev readK (i:Points 2)(x y:UV.Label d):ℂ:= UV.Free.wick (fun _ : Fin 2=> d) i (![x,y])
local notation "W"=>Q.total
local notation "f" i:arg=> E.V i
include hQ
lemma bonus (hx:i∈conf 2): Tendsto (fun k=> Q.total 2 ((E.B k).r • i) ![cut E k x,cut E k y]) atTop (𝓝 (readK i x y)):=by
     let D:Fin 2→ℕ:=fun _=> d; have h:= sensorM hQ E D (![x,y]) i hx; refine h.congr fun k=>?_ ; unfold rCorr; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg (Q.total 2 _); funext j; fin_cases j<;>rfl
omit hQ
lemma cut_unit : ∀ᶠ k in atTop,E.cut k (P.sym.unit d)=Q.focus none d (P.sym.unit d):=by filter_upwards [E.wohlen d] with k hk; unfold cut choiceT; rw[((E.checkedW k).acts d hk.level).unit]
lemma cut_pin:∀ᶠ k in atTop,∀ x:Label d,∀ p:EuPin,∀ s:Signed,p.Lifts s→ E.cut k (P.sym.pin d p x)=T.spin p (E.cut k x):=by
    filter_upwards [E.wohlen d] with k hk x p s ht; unfold cut choiceT; rw [((E.checkedW k).acts _ hk.level).pin _ _ _ ht,T.w p s ht]; rfl
lemma cut_flavor:∀ᶠ k in atTop,∀ x:Label d,∀ u:FlavorTorus,E.cut k (P.sym.flavor d u x)= T.flavor u (E.cut k x):=by filter_upwards [E.wohlen d] with k hk x u; unfold cut choiceT; rw [((E.checkedW k).acts _ hk.level).flavor _ _, T.f]
lemma cut_adj:∀ᶠ k in atTop,∀ x:Label d,∀ a:Axis, E.cut k (P.sym.adj d a x)=T.adj a (E.cut k x):=by filter_upwards [E.wohlen d] with k hk x a; unfold cut choiceT; rw [((E.checkedW k).acts _ hk.level).adj _ _, T.a]
lemma cut_charge:∀ᶠ k in atTop,∀ x:Label d,E.cut k (P.sym.charge d x)= T.charge (E.cut k x):=by filter_upwards [E.wohlen d] with k hk x; unfold cut choiceT; rw [((E.checkedW k).acts _ hk.level).charge _,T.c]
lemma cut_parity:∀ᶠ k in atTop,∀ x:Label d,E.cut k (P.sym.parity d x)= T.parity (E.cut k x):=by filter_upwards [E.wohlen d] with k hk x; unfold cut choiceT; rw [((E.checkedW k).acts _ hk.level).parity _,T.p]
include hi hQ hv
lemma readMap (Y:Label d≃ₗ[ℂ]Label d)(A:Ortho)(S:Q.W≃ₗ[ℂ] Q.W)(h:∀ᶠ k in atTop,∀ x:Label d,E.cut k (Y x)=S (E.cut k x))(H:∀ (i:Points 2),i∈conf 2→∀ v,Q.total 2 (Points.move A i) (S ∘v)= Q.total 2 i v): readK (Points.move A i) (Y x) (Y y)=readK i x y:=by
     let g:=Ortho.move A; have hp: Points.move A i∈conf 2:=fun p q he=> hi (Ortho.move_injective _ he)
     apply tendsto_nhds_unique (bonus E hQ _ _ _ hp); refine (bonus E hQ x y i hi).congr' (EventuallyEq.symm ?_); filter_upwards [h] with k hk
     let K:= E.B k; rw [hk,hk, show ![S (E.cut k x), S (E.cut k y)]= (⇑S) ∘ (![E.cut k x,E.cut k y]) from funext fun i=>by fin_cases i <;> rfl]
     rw [show K.r • Points.move A i=Points.move A (K.r • i) from PiLp.ext fun j=>(map_smul (Ortho.motion A) K.r (i j)).symm]; exact H _ (vital P φ Q hQ _ hi _ K.realH) _
include hc hφ hP E
lemma oppositeK(a:Axis):readK (HarmonyF.tilted a i) (P.sym.adj d a y) (P.sym.adj d a x)=star (readK i x y):=by
    let A:=Signed.reflect a; let S:= T.adj a; let Y:=P.sym.adj d a; have hp: HarmonyF.tilted a i∈conf 2:=fun p q h=> Fin.revPerm.injective (hi (Ortho.move_injective _ h))
    apply tendsto_nhds_unique (bonus E hQ (Y y) (Y x) _ hp); refine (show Tendsto _ _ _ from (((show Continuous (star:ℂ→ℂ) from continuous_star).tendsto (readK i x y)).comp (bonus E hQ x y i hi))).congr' (EventuallyEq.symm ?_); filter_upwards [cut_adj (d:=d) T E] with k hk
    let K:=E.B k; change Q.total 2 _ (![_,_])=star (Q.total 2 _ (![_,_])); unfold Y; rw [hk,hk]
    rw [show (![S (cut E k y), S (cut E k x)])= ⇑(T.adj a) ∘ (![cut E k x,cut E k y]) ∘ Fin.rev from funext fun i=>by fin_cases i<;>rfl, show K.r • tilted a i = tilted a (K.r • i) from PiLp.ext fun j=>(map_smul (Ortho.motion A) _ _).symm]
    exact HarmonyF.swung hc hQ hφ hP T _ (vital P φ Q hQ i hi _ K.realH) (![cut E k x,cut E k y]) a
end YM.Intag.Sprig.Canopy
#print axioms YM.Intag.Sprig.Canopy.readMap
#print axioms YM.Intag.Sprig.Canopy.oppositeK
