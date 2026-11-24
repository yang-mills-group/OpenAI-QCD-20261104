import YM.MassiveQCD.Plate.Shift
import YM.MassiveQCD.Venture.Fair
/-! # Transition to cooled traction after mask mergers
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {I J U V E: Type}[Fintype I]
variable (I : Type)[Fintype I]
noncomputable def radial (Y:Ruby.Hue c N J):Ruby.Hue c (ample N I) J:= ⟨Y.bud,fun i U=> Apron.bearing I c N (Y.mean i U)⟩
-- NB energy bound after orientation at θ.
variable {I}
-- Coupon.Y gauge real -- currently Surround needs Color in Mint but doesn't need physical Flavor/Spectral imposes. Vows variant.
variable {t v u a w B:ℝ}{k:ℕ} (p:I→ Site c)(θ:ℝ) (S:Support c)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "pay"=> Apron.bearing I c N
lemma real_sector (x:EvenA c N): b! (rootR R K x)=pay x:= Apron.Grove.braces ..
variable (Y:Ruby.Hue c N J)
lemma payT (i:J)(U:Grid c): ‖token c M θ ((radial I Y).mean i U)‖= ‖token c N θ (Y.mean i U)‖:=by rw [skill,skill]; exact (congr_arg _ (Apron.guide I _ θ)).trans (Apron.current I _)
lemma pushGate (I:Type)[Fintype I](x:EvenA c N)(hx:Gated S x): Gated S (Apron.bearing I c N x):=by
   refine effects (embed (Ribbon.shapeE N I c)) ?_ _ hx; intro i hi; rw [embed_atom]; apply Creek.marked; exact mem_filter.mpr ⟨mem_univ _,locus N i (I:=I) |>.symm ▸ (mem_filter.mp hi).2⟩ -- notation issue
lemma WaxGov (h:Wax Y t k v u θ) : Wax (radial I Y) t k v u θ:=by
    have hx:=h.burns; refine ⟨⟨fun i U V hf ht=> congr_arg (Apron.bearing I c N) (hx.bond i U V hf ht),fun i=> (pay).toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hx.meas i),fun i U hv ht=> hv ?_,fun i U=>pushGate _ I _ (hx.lives ..)⟩,?_⟩; · exact (congr_arg (pay) (by_contra fun h=> hx.non i U h ht)).trans (map_zero _)
    obtain ⟨w,hf,H⟩:=h.expense; exact ⟨w,hf,fun i U=> (payT (I:=I) θ Y i U).trans_le (H i U)⟩
structure Pill (p:Patron.Rail c N J)(t b:ℝ)(k:ℕ)(A U:ℝ) : Prop where
   uses : p.Reg t
   pigment i: shadeG (p.warp i)
   sold : Quits p k 1 U A b
lemma paySector (f:Grid c→ EvenA c N)(h:shadeG f): shadeG (pay ∘ f):= fun i k=> (Ribbon.gaze N k (f _).val I).trans (congr_arg _ (h i k)) -- multiplication
variable (N)(q:I→Bool)(F: Patron.Rail c (ample N I) U)(φ r:ℝ)
local notation "pay₀"=> changeBill N p r φ θ
noncomputable def pursue: Patron.Rail c (ample N I) U:= ⟨F.addr,fun i U=> changeBill N p r φ θ (F.warp i U)⟩
local notation "P"=> pursue N p θ F φ r -- order binder
lemma pupil (x:Grid c)(i:U): (P).warp i x=pay₀ (F.warp i x):=rfl
lemma glimpse (h:0<φ)(G: Grid c→EvenA c (ample N I)) (hp:shadeG G)(hx:∀ U,Well N p φ q (G U)) : shadeG (pay₀ ∘ G):=fun x z=>congr_arg Subtype.val ((changeColor N p r φ θ q _ z (hx _) h).symm.trans (congr_arg (changeBill N p r φ θ) (Subtype.ext (hp x z))))
-- `Penned` is trajectory state tool. Includes θ-bills. no assumption ω.V.Pser.
variable (w:ℝ)
lemma portage (h:Pill F t φ k a w)(hv:0 < r)(hr:0 < θ)(hp:r*θ ≤ φ)(he:∀ i U,Well N p φ q (F.warp i U)) : Pill P t θ k a w :=by
     have h0:= (mul_pos hv hr).trans_le hp; have hs:= h.uses; constructor
     · exact ⟨fun i U V hu hx=>congr_arg pay₀ (hs.uses i U V hu hx), fun i=> (pay₀).toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hs.reads i), fun i U=> change_L N p r φ θ _ _ (hs.role i U),fun i U hh=>hs.buys i U (fun hp=> hh ((congr_arg pay₀ hp).trans (map_zero _)))⟩
     · exact fun i=> glimpse N p θ q φ r h0 _ (h.pigment i) (he i)
     obtain ⟨u,hu,H⟩:=h.sold.cost; exact ⟨u,hu,fun i U=> (changeCoin N p r φ θ q _ (he i U) hv hr hp).trans (H i U)⟩
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.portage
