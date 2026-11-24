import YM.Avian.Stroll
import YM.Avian.Aspen
/-! From funded weave to exact derivative moment estimates.Probe references unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset Topology
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper Tawny Cast Patria.Rolls Patria.Rolls.Attain Seals Pane BendR UV.Free KeysP Clifford
variable {C:Sequence}(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 8)(H:Bore 10)(hT:Rubric sym B)(hH:Rubric sym H)(F:ℕ→PatchMix 8)(hψ:∀ᶠ i in atTop, OrderMix (C.A i) T sym B (i:=0) (F i)∧∃ W,Wager (C.A i) T H W 0)
variable (x:ℂ)(Q:RawTensor x 8) (P:BudgetPoint)(L':ℕ→ℕ)(n m:ℕ)(t a:ℝ)(hN:10 ≤ P.order)(hm:6≤ n)(hC:2 < m)(ht:0<t)(hh:3 ≤ P.power)
open Tarn Tarn.Choir Needle
variable {Cal:Calibration C}{K:∀ d,Cottage Cal d}{β e:ℝ}(hp:C.Path β e)(hr:Sway C.S)(hR:Tendsto (fun i=> ↑((C.S.side (C.R i) 0).val):ℕ→ℝ) atTop atTop)(hI:∀ t b i, Lat.Invariant (B t b i))
variable (Y:Choir){φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)(hg:Y.Harmony Cal φ)
variable (hq:∀ i a b,stemV Cal 8 i (shelS a b) (Q.val (a,b))=skyU (C.A i) B (F i) x Q a b)
variable (hx:∀ᶠ i in atTop,∀ j k:Axis, Tutor 0 P (Canvas.foil ((C.A i).density 0) (path (C.A i) B (F i) x Q j k 0)) t n m a)
variable (hL:∀ i,i ≤ L' i)(hw:∀ a b:Axis, ∃ p:ℕ→Label 10, Needle.Weave Cal L' T 0 (shelV b) (fun i=> vine (C.A i) B (F i) x Q a b) p)
include hp hT hH hψ hg hφ hN hm hC ht hh hx hr hI hR hq hw hL K
lemma emerges :∃ d:RawVec 10, (viewsL d)=viewsX x Q ∧ lookQ d=0∧ lookB d=0 ∧ ∀ j:Axis,(∑ i:Axis,Y.arc i (Y.focus (shelS i j) 8 (Q.val (i,j)))) = Y.focus (shelV j) 10 (d.val j):=by
     choose Z hZ using hw; let D(i:ℕ)(a b:Axis):= Z a b i; obtain ⟨v,hV,hc,hQ,hz⟩:= certifiedL T sym B H hT hH F hψ x Q hp.normalized hR hI P n m t a hN hm hC ht hh hx D (eventually_all.mpr fun a:Axis=>eventually_all.mpr fun b:Axis=> (hZ a b).sees)
     refine ⟨v,hV,hc,hQ,fun j=>?_⟩; let V(a:Axis):= shelS a j
     have he(a:Axis): Weave Cal L' T 0 (shelV j) (fun i=> Rolls.nick (C.S.spacing (C.N i))⁻¹ a (stemV Cal 8 i (V a) (Q.val (a,j)))) (Z a j):=by unfold V; simp_rw [hq]; exact hZ a j
     let f:= (∑ a:Axis,Z a j); have hf: Tendsto f atTop (𝓝 (v.val j)):=by unfold f; convert! (hz j) using 1
     apply Measures.coupled hp hr hφ hg (v.val j) f hf _ 8 (shelV j) V (fun a:Axis=> Q.val (a,j)) 0 T (fun a=>can_go a [j] (by simp)) hL _ (G:=K); exact Weave.graduated (he 0) _ _ _ (fun i _=> he i)
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.emerges
