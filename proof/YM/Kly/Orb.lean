import YM.Kly.River
import YM.Ground.Spectrum
import YM.Heat.Lift
set_option maxHeartbeats 420000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Analysis
open Fields (pointMoment distinct located prepend)
open OS (Cross)
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder ContDiff
variable {F:Fields}{S:F.Kernel}
namespace Chamber
variable {a:Axis}(C:Chamber S a)
abbrev VacuumOp:= C.D→L[ℂ] C.D
lemma seenOmega (P : Spread C) {d} {w : Cluster F} (h : Slab a d w) :
    inner ℂ C.omega (P.place d w C.omega)=pointMoment S w := by
  unfold omega; rw [P.reads h, C.GNS.measure]
  simp [kernel,air,entering,linked,raised,reflectedPoint,carry]
end Chamber

namespace Spread
variable {V : Chamber S timeAxis} (P : Spread V)

def atom (w : Cluster F) (d : ℝ≥0) : V.VacuumOp := V.D.orthogonalProjectionOnto.comp ((P.place d w).comp V.D.subtypeL)

def generators : Set V.VacuumOp := {A | ∃ (w : Cluster F) (d : ℝ≥0), Slab timeAxis d w ∧ A=P.atom w d}

private theorem boring (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : IsSemitopologicalSemiring (X →L[ℂ] X) := inferInstance
private theorem norms (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : ContinuousStar (X →L[ℂ] X) := inferInstance
instance : IsSemitopologicalSemiring V.VacuumOp := boring ↥V.D
instance : ContinuousStar V.VacuumOp := norms ↥V.D
def algebra : StarSubalgebra ℂ V.VacuumOp := (StarAlgebra.adjoin ℂ P.generators).topologicalClosure

def slot (w : Cluster F) (d : ℝ≥0) (h : Slab timeAxis d w) : ↑P.algebra :=
  ⟨P.atom w d, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ P.generators ⟨_,_,h,rfl⟩)⟩

lemma insertValue (w : Cluster F) d (h : Slab timeAxis d w) :
    inner ℂ V.omega0 ((P.slot w d h).val V.omega0) = pointMoment S w := by
  change inner ℂ V.omega0 (V.D.orthogonalProjectionOnto _) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact V.seenOmega P h

lemma place_exists {w : Cluster F} (h : distinct w) : ∃ (s : E4) (d : ℝ≥0), Slab timeAxis d (carry w s) := by
  classical
  have he : ∀ᶠ t : ℝ in atTop, ∀ i ∈ w, 0 < i.1 timeAxis + t := by
    have ht i (hi : i∈w) : ∀ᶠ t : ℝ in atTop, 0 < i.1 timeAxis+t :=
      (eventually_gt_atTop (-i.1 timeAxis)).mono fun j hj => by linarith
    simpa using (eventually_all_finset w.toFinset).mpr (fun i hi => ht i (by simpa using hi))
  obtain ⟨t,ht⟩ := he.exists
  let u := t • basis timeAxis
  let W := carry w u
  have hy : Positive W timeAxis := by
    refine ⟨still h _,fun i hi => ?_⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    change 0<(p.1 + u) timeAxis; simpa [u] using ht p hp
  have hh : ∀ᶠ t : ℝ≥0 in atTop, ∀ i ∈ W, i.1 timeAxis < (t:ℝ) := by
    have hu i (hi : i∈W) : ∀ᶠ t : ℝ≥0 in atTop, i.1 timeAxis < (t:ℝ) :=
      (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0)))).eventually (eventually_gt_atTop _)
    simpa using (eventually_all_finset W.toFinset).mpr (fun i hi => hu i (by simpa using hi))
  obtain ⟨d,hv,hh⟩ := (hh.and (eventually_gt_atTop _)).exists
  exact ⟨u,d,hh,hy,hv⟩


end Spread

namespace Kly
variable {V:Chamber S timeAxis}(P:Spread V)
open Spread
variable {d e:ℝ≥0}{w:Cluster F}
abbrev Steady (V : Chamber S timeAxis) := ∀ (x : V.D) z, V.flow.U z x=x
lemma pins (s : ℝ≥0) : V.D.orthogonalProjectionOnto.comp (V.flow.E s)=V.D.orthogonalProjectionOnto := by
  ext1 p; apply ext_inner_left ℂ; intro q
  change inner ℂ q (V.D.orthogonalProjectionOnto _)= _
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change inner ℂ q.val (V.flow.E s p)=_
  rw [← V.flow.swing,(V.flow.fixed _).1 q.property]

lemma revisits (h : Steady V) (z : Cross timeAxis) : V.D.orthogonalProjectionOnto.comp (V.flow.U z)=V.D.orthogonalProjectionOnto := by
  ext1 p; apply ext_inner_left ℂ; intro q
  change inner ℂ q (V.D.orthogonalProjectionOnto _)= _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  conv_lhs => rw [← h q z]
  exact LinearIsometry.inner_map_map (show V.H→ₗᵢ[ℂ] V.H from { (V.flow.U z).toLinearMap with norm_map' := V.flow.unitary z }) _ _

lemma atom_shift (h : Slab timeAxis d w) (u : ℝ≥0) : P.atom (raised timeAxis u w) (u+d)=P.atom w d := by
  rw [Spread.atom,crossing P h, Spread.atom]
  ext1 p
  change V.D.orthogonalProjectionOnto (V.flow.E u _) = _
  exact congr_arg (fun f : V.H→L[ℂ] V.D => f _) (pins (V := V) u)
lemma same_atom (h : Slab timeAxis d w) (hu : Slab timeAxis e w) : P.atom w e=P.atom w d := by
  have hv {d} (h : Slab timeAxis d w) (u) : P.atom w (d+u)=P.atom w d := by
    rw [Spread.atom,stretches P h]
    ext1 p; change V.D.orthogonalProjectionOnto (P.place d w (V.flow.E _ p.val)) = _
    rw [(V.flow.fixed _).1 p.property]; rfl
  rw [← hv hu d,← hv h e,add_comm]
lemma offset (h : Slab timeAxis d w) (hu : Steady V) (v : Cross timeAxis) : P.atom (carry w v.val) d=P.atom w d := by
  have he p (hp : p∈V.D) : P.place d (carry w v.val) p= V.flow.U v (P.place d w p) := by
    rw [← ContinuousLinearMap.comp_apply, P.perpendicular h v, ContinuousLinearMap.comp_apply,
      show V.flow.U v p=p from hu ⟨p,hp⟩ _]
  ext1 p; unfold Spread.atom; simp only [ContinuousLinearMap.comp_apply];
  rw [show V.D.subtypeL p=p.val from rfl,he _ (show (p.val:V.H)∈V.D from p.property),← ContinuousLinearMap.comp_apply V.D.orthogonalProjectionOnto,
    revisits hu]

lemma at_any (h : Slab timeAxis d w) (hu : Steady V) {s : E4} (t : Slab timeAxis e (carry w s)) :
    P.slot w d h=P.slot _ _ t := by
  let a := timeAxis
  let D (v : E4) := v a
  suffices he : P.atom w d=P.atom _ _ by exact Subtype.ext he
  have he {v : E4} {w : Cluster F} {d e} (hv : 0 ≤ D v) (h : Slab a d w) (t : Slab a e (carry w v)) : P.atom w d=P.atom (carry w v) e := by
    let u : ℝ≥0 := ⟨_,hv⟩
    let s := OS.Semigroup.SEP timeAxis v
    have hx := fills h u
    have ht : carry (raised timeAxis u w) s.val=carry w v := by unfold raised; rw [paths]; congr 1; change _ + (v-u.val • _) = _; exact add_sub_cancel .. 
    rw [← atom_shift P h u,← offset P hx hu s,ht]; exact same_atom P t (ht ▸ Spread.over_word s hx)
  cases le_total 0 (D s) with
  | inl hp => exact he hp h t
  | inr hp =>
    have hw : carry (carry w s) (-s)=w := by simp
    have he := (he (v := -s) (w := carry w s) (by change 0 ≤ -(D s); linarith) t (d := e) (e := d) (by rwa [hw])).symm
    rwa [hw] at he

def M (A : Cluster F) (H : distinct A) : P.algebra :=
    let p := Spread.place_exists H
    P.slot _ _ p.choose_spec.choose_spec

theorem future_reach (v : Future F timeAxis) : ∃ d : ℝ≥0, Slab timeAxis d v.val := by
  classical
  have he i (h : i∈v.val) : ∀ᶠ r : ℝ≥0 in atTop, i.1 timeAxis < (r:ℝ) :=
    (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0)))).eventually (eventually_gt_atTop _)
  obtain ⟨x,hx,hv⟩ := ((eventually_gt_atTop (0:ℝ≥0)).and ((eventually_all_finset v.val.toFinset).mpr (fun i hi => he i (by simpa using hi)))).exists
  exact ⟨x,hx,v.property,by simpa using hv⟩
def X (v : Future F timeAxis) : V.D →L[ℂ] V.H :=
    let h := future_reach v -- need beyond
    (P.place h.choose v.val).comp V.D.subtypeL
lemma standing (v : Future F timeAxis) (h : Slab timeAxis d v.val) : X P v=(P.place d v.val).comp V.D.subtypeL := by
  have he {t} (h : Slab timeAxis t v.val) (k) : (P.place (t+k) v.val).comp V.D.subtypeL=(P.place t v.val).comp V.D.subtypeL := by
    rw [stretches P h]; ext1 p
    change P.place t v.val (V.flow.E _ p.val)=_; rw [(V.flow.fixed _).1 p.property];rfl
  unfold X; dsimp only; rw [← he ((future_reach v).choose_spec) d,← he h (future_reach v).choose,add_comm]
lemma coming (v : Future F timeAxis) : X P v V.omega0=V.GNS.plant v := by
  obtain ⟨d,hd⟩ := future_reach v; rw [standing P v hd]; change P.place _ _ (V.GNS.plant (air _))=_
  rw [P.reads hd]; exact congr_arg V.GNS.plant (Subtype.ext (by simp [entering,linked,raised,air,carry]))

lemma overline (S : Steady V) (A : Cluster F) (H : distinct A) (b : E4) (h : Slab timeAxis d (carry A b)) : M P A H=P.slot _ d h := by
  let p := Spread.place_exists H
  let k := p.choose
  let n := p.choose_spec.choose
  let w := carry A k
  change P.slot w n p.choose_spec.choose_spec=_
  have he : carry w (-k+b)=carry A b := by simp [w]
  have hh := at_any P (w := w) (d := n) p.choose_spec.choose_spec S (s := -k+b) (e := d) (he ▸ h)
  exact hh.trans (show _ by congr 1)

lemma spots (S : Steady V) (h : Slab timeAxis d w) : M P w h.2.1.1=P.slot w d h := by
  have he : Slab timeAxis d (carry w 0) := by rwa [rest]
  rw [overline P S w h.2.1.1 0 he]
  congr 1; simp

lemma squeezed (h : Steady V) (v : Future F timeAxis) : (M P v.val v.property.1).val=V.D.orthogonalProjectionOnto.comp (X P v) := by
  obtain ⟨d,hv⟩ := future_reach v; rw [spots P h hv,standing P v hv]; rfl
lemma almost (h : Steady V) (v : Future F timeAxis) : (M P v.val v.property.1).val V.omega0 = V.D.orthogonalProjectionOnto (V.GNS.plant v) := by rw [squeezed P h,ContinuousLinearMap.comp_apply,coming P] -- dot?
lemma slim (hJ : Involutive (F.adj timeAxis))(H : Fields.Euclidean S) (h : Steady V) (v w : Future F timeAxis) : (M P _ (twoSides v.property w.property)).val =
    (X P v).adjoint.comp (X P w) := by
  obtain ⟨d,hd⟩ := future_reach v; obtain ⟨e,he⟩ := future_reach w
  let p := linked timeAxis d (opposite timeAxis d v.val) w.val
  have hp : p = carry (reflect v.val timeAxis ++ w.val) ((d:ℝ) • basis timeAxis) := by rw [distribute]; rfl
  have hh : Slab timeAxis (d+e) p := connects (mirrorsSlab hd) he
  have ht := overline P h _ (twoSides v.property w.property) ((d:ℝ) • basis timeAxis) (hp ▸ hh)
  have hq : M P _ (twoSides v.property w.property)=P.slot p (d+e) hh := ht.trans (by congr 1; exact hp.symm)
  rw [hq,standing P v hd,standing P w he]
  change V.D.orthogonalProjectionOnto.comp ((P.place (d+e) p).comp V.D.subtypeL)=_
  rw [ContinuousLinearMap.adjoint_comp, P.concatenate (mirrorsSlab hd) he, P.adjoints hd H hJ]
  ext1 x; change _ = V.D.subtypeL.adjoint _
  -- subtype adj projection
  rw [Submodule.adjoint_subtypeL]
  rfl

lemma full (h : Steady V) : DenseRange (fun p : P.algebra => p.val V.omega0) := by
  have hf (i : Future F timeAxis) : V.D.orthogonalProjectionOnto (V.GNS.plant i) ∈ Set.range
      (fun p : P.algebra => p.val V.omega0) := ⟨_,almost P h _⟩
  let f := fun p : P.algebra => p.val V.omega0
  apply (show DenseRange (V.D.orthogonalProjectionOnto ∘ V.GNS.stems) from
    ((show Surjective _ from fun p : V.D => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩).denseRange).comp V.GNS.whole V.D.orthogonalProjectionOnto.continuous).mono
  rintro _ ⟨x,rfl⟩
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0,by simp⟩
  | add p q hp hq =>
    obtain ⟨u,hu⟩ := hp; obtain ⟨v,hv⟩ := hq
    exact ⟨u+v,by simp [hu,hv] at *⟩
  | single i c =>
    obtain ⟨p,hp⟩ := hf i
    refine ⟨c • p,?_⟩
    simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,
      Function.comp_apply,map_smul]
    exact congr_arg (c • ·) hp
end Kly

end YM.Massive.Bridge
#print axioms YM.Massive.Bridge.Kly.full
#print axioms YM.Massive.Bridge.Kly.slim
