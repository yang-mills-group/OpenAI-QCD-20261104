import YM.Slice.Gate
import YM.QCD.RP.Sky

/-!
# Fix the two arrays of links cut by a link seam

Only for gauge invariant rates. `set` their values to identity after the
explicit Haar/Fubini and gauge calculations. Need at least four levels (two
adjacent positive levels may not coincide).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Function MeasureTheory Wilson Lattice Slice Link
open scoped ComplexOrder Topology BigOperators Matrix.Norms.Frobenius

variable {n : Side} {R : Cells.Cut n}
local notation "a" => R.pos -- lexical avoid binders
local notation "b" => Link.bottom R
local notation "c" => Link.top R
abbrev Free (R : Cells.Cut n) := Slice.Open R su × Slice.Open R su

lemma distinct_outside (hL : 2 ≤ R.half.val) : b+1≠c := by
  intro he; have hx := congrArg (res R) he
  rw [Link.bottom,sub_add_cancel] at hx
  have hi : res R R.baseLine=0 := by simp [res]
  have ht : res R c+1=R.half.val := exitRank
  omega

lemma new_frame (h : R.kind=.link) (hL : 2 ≤ R.half.val) (d : Slice.Rest R su) :
    ∃ k : Lat.Frame n, ∀ (P : Free R) (i : ↥(gate R)) (x : Slice.Row a n),
      Lattice.gauge k (chain a (wire R (d,P))) (plane a i x,a) = 1 := by
  -- positive side gauge change only on first and last level
  let k (y : Site n) := if y a=b+1 then d.2 (ebb h) (drop a y) else
    if y a=c then (d.2 (high h) (drop a y))⁻¹ else 1
  have he : b+1≠c := distinct_outside hL
  have hb : b≠b+1 := fun hh => (below_base h).1 (hh.symm ▸ (below_base h).2)
  have hc : c+1≠b+1 := fun hh => piers_split (add_right_cancel hh.symm)
  have hv : c+1≠c := fun hh => (leaving_top h).2 (hh.symm ▸ (leaving_top h).1)
  have hs : b≠c := piers_split
  refine ⟨k,fun P i x => ?_⟩
  unfold Lattice.gauge; dsimp only
  rw [chain_time,lift_time,checkpoint]
  rcases points_into h i with rfl|rfl
  · simp [k,ebb,hb,he,hs]
  simp [k,high,hc,hv,Ne.symm he]

-- `iso`, `slice` both multiplicative before replacing orientation.
def full (R : Cells.Cut n) : Dwelling R su ≃* Lat.Grid n := (Slice.iso R).trans (slice R.pos).symm
@[simp] lemma full_at (P : Dwelling R su) : full R P=chain a (wire R P) := rfl

def freeM (R : Cells.Cut n) := (fieldM su R).prod (fieldM su R)
instance : IsProbabilityMeasure (freeM R) := by unfold freeM; infer_instance
instance : Measure.IsHaarMeasure (freeM R) := Measure.prod.instIsHaarMeasure (G := Open R su) (H := Open R su) (fieldM su R) (fieldM su R)
-- right invariant

lemma clears (h : R.kind=.link) (hL : 2 ≤ R.half.val) (d : Rest R su) (f : Lat.Grid n → ℂ)
    (hf : Continuous f) (hi : GaugeInvariant f) :
    (∫ x : Free R, f (full R (d,x)) ∂freeM R) = ∫ x : Free R, f (full R (1,x)) ∂freeM R := by
  obtain ⟨k,hk⟩ := new_frame h hL d
  let U : Lat.Grid n := fun e => k e.1
  let V : Lat.Grid n := fun e => (k (e.1 + step e.2))⁻¹
  let L := (full R).symm U
  let S := (full R).symm V
  have ha (x : Free R) : Lattice.gauge k (full R (d,x)) = full R (L*(d,x)*S) := by rw [map_mul,map_mul]; simp only [L,S,MulEquiv.apply_symm_apply]; rfl
  have H : L.1*d*S.1=1 := by
    haveI := walls_link h
    apply Prod.ext
    · exact Subsingleton.elim ..
    funext i y
    let v : Free R := 1
    have ht := hk v i y
    rw [← full_at,ha,full_at,chain_time,checkpoint] at ht
    exact ht
  have hy (x : Free R) : f (full R (d,x)) = f (full R (1,L.2*x*S.2)) := by
    rw [← hi k (full R (d,x)),ha, show L*(d,x)*S=(L.1*d*S.1, L.2*x*S.2) from rfl,H] -- check hi order
  let g : Free R→ℂ := fun x => f (full R (1,x))
  simp_rw [hy]
  haveI : Measure.IsMulRightInvariant (freeM R) := by
    constructor
    intro u
    haveI : IsProbabilityMeasure ((freeM R).map (· * u)) := Measure.isProbabilityMeasure_map (measurable_mul_const u).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  exact (integral_mul_left_eq_self (μ:=freeM R) (fun x => g (x*S.2)) L.2).trans (integral_mul_right_eq_self g S.2)

/-- The two open configurations, oriented as in the base library. -/
def clear (R : Cells.Cut n) (x y : Open R su) := chain R.pos (follow R (1,x,y))
@[fun_prop] lemma clear_cont : Continuous fun p : Free R => clear R p.1 p.2 := by unfold clear; fun_prop

lemma cleared (h : R.kind=.link) (hL : 2≤ R.half.val) (f : Lat.Grid n → ℂ)
    (hf : Continuous f) (hi : GaugeInvariant f) :
    (∫ x, f x ∂prior su n) = ∫ x : Free R, f (clear R x.1 x.2) ∂freeM R := by
  let u := fun x : Free R => (x.1,replace R x.2)
  let j := fun x : Free R => f (full R (1,x))
  have hm : MeasurePreserving u (freeM R) (freeM R) := (MeasurePreserving.id _).prod (twisted R)
  have hx : MeasurePreserving (full R) ((restM su R).prod (freeM R)) (prior su n) := (chain_volume _).comp (wiredVolume R)
  have hw := integral_map hx.aemeasurable (f:=f) (by rw [hx.map_eq]; exact hf.aestronglyMeasurable)
  rw [hx.map_eq] at hw; rw [hw, integral_prod _ (show Integrable (fun x => f (full R x)) _ from hx.integrable_comp_of_integrable
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))]
  change (∫ x, (∫ y : Free R, f (full R (x,y)) ∂freeM R) ∂restM su R) = ∫ x, j (u x) ∂freeM R
  simp_rw [clears h hL _ f hf hi]; rw [integral_const]; simp only [Measure.real, measure_univ,ENNReal.toReal_one,one_smul]
  have hj : Continuous j := by unfold j; simp_rw [full_at]; fun_prop
  have He := integral_map hm.aemeasurable (f:=j) (by rw [hm.map_eq]; exact hj.aestronglyMeasurable)
  rw [hm.map_eq] at He; exact He
end YM.QCD.RP
