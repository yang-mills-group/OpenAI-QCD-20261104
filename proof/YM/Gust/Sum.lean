import YM.Gust.Skilt
-- adapt drought formulas to physical Kernels. not priced assertion.
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Filter Set MeasureTheory Measure Outer Analysis Table Work.A01 Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators Classical
variable {K:Choir}{m n:ℕ}
abbrev phot (J:Axis→Axis→ K.W)(q:Fin (m+1)→ K.W)(x:Points (m+1))(a b:Axis)(y:E4):= K.total _ (Points.cons y x) (Fin.cons (J a b) q)
noncomputable abbrev stream (x : Points (m+1)) (q : Fin (m+1)→K.W) (J : Axis→Axis→ K.W) (F : Axis→E4→ℝ) (a b : Axis) (y : E4) :=
    D (basis a) (F b) y • phot J q x a b y
noncomputable abbrev vigor (x : Points (m+1)) (q : Fin (m+1)→K.W) (J : Axis→Axis→ K.W) (F : Axis→E4→ℝ) (y : E4) :=
    ∑ a,∑ b, stream x q J F a b y
noncomputable abbrev shineP (J : Axis→Axis→ K.W) (q : Fin (m+1)→ K.W) (x : Points (m+1))(a b l d:Axis)(n:ℕ)(y:E4):= stream x q J (fun _=> petal a b l n) d b y
noncomputable abbrev gustL (x : Points (m+1)) (q : Fin (m+1)→ K.W) (J : Axis→Axis→ K.W) (a b l : Axis) (n : ℕ) (y : E4) :=
    ∑ d∈other a, shineP J q x a b l d n y
lemma paid_zero (hK:K.Domestic) (J:Axis→Axis→ K.W) (hJ:Safe K J) (x : Points (m+1))
    (hx : x∈conf _) (q : Fin (m+1)→ K.W) (F : Axis→E4→ℝ) (hf : ∀ b,ContDiff ℝ ∞ (F b)) (hv : ∀ b,HasCompactSupport (F b))
    (he : ∀ b i, x i∉tsupport (F b)) : Integrable (vigor x q J F) ∧ (∫ y,vigor x q J F y)=0 := by
  have hl (b : Axis) : ∀ y ∈ tsupport (F b), Points.cons y x∈conf _ := fun y hy => conf_cons hx fun i h => he b i (h ▸ hy)
  have hi (b a : Axis) : Integrable (stream x q J F a b) := cutoff_integrable ((hv b).fderiv_apply ℝ (basis a))
    (continuous_iff_continuousAt.mpr fun y => (dSmooth (m:=∞) ((hf b).contDiffAt (x:=y)) (basis a) (by simp)).continuousAt)
    (fun y hy => (smooth_cons_ K hK _ q (hl b y (tsupport_fderiv_apply_subset ℝ (basis a) hy))).continuousAt)
  constructor
  · exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi b a
  unfold vigor
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hi b a)]; simp_rw [integral_finsetSum _ (fun b _ => hi b _)]
  rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun b _ => ?_
  have h := Gust.cutoff_zero hK J hJ (fun _ => basis b) (fun _ => contDiff_const) (killing_const (basis b)) x q (F b) (hf b) (hv b) (hl b)
  rw [neg_eq_zero] at h
  have HH (a : Axis) (y : E4) : currentG J (fun _ => basis b) x q a y=phot J q x a b y := by
    unfold currentG phot; simp
  simp_rw [HH] at h; exact h

lemma gustL_river (x : Points (m+1)) (q : Fin (m+1)→K.W) (J : Axis→Axis→K.W) (hs : ∀ i j,J i j=J j i) (a b l : Axis) (h : a≠b) (n : ℕ) (y : E4) :
    vigor x q J (vane a b l n) y=gustL x q J a b l n y-gustL x q J b a l n y := by
  let F := vane a b l n; let X (d c : Axis) := stream x q J F d c y
  change ∑ d : Axis,∑ c : Axis, X d c=_
  have hv : F b=petal a b l n := if_pos rfl
  have ht : F a= -petal b a l n := by simp [F,vane,h]
  have he d : X d b= shineP J q x a b l d n y := by unfold X stream; rw [hv]
  have ha d : X d a= -shineP J q x b a l d n y := by
    unfold X stream; rw [ht,D,fderiv_neg,(show ∀ U : E4→L[ℝ]ℝ, (-U) (basis d) = -U (basis d) from fun _ => rfl),neg_smul]; rfl
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ (f:=fun c => ∑ d, X d c) (Finset.mem_univ b),← Finset.add_sum_erase _ _ (apart h)]
  have hl : ∑ c∈(other b).erase a, ∑ d, X d c=0 := Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun d _ => by
    have h1 : i≠a := (Finset.mem_erase.mp hi).1; have h2 := (Finset.mem_erase.mp (show i∈other b from (Finset.mem_erase.mp hi).2)).1
    simp [X,stream,F,vane,h1,h2,D]
  rw [hl,add_zero]; simp_rw [he,ha, Finset.sum_neg_distrib]
  unfold gustL other; rw [← Finset.add_sum_erase (f:=fun d => shineP J q x a b l d n y) _ (Finset.mem_univ a),← Finset.add_sum_erase (f:=fun d => shineP J q x b a l d n y) _ (Finset.mem_univ b)]
  have hz : shineP J q x a b l a n y=shineP J q x b a l b n y := by
    unfold shineP stream; rw [petal_self,petal_self,chart_symm a b]; unfold phot; rw [hs a b]
  rw [hz]; abel
end YM.Massive.Gust
#print axioms YM.Massive.Gust.paid_zero
#print axioms YM.Massive.Gust.gustL_river
