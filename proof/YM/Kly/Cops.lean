import YM.Kly.Boast
import YM.Work.B02.Analysis
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Filter Analysis Set MeasureTheory
open Fields (pointMoment distinct)
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace ComplexOrder
variable {F:Fields}{S:F.Kernel} {a:Axis}{V:Chamber S a}{n:ℕ}
def region (a : Axis) (d : ℝ≥0) (n : ℕ) : Set (Points n) :=
  {x | 0 < d ∧ x ∈ conf n ∧ ∀ i, 0 < x i a ∧ x i a < (d : ℝ)}

theorem in_region (d : ℝ≥0) (v : Fin n → F.W) (x : Points n) :
    Slab a d (realize v x) ↔ x ∈ region a d n := by
  constructor
  · intro h
    refine ⟨h.1, (realized v x).1 h.2.1.1, fun i => ?_⟩
    have hi : (x i, v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact ⟨h.2.1.2 _ hi, h.2.2 _ hi⟩
  rintro ⟨hd,hx,ht⟩
  refine ⟨hd, ⟨(realized v x).2 hx, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    exact (ht i).1
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]
  exact (ht i).2

theorem region_open (d : ℝ≥0) (n : ℕ) : IsOpen (region a d n) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨hd,hx,ht⟩
  have hi i : ∀ᶠ y : Points n in 𝓝 x, 0 < y i a ∧ y i a < (d : ℝ) := by
    have hc : ContinuousAt (fun y : Points n => y i a) x := by fun_prop
    exact hc (Ioo_mem_nhds (ht i).1 (ht i).2)
  filter_upwards [(conf_open n).mem_nhds hx, eventually_all.mpr hi] with y hy hiy
  exact ⟨hd,hy,hiy⟩

theorem realize_spaced (r : ℝ) (v : Fin n → F.W) (x : Points n) :
    spaced r (positions (realize v x)) ↔ spaced r x := by
  let e : Fin (realize v x).length ≃ Fin n := finCongr (by simp [realize])
  have he i : positions (realize v x) i = x (e i) := by
    simp [positions,Fields.located, realize, e, finCongr]
    rfl
  constructor
  · intro h i j hne
    have ht := h (e.symm i) (e.symm j) (e.symm.injective.ne hne)
    simpa only [he, Equiv.apply_symm_apply] using ht
  intro h i j hne
  rw [he, he]
  exact h _ _ (e.injective.ne hne)

private theorem buffer_near (d : ℝ≥0) (r : ℝ) (v : Fin n → F.W)
    {x : Points n} (hr : 0 < r) (hx : buffer a r d (realize v x)) :
    ∀ᶠ y : Points n in 𝓝 x, buffer a (r/2) d (realize v y) := by
  have hf : r / 2 < r := by linarith
  have ht i : ∀ᶠ y : Points n in 𝓝 x, r/2 ≤ y i a ∧ y i a ≤ (d : ℝ) - r/2 := by
    have hi : (x i, v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hc : ContinuousAt (fun y : Points n => y i a) x := by fun_prop
    have hh : ∀ᶠ y : Points n in 𝓝 x, y i a ∈ Ioo (r/2) ((d : ℝ) - r/2) :=
      hc (Ioo_mem_nhds (hf.trans_le (hx.2 _ hi).1)
        ((show x i a ≤ (d : ℝ) - r from (hx.2 _ hi).2).trans_lt (sub_lt_sub_left hf _)))
    exact hh.mono fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hh : spaced r x := (realize_spaced r v x).1 hx.1
  have hs i j : ∀ᶠ y : Points n in 𝓝 x, i ≠ j → r / 2 ≤ cubedist (y i) (y j) := by
    by_cases he : i = j
    · exact Eventually.of_forall fun _ hn => (hn he).elim
    have hc : ContinuousAt (fun y : Points n => cubedist (y i) (y j)) x := by fun_prop
    have he' : ∀ᶠ y : Points n in 𝓝 x, r / 2 < cubedist (y i) (y j) :=
      hc (lt_mem_nhds (hf.trans_le (hh i j he)))
    exact he'.mono fun _ hz _ => hz.le
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hs i)),
    eventually_all.mpr ht] with y hy hty
  refine ⟨(realize_spaced _ v y).2 hy, fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]
  exact hty i


variable (A:Spread V)(H:Fields.Euclidean S) {C:Sequence}{P:Calibration C}(E:F.System P) (d:ℝ≥0)
variable (v:Fin n → F.W)(x:Points n)
include E H
theorem bound_p :∃ (k:ℕ)(B:ℝ), 0≤B∧∀ (d:ℝ≥0)(x:Points n)(r:ℝ),x∈region a d n→ 0<r → r ≤ 1 → buffer a r d (realize v x)→ ‖A.place d (realize v x)‖ ≤ B * r⁻¹^k:=by
      obtain ⟨D',f,hf⟩:= Rotate.cover_cap E v
      obtain ⟨B,hG,h⟩:∃ B:ℝ, 0<B∧∀ i:Fin n,‖v i‖≤B:=by
             have hp(i:Fin n):∀ᶠ k:ℝ in atTop,‖v i‖≤k:= eventually_ge_atTop _; obtain ⟨k,hk,h⟩:= ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr hp)).exists; exact ⟨_,hk,h⟩
      obtain ⟨m,C,hC,hM⟩:= A.rated H n D'
      let u:=(↑B:ℂ)⁻¹; have hu: u≠0:= inv_ne_zero (by exact_mod_cast hG.ne'); refine ⟨m,(‖u^n‖)⁻¹*C, by positivity, ?_⟩
      intro d x r hx hr ht hs; let w:=realize v x; have hd:Slab a d w:=(in_region d v x).2 hx
      have hv : widen w u= realize (u • v) x:=by unfold widen w realize; rw [List.map_ofFn]; rfl
      have he: buffer a r d (widen w u):=by
            rw [hv]; refine ⟨(realize_spaced ..).2 ((realize_spaced ..).1 hs.1),fun p hp=>?_⟩; obtain ⟨i,hi⟩:= List.mem_ofFn.mp hp; rw [← hi]; exact hs.2 (x i,v i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
      have hK: ‖A.place d (widen w u)‖ ≤ C*r⁻¹^m := by
            apply hM _ _ (widened hd u) (by rw [hv]; simp[realize]) _ r hr ht he
            rw [hv]; intro p hp; obtain ⟨i,hi⟩:= List.mem_ofFn.mp hp; rw [← hi]; change u • v i∈ _ ∧ ‖u • v i‖ ≤ 1; have hh:v i=(f i).val:= congr_fun hf i; refine ⟨Submodule.smul_mem _ _ (hh ▸ Subtype.property _),?_⟩; simp only [u,norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg hG.le]; exact (inv_mul_le_iff₀ hG).mpr (by simpa using h i)
      have he:A.place d (widen w u)= (u^n) • A.place d w:=by
            apply V.GNS.by_bud; intro i; rw [A.reads (widened hd u), scaled_plant V hd,show w.length=n from by simp[w,realize], ContinuousLinearMap.smul_apply,A.reads hd]
      rw [he,norm_smul] at hK; rw [mul_assoc]; exact (le_inv_mul_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ hu))).2 hK
lemma place_bound {x: Points n} (hx:x∈ region a d n) :∃ C:ℝ,0≤C ∧ ∀ᶠ y : Points n in 𝓝 x,‖A.place d (realize v y)‖≤ C:=by
      obtain ⟨r,hr,h1,h⟩:= affordable ((in_region d v x).2 hx); obtain ⟨k,B,hB,hK⟩:= bound_p A H E v
      refine ⟨B*((r/2)⁻¹)^k,by positivity,?_⟩; filter_upwards [(region_open ..).eventually_mem hx,buffer_near d r v hr h] with y hy ht; exact hK _ _ _ hy (half_pos hr) ((half_le_self hr.le).trans h1) ht
omit E H
def nextLabels (F:Fields) (v:Fin n → F.W)(b:Fin n ×Axis) := update v b.1 (F.partialD b.2 (v b.1))
/-- In the true real Euclidean norm on Points, the finite directions
used to test kernels exhaust a basis. -/
def columns (n : ℕ) : OrthonormalBasis (Fin n × Axis) ℝ (Points n) :=
  OrthonormalBasis.ofRepr Points.flatten

theorem columns_eq (b : Fin n × Axis) :
    columns n b = Points.direction b.1 b.2 := by
  rcases b with ⟨p,a⟩
  apply Points.flatten.injective
  rw [columns, OrthonormalBasis.coe_ofRepr, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  rintro ⟨q,j⟩
  by_cases hp : q = p
  · subst q
    simp [Points.direction, PiLp.single_apply, eq_comm]
  simp [Points.direction, hp]

/-- Operator-norm derivative candidate. -/
def columnD (v : Fin n → F.W) (x : Points n) : Points n →L[ℝ] V.GNS.H.Op :=
  ∑ b : Fin n × Axis,
    ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op (innerSL ℝ (columns n b))
      (A.place d (realize (nextLabels F v b) x))

theorem columnD_column (v : Fin n → F.W) (x : Points n) (b : Fin n × Axis) :
    columnD A d v x (Points.direction b.1 b.2) =
      A.place d (realize (nextLabels F v b) x) := by
  rw [← columns_eq b]
  simp [columnD, (columns n).inner_eq_ite, ite_smul]

include H E
theorem columnD_bound (v : Fin n → F.W)
    {x : Points n} (hx : x ∈ region a d n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y : Points n in 𝓝 x, ‖columnD A d v y‖ ≤ C := by
  have hp (b : Fin n × Axis) := place_bound A H E d (nextLabels F v b) hx
  choose k hk h using hp
  let l (b : Fin n × Axis) := ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op
    (innerSL ℝ (columns n b))
  refine ⟨∑ b : Fin n × Axis, ‖l b‖ * k b, Finset.sum_nonneg
    (fun b _ => mul_nonneg (norm_nonneg (l b)) (hk b)), ?_⟩
  filter_upwards [eventually_all.mpr h] with y hy
  let f (b : Fin n × Axis) := A.place d (realize (nextLabels F v b) y)
  calc
    ‖∑ b, l b (f b)‖ ≤ ∑ b, ‖l b (f b)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun b _ =>
      ((l b).le_opNorm (f b)).trans (mul_le_mul_of_nonneg_left (hy b) (norm_nonneg (l b)))


end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.columnD_bound
