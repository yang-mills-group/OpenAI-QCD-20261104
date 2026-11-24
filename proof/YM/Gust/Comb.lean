import YM.Gust.Deck
import YM.Work.A02
-- Work.A02 adapted to same filtration. translation flux not yet translation operator.
set_option maxHeartbeats 470000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Filter Set MeasureTheory Metric Table Work.A02 Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators
variable {K: Choir}{n:ℕ}{χ:E4→ℝ}(h:K.Domestic)
abbrev disc (w:Fin n→ K.W)(p:Points n):= K.total _ p w
abbrev spin (J:Axis→Axis→ K.W)(χ:E4→ℝ)(v:Ortho.Skew)(x:Points (n+1))(p:Fin n→ K.W)(B:K.W):= about J χ (M4.move v.val) x (Fin.cons B p)
abbrev gradG (J:Axis→Axis→K.W)(χ:E4→ℝ)(b:Axis)(x:Points (n+1))(p:Fin n→ K.W)(B:K.W):= -∑ a:Axis,∫ y:E4, (↑(D (basis a) χ y):ℂ)*K.total _ (Points.cons y x) (Fin.cons (J a b) (Fin.cons B p))
include h
lemma cont_disc (v:Fin n→ K.W){x:Points n}(hx:x∈conf n): ContDiffAt ℝ ∞ (disc v) x:= ((h.smooth n v).contDiffAt ((conf_open _).mem_nhds hx))
omit h
lemma heartShell {x:Points (n+1)}(hx:x∈conf _)(hw:Window x χ)(h:K.Domestic)(w:Fin (n+2)→K.W)(a:Axis)(l:E4→ℂ)(hl:Continuous l):Integrable fun y=> (↑(D (basis a) χ y):ℂ)* l y * disc w (Points.cons y x) :=by
   have he:{y:E4|y ∈ tsupport (D (basis a) χ)} ⊆ {y:E4|y∈ tsupport (fderiv ℝ χ)}:=by
    apply closure_minimal ?_ (isClosed_tsupport _)
    exact fun y hy=> subset_tsupport _ (show fderiv ℝ χ y ≠0 from fun H=> hy (by simp [D,H]))
   have ht:Continuous (D (basis a) χ):=(hw.1.continuous_fderiv (by simp)).clm_apply continuous_const
   have hχ: HasCompactSupport (D (basis a) χ) := hw.2.1.fderiv_apply ℝ _
   have hh(y)(hy:y∈tsupport (D (basis a) χ)): ContinuousAt (fun y=> l y * disc w (Points.cons y x)) y :=hl.continuousAt.mul ((cont_disc h w (on_shell hx hw y (he hy))).continuousAt.comp (f:=fun z=>Points.cons z x) (show Continuous (fun z=>Points.cons z x) from continuous_cons.comp (continuous_id.prodMk continuous_const)).continuousAt)
   simpa only[Complex.real_smul,mul_assoc] using Work.A01.cutoff_integrable hχ ht hh
include h
lemma deriv_cas (x : Points n) (j : Fin n) (b : Axis) (q : Fin n → K.W)
    (t : ℝ) (ht : Ward.cast x j b t ∈ conf _) :
    HasDerivAt (fun s => disc q (Ward.cast x j b s))
      (disc (update q j (K.arc b (q j))) (Ward.cast x j b t)) t := by
  dsimp only [disc]
  rw [← h.derivatives _ _ ht]
  exact ((cont_disc h q ht).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (Ward.moves x j b t)

/-- One summand. Justify both operations (derivative of the weight and replacement by the
positional derivative label) on the same fixed shell, moving slot 0 of x and not moving y.
`tsupport (fderiv ℝ χ)` works uniformly in a neighborhood of the parameter. -/
theorem deriv_coax {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (a b : Axis)
    (J : K.W) (B : K.W) (q : Fin n → K.W)
    (m m' : ℝ × E4 → ℂ) (cm : Continuous m) (cm' : Continuous m')
    (hm : ∀ (t : ℝ) (y : E4), HasDerivAt (fun s => m (s, y)) (m' (t, y)) t) :
    HasDerivAt (fun t => ∫ y : E4,
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m (t, y) *
        K.total _ (Points.cons y (Ward.cast x 0 b t)) (Fin.cons J (Fin.cons B q)))
      ((∫ y : E4, ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m' (0, y) *
        K.total _ (Points.cons y x) (Fin.cons J (Fin.cons B q))) +
       (∫ y : E4, ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m (0, y) *
        K.total _ (Points.cons y x) (Fin.cons J (Fin.cons (K.arc b B) q)))) 0 := by
  classical
  obtain ⟨r, hr, hh⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (show {t | Ward.cast x 0 b t ∈ conf _ ∧ Window (Ward.cast x 0 b t) χ} ∈ 𝓝 (0 : ℝ)
      from stable hx hw b)
  let s := closedBall (0 : ℝ) r
  have hs : s ∈ 𝓝 (0 : ℝ) := closedBall_mem_nhds 0 hr
  have zs : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  let Cκ := tsupport (fderiv ℝ χ)
  have hK : IsCompact Cκ := hw.2.1.fderiv ℝ
  let g (y : E4) : ℂ := ↑(Analysis.D (basis a) χ y)
  have cg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact Complex.continuous_ofReal.continuousAt.comp
      ((Analysis.dSmooth (hw.1.contDiffAt (x := y)) (basis a) (m := ∞) (by simp)).continuousAt)
  have g_zero (y : E4) (hy : y ∉ Cκ) : g y = 0 := by
    have hf : fderiv ℝ χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [g, Analysis.D, hf]
  let X (t : ℝ) (y : E4) := Points.cons y (Ward.cast x 0 b t)
  let Q : Fin (n+2) → K.W := Fin.cons J (Fin.cons B q)
  let Q' : Fin (n+2) → K.W := Fin.cons J (Fin.cons (K.arc b B) q)
  let F (l : ℝ × E4 → ℂ) (w : Fin (n+2) → K.W) (t : ℝ) (y : E4) : ℂ :=
    g y * l (t, y) * disc w (X t y)
  let F' (t : ℝ) (y : E4) := F m' Q t y + F m Q' t y
  have int (l : ℝ × E4 → ℂ) (cl : Continuous l) (w : Fin (n+2) → K.W) {t : ℝ} (ht : t ∈ s) :
      Integrable (F l w t) :=
    heartShell (hh ht).1 (hh ht).2 h w a (fun y => l (t, y))
      (cl.comp (f := fun y : E4 => (t, y)) (by fun_prop))
  have sep (t : ℝ) (ht : t ∈ s) (y : E4) (hy : y ∈ Cκ) : X t y ∈ conf _ :=
    on_shell (hh ht).1 (hh ht).2 y hy
  have fc (l : ℝ × E4 → ℂ) (cl : Continuous l) (w : Fin (n+2) → K.W) :
      ContinuousOn (fun z : ℝ × E4 => F l w z.1 z.2) (s ×ˢ Cκ) := by
    have ht : Continuous (Ward.cast x 0 b) := continuous_iff_continuousAt.mpr
      (fun t => (Ward.moves x 0 b t).continuousAt)
    have cX : Continuous (fun z : ℝ × E4 => X z.1 z.2) :=
      continuous_cons.comp (continuous_snd.prodMk (ht.comp continuous_fst))
    rintro ⟨t, y⟩ ⟨hp, hy⟩
    refine ContinuousAt.continuousWithinAt (s := s ×ˢ Cκ) ?_
    exact (((cg.comp continuous_snd).mul cl).continuousAt).mul
      ((cont_disc h w (sep t hp y hy)).continuousAt.comp
        (f := fun z : ℝ × E4 => X z.1 z.2) (x := (t, y)) cX.continuousAt)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).prod hK).exists_bound_of_continuousOn
    ((fc m' cm' Q).add (fc m cm Q'))
  let bound := Cκ.indicator fun _ : E4 => C
  have integrable_bound : Integrable bound :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hB (y : E4) (t : ℝ) (hp : t ∈ s) : ‖F' t y‖ ≤ bound y := by
    by_cases hy : y ∈ Cκ
    · rw [show bound y = C from indicator_of_mem hy _]
      exact hC (t, y) ⟨hp, hy⟩
    · simp [F', F, g_zero y hy, bound, hy]
  have hF (y : E4) (t : ℝ) (ht : t ∈ s) : HasDerivAt (fun u => F m Q u y) (F' t y) t := by
    by_cases hy : y ∈ Cκ
    · have hsep := sep t ht y hy
      have hk : HasDerivAt (fun u => disc Q (X u y)) (disc Q' (X t y)) t := by
        let j := (0 : Fin (n+1)).succ
        have he : Q' = update Q j (K.arc b (Q j)) := by
          simp only [Q, Q', j, Fin.cons_succ, Fin.cons_zero, ← Fin.cons_update,
            Fin.update_cons_zero]
        simp_rw [X, cons_cast] at hsep ⊢
        rw [he]
        exact deriv_cas h _ j b Q t hsep
      exact ((hm t y).const_mul (g y)).mul hk
    · simpa only [F', F, g_zero y hy, zero_mul, add_zero] using! hasDerivAt_const t (0 : ℂ)
  have key : HasDerivAt (fun t => ∫ y : E4, F m Q t y) (∫ y : E4, F' 0 y) 0 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (show ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F m Q t) volume from
        Eventually.mono hs fun t ht => (int m cm Q ht).aestronglyMeasurable)
      (int m cm Q zs)
      (show AEStronglyMeasurable (F' 0) volume from
        ((int m' cm' Q zs).add (int m cm Q' zs)).aestronglyMeasurable)
      (ae_of_all _ hB) integrable_bound (ae_of_all _ hF)).2
  dsimp only [F'] at key
  rw [integral_add (int m' cm' Q zs) (int m cm Q' zs)] at key
  simpa only [F, g, disc, X, Ward.start, Q, Q'] using key

lemma deriv_shellSpin {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (b : Axis)
    (J:Axis→Axis→ K.W) (v : Ortho.Skew) (B : K.W) (q : Fin n → K.W) :
    HasDerivAt (fun t => spin J χ v (Ward.cast x 0 b t) q B)
      (spin J χ v x q (K.arc b B) -
        ∑ c : Axis, (v.val c b : ℂ) * gradG J χ c x q B) 0 := by
  let F (a c : Axis) (t : ℝ) := ∫ y : E4,
    ((Analysis.D (basis a) χ y * M4.move v.val (y - Ward.cast x 0 b t 0) c : ℝ) : ℂ) *
      K.total _ (Points.cons y (Ward.cast x 0 b t)) (Fin.cons (J a c) (Fin.cons B q))
  let A (a c : Axis) := ∫ y : E4,
    ((Analysis.D (basis a) χ y * M4.move v.val (y - x 0) c : ℝ) : ℂ) *
      K.total _ (Points.cons y x) (Fin.cons (J a c) (Fin.cons (K.arc b B) q))
  let L' (a c : Axis) := ∫ y : E4,
    ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
      K.total _ (Points.cons y x) (Fin.cons (J a c) (Fin.cons B q))
  have row (a c : Axis) : HasDerivAt (F a c) ((-(v.val c b : ℂ)) * L' a c + A a c) 0 := by
    let m (z : ℝ × E4) : ℂ := ↑(M4.move v.val (z.2 - Ward.cast x 0 b z.1 0) c)
    have cm : Continuous m := by
      unfold m
      simp_rw [center_eq]
      have ht : Continuous (Ward.cast x 0 b) := continuous_iff_continuousAt.mpr
        (fun t => (Ward.moves x 0 b t).continuousAt)
      have hc : Continuous (fun y : E4 => M4.move v.val y c) := by
        simp_rw [M4.at_coord]; fun_prop
      exact Complex.continuous_ofReal.comp
        ((hc.comp continuous_snd).sub ((Ward.factor 0 c v).continuous.comp (ht.comp continuous_fst)))
    have hd' : ∀ (t : ℝ) (y : E4), HasDerivAt (fun s => m (s, y)) (-(v.val c b : ℂ)) t := by
      intro t y
      simpa only [m, Complex.ofReal_neg] using (deriv_center x v c b y t).ofReal_comp
    have he := deriv_coax h hx hw a b (J a c) B q m (fun _ => -(v.val c b : ℂ))
      cm continuous_const hd'
    simp only [F, L', A, Complex.ofReal_mul]
    simp only [m, Ward.start] at he
    apply he.congr_deriv
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae; filter_upwards with y; ring
  have he := HasDerivAt.fun_sum (u := (Finset.univ : Finset Axis))
    (fun a _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset Axis)) (fun c _ => row a c))
  -- Both shells carry the leading minus sign. Regroup the terms from
  -- differentiating the centering as minus the matrix entries times the translation shells.
  apply (he.neg).congr_deriv
  change -(∑ a : Axis, ∑ c : Axis, (-(v.val c b : ℂ) * L' a c + A a c)) =
    -(∑ a : Axis, ∑ c : Axis, A a c) - ∑ c : Axis, (v.val c b : ℂ) * -(∑ a : Axis, L' a c)
  simp_rw [neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_neg, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a c : Axis => (v.val c b : ℂ) * L' a c)]
  rw [Finset.sum_neg_distrib]
  abel

lemma deriv_head {x : Points (n+1)} (hx : x ∈ conf _) (b : Axis) (B : K.W)
    (q : Fin n → K.W) :
    HasDerivAt (fun t => K.total _ (Ward.cast x 0 b t) (Fin.cons B q))
      (K.total _ x (Fin.cons (K.arc b B) q)) 0 := by
  have hh : Ward.cast x 0 b 0 ∈ conf _ := Ward.start x 0 b |>.symm ▸ hx
  have hp := deriv_cas h x 0 b (Fin.cons B q) 0 hh
  simp only [Ward.start, Fin.cons_zero, Fin.update_cons_zero] at hp
  exact hp

end YM.Massive.Gust
#print axioms YM.Massive.Gust.deriv_shellSpin
#print axioms YM.Massive.Gust.deriv_head
