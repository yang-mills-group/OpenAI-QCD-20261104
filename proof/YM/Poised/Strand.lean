import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
/-! # Heir acts in true Teller at much higher rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Filter Function Lattice Wilson Pressure RG Tree Precision Next Next.Free Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory Extra.Iteration Extra.Iteration.Scales SelectedOrderedKernels.Sector
    AnalyticBridge.LocalGaussianLaws
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {L : Side} {P B : BudgetPoint} {x u a t K : ℝ} {n r : ℕ} {C : Libretto G n} {D : Record}
-- adapt songs proof
lemma streamsG (Pt : Teller G) (δ K : ℝ) (n w:ℕ) (hk:2≤w)(hd : 0<δ) (hK : 0≤K) : ∃ C : Libretto G n, C.δ=δ ∧ C.N=K ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ F, Matins T F w (2*C.C) C.M := by
  obtain ⟨Z⟩ := Foliage.collarSupply G n; obtain ⟨Q⟩ := authority G n; obtain ⟨W⟩ := webExists G
  have h := Foliage.Cube.fee_one Z
  obtain ⟨M,hM,H⟩ := coaches Pt w (2*Foliage.Cube.fee Z) hk (by positivity)
  exact ⟨⟨Z,Q,W,δ,hd,K,hK,M,hM⟩,rfl,rfl,H⟩

lemma songsP (H : Patch) (Pt : Teller G) (C : Libretto G n) (hp : H.Branches Pt.bind G) (hL : licensed C.δ C.N H.L)
    (hn : 6 ≤ n) (m p w:ℕ) (hk : n ≤ m) (he : p ≤ w)
    (hm : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ F, Matins T F w (2*C.C) C.M) (r : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ D : Record, D.ε ≤ R ∧ Tight C D ∧ ∀ᶠ x : ℝ in atTop, ∀ P B : BudgetPoint,
      P.threshold=temp x → B.threshold=fiery G x H.L → B.B=radiusB (betaF G x H.L) → P.order=n → B.order=m →
      P.power=p → B.power=w → (∀ β, betaF G x H.L / 2 ≤ β → 0 < coupling β ∧ Lute.Plented C D P B H.L r x (coupling β)) ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=H → Seam T C.δ C.N → Lift.Booth Pt S T → 100*(1+radiusB x)≤c.val → Plays C D P B Pt T x := by
  have h₀ := C.web.cost
  obtain ⟨b,Q,hb,hQ,hh⟩ := Psalm.harmony G H Pt hp n (by omega)
  obtain ⟨w,g,d,M,Y,s,Y',hw,hg,hd,hs,hM,hY,hY',h⟩ := haar_operators G H Pt hp n
  let ε := min R ((128*C.web.scale)⁻¹); have hε : 0 < ε := lt_min hR (by positivity)
  let Z := 1+peal G n p d s M w Y g Y'
  let D : Record := ⟨b,hb,Q,hQ,ε,hε,peakCost G n M w Y,le_add_of_nonneg_right (abs_nonneg _),Z,le_add_of_nonneg_right (by unfold peal; positivity)⟩
  have hε' := min_le_right R ((128*C.web.scale)⁻¹)
  have ht : Tight C D := ⟨le_trans hε' (inv_le_comm₀ (by positivity) (by norm_num) |>.mpr (by linarith)),by
    have h := mul_le_mul_of_nonneg_left hε' (zero_le_one.trans h₀); field_simp at h; change C.web.scale * min R _ ≤ 1/128; rw [mul_comm (128:ℝ),← one_div]; linarith⟩
  refine ⟨D,min_le_left ..,ht,?_⟩
  filter_upwards [hh,h,rehearses hL ht _ _ he,Folio.subscribe Pt H,plents C D H.L r p (by omega), Rebuild.geometry (G.slopeConstant * Real.log H.L.val)] with x hx h hR hB hP hE P B hv hb' hBB h₁ h₂ h₃ h₄
  refine ⟨fun β hl => let hb := hP β hl; ⟨hb.1,hb.2 P B hb' h₃⟩,fun S T hH hT hh hc => ⟨hB S T hh.1 hH, h₄.symm ▸ hm S T hh.1,hT, fun F k => (hx S T hH hh hc F k).1,fun F k => (hx S T hH hh hc F k).2,fun A F k {ι} _ _ e o R V hR hv' => ?_,hc,hH.symm ▸ hR P B hv hb' (hBB.symm ▸ hE.1.1) h₃ h₁ (h₂.symm ▸ hk) h₄⟩⟩
  rw [hv] at hv'; have hr := ringing (h S T hH hc hh.1 A F k V hv') hg hv e hR
  rw [hb',← hH]; convert hr using 1; unfold D Z; simp only [h₃]
end YM.PhysicalNext.JointLoad.Heir
#print axioms YM.PhysicalNext.JointLoad.Heir.songsP
