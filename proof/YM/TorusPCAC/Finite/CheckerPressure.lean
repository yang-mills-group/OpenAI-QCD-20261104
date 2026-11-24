import YM.TorusPCAC.Finite.CheckerDet

/-!
# Unequal-mass bare lower pressure

A tighter/different lower bound than going by the determinant patch
(`YM.QCD.Lattice.Stability`, constant mass). Useable also with six
*unequal* small negative bare Wilson masses. The estimate is *real* and
on the **joint integrated weight**, lower bound in terms of the actual
pure gauge partition, hence e.g. doesn't lose `exp(-C*beta*V)` in that
comparison. No inference of global configuration sign for the determinants.

Insufficient by itself for `work/bend:eq:Bpressure`: the estimate proved
here spends volume at the finest scale. It means, for example, that an
actual analytic Blaschke selection argument, at near-zero starting masses,
is needed for a **better-than-fine-volume-scale** pressure, not to show
that the normalization works at all after doing unequal-mass shooting, or
that strict finite link-wall positivity (`V(∅)>0`) can be applied to the
result. (Here "strict" refers just to that nonvanishing, not to no null
vectors of the RP form.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Finite.Checker.Width
open QCD QCD.Lat Lattice Wilson MeasureTheory Function Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix ComplexOrder
variable {n : Side} {N : ℕ}
variable (w : Width n) (B : Torus n N)

lemma probe_integrand (U : Grid n) (s : Site n → ℝ) :
    Grass.ber _ ((B.weight * (⇑(Marker.probe s): Density n N) : Density n N) U) =
      (bare B.beta U : ℂ)*(B.fermion U+Marker.matrix n N s).det := by
  rw [Pi.mul_apply, Marker.probe_apply, Torus.weight_complex,smul_mul_assoc,map_smul,← Grass.gauss_add]
  rw [Grass.det_amplitude,smul_eq_mul]

lemma cost_nonneg : 0 ≤ cost B := prod_nonneg (fun _ _ => Even.pow_nonneg (by decide : Even 12) _)
variable (S : Finset (Site n))
def ledger (t : ℝ) := ∫ U, (bare B.beta U:ℂ)*(shift B S t U).det ∂prior su n
lemma ledger_shift (t : ℝ) (ht : t ≠ 0) :
    ledger B S t = (t:ℂ)^bill N S * Density.moment B.weight (Marker.probe (test S t)) := by
  unfold ledger Density.moment Density.volume
  simp_rw [detShift B S t _ ht,probe_integrand]; rw [← integral_const_mul]; congr 1; funext p; ring

lemma boundary (S : Finset (Site n)) : Tendsto (fun t : ℝ =>
    t^bill N S * Marker.price B (test S t)) (𝓝[>] 0) (𝓝 ‖ledger B S 0‖) := by
  let F (t : ℝ) (U : Grid n) := (bare B.beta U : ℂ)*(shift B S t U).det
  have hg : Continuous fun t : ℝ => diagonal n N (fun x=> if x∈S then (t:ℂ) else 1) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j; unfold diagonal; simp only [Matrix.diagonal_apply]; split_ifs <;> fun_prop
  have hc : Continuous F.uncurry := by
    let X(t:ℝ) := diagonal n N (fun x => if x∈S then (t:ℂ) else 1)
    have hl := ((show Continuous X from hg).comp (continuous_fst (Y := Grid n))).mul (B.continuous_fermion.comp (continuous_snd (X := ℝ)))
    let Y := diagonal n N (fun x=>if x∈S then (1:ℂ) else 0)
    change Continuous (fun p : ℝ × Grid n => (bare _ p.2 : ℂ)*(X p.1 * B.fermion p.2 + Y).det)
    exact Continuous.mul (by fun_prop) (hl.add continuous_const).matrix_det
  have hh : Continuous (ledger B S) := by simpa only [Measure.restrict_univ] using! (continuous_parametric_integral_of_continuous (μ:=prior su n) hc (isCompact_univ (X:=Grid n)))
  apply Tendsto.congr' (f₁:=fun t : ℝ => ‖ledger B S t‖) ?_ (hh.norm.continuousAt.continuousWithinAt (x:=0))
  filter_upwards [self_mem_nhdsWithin (a:=0) (s:=Set.Ioi (0:ℝ))] with b hb
  have hz : 0<b := hb
  rw [ledger_shift B S b hz.ne',norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hz.le]; rfl

lemma zero_test (S : Finset (Site n)) : test S 0 = fun _ => 0 := by ext; simp [test]
@[simp] lemma test_univ (t : ℝ) : test (n:=n) univ t=fun _=> t⁻¹ := by ext; simp [test]

lemma pq : 0 ≤ B.beta → n.val ≥ 4 → Even n.val →
    Marker.price B (fun _=>0) = B.partition := by
  intro he hh hE; unfold Marker.price; have hp : Marker.probe (n:=n) (N:=N) (fun _=>0) = 1 := by
    ext1 U; rw [Marker.probe_apply]; simp [Marker.matrix,Grass.gauss,Grass.form]
  rw [hp,Density.moment, show (⇑(1 : Insertion n N))=1 from rfl,mul_one,B.volume,
    Complex.norm_real,Real.norm_of_nonneg (Link.partition_nonneg B hh he hE)]

include w
/-- Checker bound. There is no hidden sign or abs assumption on the old
measure; use the absolute values on the probe readings, *then* use that
the vacuum itself is nonnegative by RP and that the powers in the checker
multiplicity (12 per flavor/site) are even. -/
lemma comparison (he : 0 ≤ B.beta) : Wilson.partition su n B.beta * cost B ^ sites n ≤ B.partition := by
  have hp := w.checker B he
  let a := Marker.price B fun _=>0
  have hv (t : ℝ) (ht : 0<t) : (t^bill N w.occupied * Marker.price B (test w.occupied t))^2 ≤
      (t^bill (n:=n) N univ * Marker.price B (test univ t))*a := by
    have hk : bill N w.occupied*2=bill (n:=n) N univ := by
      simp only [bill,card_univ, w.covers,mul_assoc]
    rw [mul_pow,← pow_mul,hk,test_univ,mul_assoc]
    apply mul_le_mul_of_nonneg_left (hp t⁻¹ 0) (by positivity)
  have ht : ‖ledger B w.occupied 0‖^2 ≤ ‖ledger B univ 0‖*a :=
    le_of_tendsto_of_tendsto ((boundary B _).pow 2) ((boundary B _).mul_const a)
    ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).mono hv)
  simp_rw [ledger, short w B, all B, mul_one, integral_mul_const, integral_complex_ofReal] at ht
  let Z := Wilson.partition su n B.beta
  have hh : 0< Z:= Wilson.partition_pos B.beta
  change ‖(Z:ℂ)*(cost B:ℂ)^ (w.occupiedᶜ.card)‖^2 ≤ ‖(Z:ℂ)‖*a at ht
  rw [norm_mul,norm_pow] at ht; simp_rw [Complex.norm_real, Real.norm_of_nonneg hh.le, Real.norm_of_nonneg (cost_nonneg B)] at ht
  unfold a at ht; rw [← w.equal,mul_pow,← pow_mul,← w.covers,pq B he (by rw [w.even]; have:=w.space; omega) (by rw [w.even]; simp)] at ht
  rw [pow_two, mul_assoc] at ht; exact le_of_mul_le_mul_left ht hh

end YM.TorusPCAC.Finite.Checker.Width

namespace YM.TorusPCAC.Finite
open QCD QCD.Lat Filter Wilson Lattice Finset Checker
open scoped BigOperators
variable {n : Side} {N : ℕ} (B : Torus n N)

lemma cut_width (he : Even n.val) (hh : 4 ≤ n.val) : Nonempty (Width n) := by
  obtain ⟨k,hk⟩:=he; exact ⟨⟨⟨k,by omega⟩,(show n.val=2*k by omega),(show 2≤k by omega)⟩⟩

theorem bare_comparison (h : 0 ≤ B.beta) (he : Even n.val) (hh : 4 ≤ n.val) :
    Wilson.partition su n B.beta * (∏ i : Flavor N, ((4:ℝ)+B.mass i)^12) ^ sites n ≤ B.partition := by
  obtain ⟨v⟩:=cut_width he hh; exact v.comparison B h

theorem real_normalization (h : 0 ≤ B.beta) (he : Even n.val) (hh : 4 ≤ n.val) (hs : ∀ i, B.mass i ≠ -4) :
    0 < B.partition := by
  apply lt_of_lt_of_le ?_ (bare_comparison B h he hh)
  refine mul_pos (Wilson.partition_pos B.beta) (pow_pos (prod_pos fun i _=> lt_of_le_of_ne ?_ ?_) _)
  · exact Even.pow_nonneg (by decide : Even 12) _
  exact Ne.symm (pow_ne_zero _ (by have:=hs i; intro hw; apply this; linarith))

end YM.TorusPCAC.Finite
#print axioms YM.TorusPCAC.Finite.bare_comparison
