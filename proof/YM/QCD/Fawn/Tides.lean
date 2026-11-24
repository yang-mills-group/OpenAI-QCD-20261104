import YM.QCD.Fawn.Fleur
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Hera
open Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
open Heir.Lute
private lemma raisePrice (n : ℕ) {a b s : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : (a+b*s^2)^(n+n) ≤ (a+a)^(n+n)*(1+b^(n+n)*s^(2*(n+n))) := by
  let d := n+n
  have hp : 0≤b*s^2 := mul_nonneg hb (sq_nonneg _)
  rw [pow_mul, ← mul_pow]; rcases le_or_gt (b*s^2) 1 with h|h
  · exact (pow_le_pow_left₀ (by positivity) (add_le_add_right (h.trans ha) a) d).trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hp _)))
  rw [mul_add,mul_one,← mul_pow]; apply le_add_of_nonneg_left' (pow_le_pow_left₀ (by positivity) _ _) (by positivity : 0 ≤ (a+a)^d)
  rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) h.le) (le_mul_of_one_le_left hp ha)
where le_add_of_nonneg_left' {u v w : ℝ} (h : u≤v) (he : 0≤w) : u≤w+v := h.trans (le_add_of_nonneg_left he)

variable {Γ : Prices G ι → ℝ}  (a : Museum F x A X Y ι) (he : Plays C D P B Pt T x) (ho : o ∈ X)(hτ:0≤τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ)
include he ho hτ hY hu hΓ
lemma vested (U : Config G f) (hV : Healthy P.threshold Y V) (h:Fugue a U f' T C D P B r Γ u τ k q d o V) (l : List (Directions G c)) (hl : l.length ≤ n) (ha : ∀ A∈l, P.dirBound (S.ratio.parent o) A) (z : Prices G ι) :
    let ρ := rust C D P B S.patch.L X r x u
    ‖leftDerivs (a.concert T u q d k f' Γ U V z) l V‖ ≤ ((Heir.Lute.leading C+Heir.Lute.leading C)^(n+n)*τ) * (1+ρ^(n+n)*powers z^(2*(n+n))) := by
  intro ρ; have ht := hτ
  obtain hx := Hera.choir_band a U he ho hτ hY hu hΓ hV h z
  have hw :0≤ρ:= rust_nn hu; have hc:= leading_one C
  let t:= leading C+ρ*powers z^2; have h1:1≤ t:= hc.trans (le_add_of_nonneg_right (mul_nonneg hw (sq_nonneg _)))
  calc
     _ ≤ τ*t^n*t^n := (hx.caps l hl ha).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hx.sane (speed_le a hY ho hu z) _).trans (pow_le_pow_right₀ h1 hl)) (by change 0≤ τ*t^n; positivity))
     _= τ*t^(n+n):= by rw [pow_add,mul_assoc]
     _ ≤ τ*((leading C+leading C)^(n+n)*(1+ρ^(n+n)*powers z^(2*(n+n)))):= mul_le_mul_of_nonneg_left (raisePrice n hc hw) hτ
     _ = _:=by ring

omit he ho hτ hY hu hΓ
private lemma meter_nn {Q : ℝ} (hq : 0≤Q) (d k : ℕ) : 0 ≤ AnalyticBridge.LocalGaussian.Moments.meter d 0 Q k := by
  unfold AnalyticBridge.LocalGaussian.Moments.meter; positivity [inflate_ge k (show 0 ≤ Q⁻¹ / 8 by positivity)]
private lemma meter_mono {Q : ℝ} (hq : 0≤Q) {D H : ℕ} (k : ℕ) (h : D ≤ H) :
    AnalyticBridge.LocalGaussian.Moments.meter D 0 Q k ≤ AnalyticBridge.LocalGaussian.Moments.meter H 0 Q k := by
  have hi := inflate_ge k (show 0≤Q⁻¹/8 by positivity)
  unfold AnalyticBridge.LocalGaussian.Moments.meter; gcongr

def ripple (C : Libretto G n)(τ:ℝ):= (Heir.Lute.leading C+Heir.Lute.leading C)^(n+n)*τ
def lyreFee (C : Libretto G n)(τ:ℝ)(D : Record)(P B : BudgetPoint)(L : Side)(X : Support f)(r : ℕ)(x u :ℝ) := ripple C τ *(1+(rust C D P B L X r x u)^(n+n) * AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)))
include he ho hτ hY hu hΓ
lemma banner (U:Config G f)(hV:Healthy P.threshold Y V) (h:Fugue a U f' T C D P B r Γ u τ k q d o V)(l:List (Directions G c))(hl:l.length≤ n)(hA:∀ i∈l,P.dirBound (S.ratio.parent o) i):
    let f:=a.hymn T u q d k f' Γ U; Multi.Puff.Crest n f V ∧ ‖leftDerivs f l V‖≤ lyreFee C τ D P B S.patch.L X r x u:=by
  intro f
  obtain ⟨hx,hI,hL⟩:= Hera.exchange a U he ho hτ hY hu hΓ hV h l hl
  refine ⟨hx,?_⟩
  change ((leftDerivs f l V:ℝ):ℂ)=_ at hL; let b:= ripple C τ; have hb :0≤b:=mul_nonneg (by positivity [Heir.Lute.leading_one C]) hτ
  let Q:=a.twilight k T V; have ha:=he.cantos (k:=k) a hV hY ho; have hQ:= D.peak; let ρ:= rust C D P B S.patch.L X r x u; have hρ: 0≤ρ:=rust_nn hu
  let j:= 2*(n+n); rw [← Complex.norm_real,show ((leftDerivs f l V:ℝ):ℂ)=_ from hL]; apply (norm_integral_le_integral_norm ..).trans
  obtain ⟨hM,hh⟩ := purchased ∅ (zero_lt_one.trans_le hQ) ha.pos ha.peak j
  change Integrable (fun z => slopeEnvelope ∅ D.K j z) _ at hM
  simp only [slopeEnvelope,load,Finset.sum_empty,mul_zero, Real.exp_zero, mul_one, Finset.card_empty] at hM hh
  have hT := ((integrable_const (1:ℝ)).add (hM.const_mul (ρ^(n+n)))).const_mul b
  calc
    _ ≤ ∫ z, b*(1+ρ^(n+n)*powers z^j) ∂(Gaussian.cloud Q) := integral_mono hI.norm hT (vested a he ho hτ hY hu hΓ U hV h l hl hA)
    _ ≤ _ := by
      rw [integral_const_mul,integral_add (integrable_const _) (hM.const_mul _), integral_const, integral_const_mul, probReal_univ,one_smul]
      apply mul_le_mul_of_nonneg_left _ hb; gcongr; exact hh.trans (meter_mono (by positivity) _ (a.viewed hY B ho _))

end YM.PhysicalNext.JointLoad.Hera
