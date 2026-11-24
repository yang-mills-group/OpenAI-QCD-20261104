import YM.Kly.Palm
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(RA:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
open OS.Ground (Panes)
def amplitude (V : Chamber S timeAxis) (b : Future F timeAxis) := V.D.orthogonalProjectionOnto (V.GNS.plant b)
def current (S : F.Kernel) (b : Future F timeAxis) (s : ℕ) := Bridge.kernel S timeAxis (travel b (s:ℝ≥0)).val (travel b (s:ℝ≥0)).val

theorem magnitude (V : Chamber S timeAxis) (b : Future F timeAxis) (s : ℕ) : current S b s = ↑(‖V.flow.E (s:ℝ≥0) (V.GNS.plant b)‖^2) := by
  unfold current; rw [← V.GNS.measure, V.atBirth, inner_self_eq_norm_sq_to_K];norm_cast
lemma trail (V : Chamber S timeAxis) (b : Future F timeAxis) : Tendsto (current S b) atTop (𝓝 (↑(‖amplitude V b‖^2):ℂ)) := by
  rw [show current S b=(fun s : ℕ => ↑(‖V.flow.E (s:ℝ≥0) (V.GNS.plant b)‖^2)) from funext (magnitude V b)]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((V.flow.emerges (V.GNS.plant b)).comp tendsto_natCast_atTop_atTop |>.norm.pow 2)

lemma side (V : Chamber S timeAxis) (b : Future F timeAxis) : inner ℂ V.omega0 (amplitude V b)=pointMoment S b.val := by
  unfold amplitude Chamber.omega0; simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold Chamber.omega; rw [V.GNS.measure]; rfl

lemma fits (V : Chamber S timeAxis) (H : Fields.Euclidean S) (b : Future F timeAxis) :
    ‖amplitude V b-pointMoment S b.val • V.omega0‖^2 = ‖amplitude V b‖^2-‖pointMoment S b.val‖^2 := by
  rw [norm_sub_sq (𝕜:=ℂ), norm_smul, show ‖V.omega0‖=1 from nil_norm V.GNS H,mul_one,inner_smul_right,← inner_conj_symm (amplitude V b),side,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show ∀ i : ℝ, RCLike.re (K := ℂ) (↑i:ℂ)=i from fun _ => rfl]
  ring

variable (R:Panes P.algebra)(ht:R.Shines (dome V) P.algebra.subtype V.omega0)
include P Y R H ht in
lemma champ (s:ℕ)(b:Future F timeAxis): Continuous (fun i:R.X=> current (bloom P H (R.character i)) b s) ∧ (∫ i,current (bloom P H (R.character i)) b s ∂R.μ)=current S b s:=by
      let p:=travel b (s:ℝ≥0); let w:=reflect p.val t₀ ++ p.val; have hx:distinct w:=twoSides p.property p.property
      have hv: (fun i:R.X=> current (bloom P H (R.character i)) b s)= (fun i:R.X=> R.character i (M P _ hx)):=funext fun i=> bless P H (R.character i) w hx
      constructor; · rw[hv]; exact ht.weak _
      rw[show (∫ i,current (bloom P H (R.character i)) b s ∂R.μ)=(∫ i,R.character i (M P _ hx) ∂R.μ) from congr_arg (fun f:R.X→ℂ=> ∫ i,f i ∂R.μ) hv,ht.ground]; obtain ⟨u,d,hu⟩:= Spread.place_exists hx; change inner ℂ V.omega0 ((M P w hx).val V.omega0)=pointMoment S w; rw [overline P H _ _ u hu, P.insertValue _ d hu,invariance Y hx]
private lemma at_M (u : P.algebra) (h : R.Shines (dome V) P.algebra.subtype V.omega0) : (∫ i, ‖R.character i u‖^2 ∂R.μ)=‖u.val V.omega0‖^2 := by
  have he i : R.character i (star u*u)= ↑(‖R.character i u‖^2) := by
    rw [map_mul,map_star];change starRingEnd ℂ _ * _=_; rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have ht := h.ground (star u*u); simp_rw [he,integral_complex_ofReal] at ht
  apply Complex.ofReal_injective; rw [ht,Complex.ofReal_pow]
  exact (ContinuousLinearMap.adjoint_inner_right u.val V.omega0 (u.val V.omega0)).trans (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (u.val V.omega0))

variable (Tα:R.X→Fields.Kernel F)(Qo:∀ i:R.X,Chamber (Tα i) timeAxis)(hc6:∀ k p,Continuous (fun i:R.X=>current (Tα i) p k)∧(∫ i:R.X,current (Tα i) p k ∂R.μ)=current S p k)(h7:∀ (i:R.X)(v:Cluster F)(hx:distinct v),pointMoment (Tα i) v=R.character i (M P _ hx))(hT:∀ i,Fields.Euclidean (Tα i))
include P Y R H ht hT hc6 h7 Qo

lemma exp_real (b:Future F timeAxis) :
    ∀ᵐ i ∂R.μ, amplitude (Qo i) b = pointMoment (Tα i) b.val • (Qo i).omega0 := by
  haveI := ht.normalized
  let w (i : R.X) := ‖amplitude (Qo i) b‖^2
  have hw i : 0≤w i := sq_nonneg _
  let F0 s (i : R.X) := (current (Tα i) b s).re
  have hu k : Continuous (F0 k) := Complex.continuous_re.comp (hc6 k b).1
  have hz0 i : Tendsto (fun j => F0 j i) atTop (𝓝 (w i)) := Complex.continuous_re.continuousAt.tendsto.comp (trail (Qo i) b)
  have he s : ∀ᵐ i ∂R.μ, ‖F0 s i‖ ≤ F0 0 i := by
    apply Eventually.of_forall; intro i
    unfold F0; rw [magnitude (Qo i),magnitude (Qo i),Complex.ofReal_re,Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (((Qo i).flow.norm_decrease ((Qo i).GNS.plant b)) (by exact_mod_cast Nat.zero_le s : ((0:ℕ):ℝ≥0)≤ (s:ℝ≥0))) 2
  have Hz := (hu 0).integrable_of_hasCompactSupport (μ := R.μ) (HasCompactSupport.of_compactSpace _)
  have hm := tendsto_integral_of_dominated_convergence (μ := R.μ) (F0 0) (fun n => (hu n).aestronglyMeasurable) Hz he
    (f:= w) (Eventually.of_forall hz0)
  have hf k : (∫ i, F0 k i ∂R.μ) = (current S b k).re := by
    rw [← (hc6 k b).2]; exact (integral_re ((hc6 k b).1.integrable_of_hasCompactSupport (μ:=R.μ) (HasCompactSupport.of_compactSpace _)))
  have hi : (∫ i, w i ∂R.μ)=‖amplitude V b‖^2 := by
    simp_rw [hf] at hm; exact tendsto_nhds_unique hm (Complex.continuous_re.continuousAt.tendsto.comp (trail V b))
  let k:= M P b.val b.property.1
  have HH i : pointMoment (Tα i) b.val=R.character i k := h7 i b.val b.property.1
  let f (i : R.X) := w i- ‖R.character i k‖^2
  have H1 : Integrable w R.μ := ⟨aestronglyMeasurable_of_tendsto_ae _ (fun i : ℕ => (hu i).aestronglyMeasurable (μ:=R.μ))
    (Eventually.of_forall hz0),hasFiniteIntegral_of_dominated_convergence Hz.2 he (Eventually.of_forall hz0)⟩
  have H2 : Integrable (fun x => ‖R.character x k‖^2) R.μ := by simpa only [Pi.pow_def] using!  ((ht.weak k).norm.pow 2).integrable_of_hasCompactSupport (μ := R.μ) (HasCompactSupport.of_compactSpace _)
  have Hz i : f i= ‖amplitude (Qo i) b-pointMoment (Tα i) b.val • (Qo i).omega0‖^2 := by rw [fits (Qo i) (hT i),HH]
  have hx : (∫ i,f i∂R.μ)=0 := by
    unfold f; rw [integral_sub H1 H2,at_M P R k ht, show k.val V.omega0=amplitude V b from almost P H b, hi,sub_self]
  have hh : ∀ᵐ i ∂R.μ, f i=0 := (integral_eq_zero_iff_of_nonneg (f:= f) (fun i => (Hz i).symm ▸ sq_nonneg _) (H1.sub H2)).1 hx
  filter_upwards [hh] with i hi; rw [Hz] at hi; exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa only [sq_eq_zero_iff] using hi))

omit Qo
abbrev horizon (V : Chamber S timeAxis) (i : ℕ → Future F timeAxis) := DenseRange (Finsupp.linearCombination ℂ
    (fun x => V.GNS.plant (i x)))

lemma lifts (Qo : ∀ i:R.X,Chamber (Tα i) timeAxis) (f:ℕ→Future F timeAxis)(hp:∀ i,horizon (Qo i) f):
    ∀ᵐ i ∂R.μ,(Qo i).UniqueHeat := by
  have hi := ae_all_iff.mpr (fun b : ℕ => exp_real P H Y R ht Tα Qo hc6 h7 hT (f b))
  filter_upwards [hi] with i hx
  let Q := Qo i
  let U : Submodule ℂ Q.D := Submodule.span ℂ {Q.omega0}
  have he : DenseRange (Q.D.orthogonalProjectionOnto ∘ Finsupp.linearCombination ℂ (fun x => (Qo i).GNS.plant (f x))) :=
    (show Surjective _ from fun p => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩).denseRange.comp (hp i) Q.D.orthogonalProjectionOnto.continuous
  have ht (x : ℕ→₀ℂ) : Q.D.orthogonalProjectionOnto (Finsupp.linearCombination ℂ (fun x => (Qo i).GNS.plant (f x)) x) ∈ U := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y X Y => simpa only [map_add] using! U.add_mem X Y
    | single j c =>
      simp_rw [Finsupp.linearCombination_single,map_smul]
      exact U.smul_mem _ ((Submodule.mem_span_singleton).2 ⟨_,(hx j).symm⟩)
  intro v
  suffices hx : v∈ U by obtain ⟨k,h⟩:=(Submodule.mem_span_singleton).1 hx; exact ⟨k,h.symm⟩
  refine closure_minimal ?_ (show IsClosed (U : Set _) from (by unfold U; exact Submodule.closed_of_finiteDimensional _)) (he v)
  rintro _ ⟨x,rfl⟩; exact ht x

end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.lifts
