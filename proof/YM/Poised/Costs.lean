import YM.Poised.Orbit
/-!
# Charging arbitrary rank mixed directions

At all-mask arbitrary anchors.This reads bounds under `Sight`, no gauges or spin sym needed.
Credit actual engine basis.Borrow Next.FOUNDATIONS.TestBounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n : ℕ}
namespace Costs
theorem budget_probes {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : ι → V →L[ℝ] W) (h : ∀ x : V, (∀ i, p i x = 0) → x = 0) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ x : V, (∀ i, ‖p i x‖ ≤ b i*c) → ‖x‖ ≤ C*c := by
  by_contra! hu
  let B (n : ℕ) := (n : ℝ)+1
  have he (n) : 0 < B n := by unfold B; positivity
  choose c hc x hp hN using fun n : ℕ => hu (B n) (he n)
  have hx (n) : 0 < ‖x n‖ := lt_of_le_of_lt (mul_nonneg (he n).le (hc n)) (hN n)
  let y (n : ℕ) := ‖x n‖⁻¹ • x n
  have hy (n) : y n ∈ Metric.sphere (0:V) 1 := by simp [y,norm_smul,(hx n).ne']
  haveI : ProperSpace V := FiniteDimensional.proper ℝ _
  obtain ⟨z,hz,m,hm,ha⟩ := (isCompact_sphere (0:V) 1).isSeqCompact hy
  suffices z = 0 by simp [this] at hz
  apply h
  intro i
  have ht (n) : ‖p i (y n)‖ ≤ b i/B n := by
    unfold y
    rw [map_smul,norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hx n)).le]
    calc
      _ ≤ ‖x n‖⁻¹ * (b i*c n) := by
        apply mul_le_mul_of_nonneg_left (hp ..) (inv_pos.mpr (hx n)).le
      _ ≤ ‖x n‖⁻¹ * (b i*(‖x n‖/B n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hb i))
          (inv_pos.mpr (hx n)).le
        rw [le_div_iff₀ (he n), mul_comm]; exact (hN n).le
      _ = _ := by field_simp [(hx n).ne', (he n).ne']
  have hs : Tendsto (fun n => ‖p i (y n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) ht
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  exact norm_eq_zero.mp (tendsto_nhds_unique (((p i).continuous.continuousAt.tendsto.comp ha).norm)
    (hs.comp hm.tendsto_atTop))

section Dir
open Next.Foundations
variable (Z : Type)[NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z]
local instance : CompleteSpace Z := FiniteDimensional.complete ℝ Z
def tensorSpace (k : ℕ) : Submodule ℝ (Tensor.T (Fin k → ℝ) Z k) where
  carrier := {A | Tensor.Sym A}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) x s => by
    simp only [add_apply, ha x s, hb x s]
  smul_mem' r A ha x s := by
    change Tensor.Sym A at ha
    simp only [smul_apply, ha x s]

private lemma tensor_budget (k : ℕ) (q : Fin k → (Fin k → ℝ)) (b : (Fin k → ℝ) → ℝ)
    (hb : ∀ x, 0 ≤ b x) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Tensor.T (Fin k → ℝ) Z k,
      Tensor.Sym T → ∀ c : ℝ, 0 ≤ c → (∀ x, ‖Tensor.diagonal T x‖ ≤ b x*c) → ‖T q‖ ≤ C*c := by
  let u (x : Fin k → ℝ) : tensorSpace Z k →L[ℝ] Z :=
    (ContinuousMultilinearMap.apply ℝ _ Z fun _ => x) ∘L (tensorSpace Z k).subtypeL
  have hd (T : tensorSpace Z k) (ht : ∀ i, u i T = 0) : T = 0 := by
    apply Subtype.ext
    show T.val = 0
    apply Tensor.ext_diag T.val 0 T.property (fun _ _ => rfl)
    exact funext fun i => ht i
  obtain ⟨C,hC,hh⟩ := budget_probes (V:=tensorSpace Z k) (W:=Z) u hd b hb
  let K := ∏ j, ‖q j‖
  have hK : 0 ≤ K := Finset.prod_nonneg fun i _ => norm_nonneg _
  refine ⟨C*K, mul_nonneg hC.le hK, fun A hA c hc hx => ?_⟩
  have hi : ‖A‖ ≤ C*c := hh c hc ⟨A,hA⟩ hx
  calc
    ‖A q‖ ≤ ‖A‖*K := A.le_opNorm _
    _ ≤ C*c*K := mul_le_mul_of_nonneg_right hi hK
    _ = C*K*c := by ring

theorem mixed_budget (G₀ : Gauge) (k : ℕ) (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : BudgetPoint) (n : Side) (U:Config G₀ n) (o : Site n)
      (f : Config G₀ n → Z) (c : ℝ), ContDiffAt ℝ k (f ∘ increment U) 0 → (0 ≤ c ∧ ∀ l:Directions G₀ n, B.dirBound o l → ‖leftDerivs f (List.replicate k l) U‖ ≤ c) →
        ∀ w : Fin k → Directions G₀ n,
          (∀ i l, ‖w i l‖ ≤ a i*B.threshold*(1+(separation l.1 o : ℝ))^B.power) →
          ‖iteratedFDeriv ℝ k (f ∘ increment U) 0 w‖ ≤ C*c := by
  classical
  let r (x : Fin k → ℝ) := 1 + ∑ i, ‖x i‖*a i
  have hr (x) : 0 < r x := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (ha _))
  obtain ⟨C,hC,h⟩ := tensor_budget Z k (fun i => Pi.single i 1) (fun x => r x^k) (fun x => pow_nonneg (hr x).le _)
  refine ⟨C,hC,fun B n U o f c hf hc w hw => ?_⟩
  let L : (Fin k → ℝ) →L[ℝ] Directions G₀ n := ∑ i : Fin k,
    (ContinuousLinearMap.proj (R:=ℝ) i).smulRight (w i)
  have ht (x : Fin k → ℝ) : L x = ∑ i, x i • w i := by simp [L]
  let A := iteratedFDeriv ℝ k (f ∘ increment U) 0
  let T := A.compContinuousLinearMap (fun _ => L)
  have hp : Tensor.Sym T := by
    intro u e
    exact Analysis.sym_Jet (F:=Z) hf (L ∘ u) e
  have he (x : Fin k → ℝ) : ‖Tensor.diagonal T x‖ ≤ r x ^ k * c := by
    let p := (r x)⁻¹ • L x
    have hb : B.dirBound o p := by
      intro l
      let u := B.threshold * (1+(separation l.1 o : ℝ))^B.power
      have hU : 0 ≤ u := mul_nonneg B.threshold_pos.le (pow_nonneg (by positivity) _)
      have H : ‖L x l‖ ≤ r x*u := calc
        ‖L x l‖ = ‖∑ i, x i • w i l‖ := by rw [ht]; simp [Finset.sum_apply]
        _ ≤ ∑ i, ‖x i • w i l‖ := norm_sum_le ..
        _ ≤ ∑ i, (‖x i‖*a i)*u := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_of_le_of_eq (hw i l) (mul_assoc ..)) (norm_nonneg _)
        _ ≤ r x*u := by
          unfold r; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left zero_le_one) hU
      change ‖(r x)⁻¹ • L x l‖ ≤ u
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hr x)).le]
      exact le_trans (mul_le_mul_of_nonneg_left H (inv_pos.mpr (hr x)).le) (by simp [(hr x).ne'])
    have hi : ‖Tensor.diagonal A p‖ ≤ c := by
      rw [show Tensor.diagonal A p = iteratedDeriv k (fun t : ℝ => f (increment U (t • p))) 0 from
        (iteratedDeriv_on_line hf p).symm, ← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
      exact hc.2 p hb
    change ‖Tensor.diagonal A (L x)‖ ≤ _
    calc
      ‖Tensor.diagonal A (L x)‖ = ‖Tensor.diagonal A (r x • p)‖ := by
        congr 2; unfold p; rw [smul_smul, mul_inv_cancel₀ (hr x).ne',one_smul]
      _ = r x ^ k * ‖Tensor.diagonal A p‖ := by
        rw [Tensor.homogeneous, norm_smul, Real.norm_of_nonneg (pow_nonneg (hr x).le _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (pow_nonneg (hr x).le _)
  have hT : T (fun i => Pi.single i 1) = A w := by
    unfold T; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply congr_arg A
    funext i
    simp [ht, Pi.single_apply, ite_smul]
  change ‖A w‖ ≤ _
  rw [← hT]; exact h T hp c hc.1 he

end Dir
open Beacon Next.Foundations
variable (H:TaperHol)(c:Side)(b:Cover)
-- target Darger.Action.Mark.Val
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
local notation "N"=> Pairs (SpinMode d)
abbrev stageZ (v :ℝ):Ψ→ₗ[ℂ]Z := (engine v N).toLinearMap.comp (whisper H.T b).toLinearMap
abbrev producing (x : Grid c→Ψ)(v:ℝ) (J:Labels.Jet su) (h:ℝ):Z:= stageZ H c b v (x (current H b d J h))
lemma warmP (v:ℝ)(T:Finset N)(x:Z): coef T (engine v N x)= (v:ℂ)^T.card*coef T x:=fundW x v T
private lemma scale_cst {Z₀:Type*}[NormedAddCommGroup Z₀][NormedSpace ℝ Z₀](v:ℝ)(f:ℝ→Z₀)(x:ℝ)(j:ℕ)(he:ContDiffAt ℝ j f x): iteratedDeriv j (fun s=> v • f s) x= v • iteratedDeriv j f x:= clm_step f j x he (v • ContinuousLinearMap.id ℝ Z₀)
private lemma stretch_cst {Z₀:Type*}[NormedAddCommGroup Z₀][NormedSpace ℝ Z₀](v:ℝ)(x:Z₀): ‖v • x‖= ‖v‖*‖x‖:= norm_smul ..
lemma tau_cost (d j : ℕ)(J:Labels.Jet su)(hj:j≤d):∃ C:ℝ,0≤C∧∀ (H:TaperHol)(c:Side)(b:Cover)(θ:ℝ),0≤θ→θ≤1 →∀ e:Edge (Site c), ‖(iteratedDeriv j (lamp (d:=d) H b ∘ scaledD d (θ • J)) 0) e‖ ≤ C*θ*(1+(separation e.1 (wrap c b):ℝ))^(d*d):=by
    classical
    choose C hC h using Verse.lampFee d
    let v (n:ℕ):= iteratedDeriv n (scaledD d J) 0
    let t(r:OrderedFinpartition j):= ∏ i, ‖v (r.partSize i)‖
    let K:= ∑ r:OrderedFinpartition j,C r.length*t r
    refine ⟨K,sum_nonneg (fun i _=> mul_nonneg (hC _) (prod_nonneg fun _ _=> norm_nonneg _)),fun H c b θ hx hv e=>?_⟩
    by_cases ht:j=0; · subst j; rw [iteratedDeriv_zero,Function.comp_apply, scaled_zero,at_dark]; change ‖(0:su.Color)‖≤_; rw [norm_zero]; have hK: 0≤K:=sum_nonneg (fun _ _=>mul_nonneg (hC _) (prod_nonneg fun _ _=>norm_nonneg _)); positivity
    rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ (d:ℕ∞) _ _ from (scaled_zero d (θ • J)).symm ▸ ((fluent H b d c).contDiffAt.of_le le_top)) (scaled_smooth d _) (by exact_mod_cast hj),scaled_zero,Finset.sum_apply]; apply (norm_sum_le ..).trans; unfold K; rw [Finset.sum_mul,Finset.sum_mul]; apply Finset.sum_le_sum; intro r _
    have he(i)(hi:i≤d): iteratedDeriv i (scaledD d (θ • J)) 0= θ • v i:=by rw [show scaledD d (θ • J)=(fun p=>θ • scaledD d J p) from funext fun _=>funext fun _=> by simp only [scaledD,trunk,scaleJet]; exact smul_comm _ θ _]; exact scale_cst θ (scaledD d J) 0 i ((scaled_smooth d J).of_le (by exact_mod_cast hi))
    simp_rw [he (r.partSize _) ((r.partSize_le _).trans hj)]
    apply (h r.length H c b e _).trans
    have ha(i:Fin r.length): ‖θ • v (r.partSize i)‖= θ*‖v (r.partSize i)‖:= (stretch_cst θ (v (r.partSize i))).trans (by rw [Real.norm_of_nonneg hx])
    simp only [ha, prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]; 
    let u:=1+(separation e.1 (wrap c b):ℝ); have hU:1≤u:=by simp [u]
    apply le_trans (b:=C r.length*u^(d*d)*(θ*t r)); swap; · unfold u t; exact le_of_eq (by ring)
    have hR:j≤0∨1≤r.length:= Or.inr (r.length_pos (Nat.pos_of_ne_zero ht))
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (by exact Nat.mul_le_mul_left d (r.length_le.trans hj))) (hC _)) (mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one hx hv (by omega : 1≤r.length)).trans_eq (pow_one _)) (prod_nonneg fun _ _=>norm_nonneg _)) (mul_nonneg (pow_nonneg hx _) (prod_nonneg fun _ _=>norm_nonneg _)) (mul_nonneg (hC _) (by positivity))
lemma curvatureW (d j :ℕ)(J:Labels.Jet su)(hj:j≤d): ∃ C:ℝ,0≤C ∧ ∀ (H:TaperHol)(c: Side)(b:Cover)(k:ℕ)(P:BudgetPoint)(v:ℝ)(x:Grid c→Lat.Fields c 6)(r:ℝ)(D:Support c), Sight D (wrap c b) k P v x r→ surface d ≤ k→ d ≤ P.order → d*d ≤ P.power→ 0 ≤ v → ‖iteratedDeriv j (producing H c b x v (P.threshold • J) (d:=d)) 0‖≤ C*r :=by
   choose C hp h using fun (r:OrderedFinpartition j)(i:Fin r.length)=>tau_cost d (r.partSize i) J ((r.partSize_le i).trans hj)
   choose V hV hΛ using fun r:OrderedFinpartition j=>mixed_budget (SpinPol d) su r.length (C r) (hp r)
   have hh : 0≤penny d:=by unfold penny; positivity
   refine ⟨∑ r, V r*penny d,sum_nonneg fun _ _=>mul_nonneg (hV _) hh,?_⟩
   intro H c b k P v x r D hw hξ hd he hv; let B:= P.threshold; let Z':= B • J; let T := (stageZ (d:=d) H c b v); let X:= T ∘ x; let W(h:ℝ):= scaledD d Z' h; let V' := lamp H b (d:=d) (c:=c) ∘ W
   have hG : Healthy B D (1: Grid c):= one_healthy D B P.threshold_pos.le
   let L:= (T.restrictScalars ℝ).toContinuousLinearMap
   have ht : ContDiffAt ℝ (d:WithTop ℕ∞) (X ∘ increment 1) 0:= L.contDiff.contDiffAt.comp (f:=x ∘ increment 1) _ ((hw.use 1 hG).of_le (by exact_mod_cast hd))
   have hy:V' 0=0:=by unfold V' W; rw [Function.comp_apply,scaled_zero,at_dark]
   have hσ : Tendsto W (𝓝 0) (𝓝 0):=(scaled_zero d _ ▸ (scaled_smooth d Z').continuousAt)
   have hS: producing (d:=d) H c b x v Z' =ᶠ[𝓝 0] ((X ∘ increment 1) ∘ V'):=by filter_upwards [hσ.eventually (at_east H b (c:=c) (d:=d))] with y hy; exact congr_arg X hy
   rw [hS.iteratedDeriv_eq,iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hy.symm ▸ ht) (show ContDiffAt ℝ (↑d:WithTop ℕ∞) V' 0 from (show ContDiffAt ℝ (↑d:WithTop ℕ∞) (lamp (d:=d) H b (c:=c)) (W 0) from (show W 0=0 from scaled_zero d Z').symm ▸ ((fluent H b d c).contDiffAt.of_le le_top)).comp _ (scaled_smooth d _)) (by exact_mod_cast hj), hy]
   apply (norm_sum_le _ _).trans; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro R _; rw [mul_assoc]; have hy: R.length≤ d := R.length_le.trans hj
   refine hΛ R P c 1 (wrap c b) X _ (ht.of_le (by exact_mod_cast hy)) ⟨mul_nonneg hh hw.travels,?_⟩ _ ?_
   · intro l hl; let s:= List.replicate R.length l; have hs:s.length≤P.order:= (List.length_replicate ..) ▸ (hy.trans hd)
     change ‖leftDerivs (L∘x) s 1‖ ≤ _; rw [Push.Local.left_linear L s (hw.use 1 hG) hs]; exact (lots H.T b v (leftDerivs x s 1) hv hξ).trans (mul_le_mul_of_nonneg_left (hw.pole 1 hG s hs (fun i hi=> (List.mem_replicate.mp hi).2.symm ▸ hl)) hh)
   intro i l
   exact (h R i H c b B P.threshold_pos.le P.threshold_le l).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) he) (mul_nonneg (hp R i) P.threshold_pos.le))
end Costs
end YM.Massive.Poised
