import YM.QCD.Oasis.Wake
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Trebles
/-! # slope exact. central short & charge hanging.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {I:Type}[Fintype I][DecidableEq I]{s v j t u a:ℝ}{M:ℕ}
lemma heartV {φ ψ:E×Poll.Body I→ℝ}{ρ:E→Poll.Body I}{A:E→ Matrix I I ℝ}(h: Golf φ ψ ρ A M s u u t)(hx:0≤j)(hy:j ≤ s) : Golf φ ψ ρ A M j u u t:=⟨h.pos,h.pos',h.small,h.small',hx,h.curve,fun i z p hi=> h.color _ z p (hi.trans hy),h.station,h.gram⟩
lemma alley {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F][MeasurableSpace F][BorelSpace F][SecondCountableTopology F]
    {ι:Type}[MeasurableSpace ι]{f:ι→ℝ}{g:ι→F}(r:Measure ι){Z:Set ι} (h:Integrable f r)(hr : MeasurableSet Z)(hg:∀ i,0≤ f i)(ht: Measurable g)(hv:∀ i,‖g i‖ ≤ u)(hf : (∫ i,f i ∂r) - (∫ i in Z,f i ∂r) ≤ s) :
       ‖(∫ i,f i • g i ∂r)-(∫ i in Z,f i • g i ∂r)‖ ≤ s*|u| := by
  let m i:= f i • g i; have hm:Integrable m r:= Beam.envDash g ⟨ht,u,hv⟩ _ h; rw [←integral_add_compl hr hm,add_sub_cancel_left]; rw [← integral_add_compl hr h, add_sub_cancel_left] at hf
  exact (norm_integral_le_integral_norm _).trans ((integral_mono hm.integrableOn.norm (h.integrableOn.mul_const |u|) (fun i => by rw [norm_smul,Real.norm_of_nonneg (hg i)]; exact mul_le_mul_of_nonneg_left ((hv i).trans (le_abs_self _)) (hg i))).trans (by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hf (abs_nonneg _)))
variable {G : Gauge} {L : Side} {P : Teller G} {c f : Side} {S : StepData c f} {x W K y σ C e β B v' b D M' p w Z: ℝ} {n:ℕ}
variable {F : Forest S.ratio} {Y : Tube G S} {k : S.Choices} {A : Before G σ C S.patch.J S.kernel (n+3)} {ρ : Bid.Dir G c→AxisChart G F}{η:ChartRatio G}{Ω : BudgetPoint}
local notation "M" => A.tables Y.high S.patch
local notation "μ" => Lapis.orbit F ρ
local notation "R"=>Poll.Body (Precision.Key F G)
local notation "Ys"=>Positions (Uniform.Primary c G)
local notation "T"=> Lapis.gram F Y.up Y.high ρ k
local notation "ψ"=> mist F η Y.up
local notation "Φ"=> Lapis.table F k Y.up Y.high
local notation "V" => (fun (x: Ys)=> represent (tint G _ x))
local notation "H"=>eaves G L x
local notation "r'"=>wick G L B x
local notation "R₀"=>Pane.virgin Y Ω β
local notation "ZB"=>gStep β
variable (h:Intake P Y x (Pane.virgin Y Ω β)) (he:LocalRatio η)
variable (F Y Ω β) in
abbrev endoP (U : Ys) := overall F Y Ω β (represent (tint G _ U))
local notation "f₀"=>endoP β F Y Ω
-- income on sector
variable {X: Positions (Uniform.Primary c G)} (hp:LawP Y A Ω F ρ k L η B W x β X)
local notation "g"=> ballots Φ ψ μ T D
local notation "G'"=>sweep (T 0)⁻¹
local notation "m'"=> (fun z=> solar F η β* Real.exp (-coverLog F Y η k ρ β z))
variable (hD:0 ≤ D)(hc:D ≤ wick G L B x){z: Positions (Uniform.Primary c G)} (hx : ‖z‖< eaves G L x)(hy:‖z-X‖ ≤ furl G L x)
local notation "S'"=> staying F (μ z) ZB D (V z)
include hp hD hc h he hx hy
section transfer
variable {D':Type} [NormedAddCommGroup D'][NormedSpace ℝ D'][CompleteSpace D'][MeasurableSpace D'][BorelSpace D'][SecondCountableTopology D']
lemma timber (J:R→D') (u:F.Slice G → D') (hv: RG.Envelope u)(hh:Integrable (fun i=>g (ZB,z) i • J i) G')
    (hr:∀ i:R, ‖i‖ ≤ D → J i=u (draw F (V z) (μ z+ZB • i))) : (∫ i in S', f₀ z i • u i ∂F.order G) = m' z • ∫ i,g (ZB,z) i • J i ∂G' :=by
   let m:= F.order G; let f i:= f₀ z i • u i
   have h' := amt F Y Ω β x P h (V z); have hf:Integrable f (m.restrict S'):= envDash u hv _ (h'.1.integrable _ |>.integrableOn)
   have hG i (hi : ‖(i:R)‖≤ D):= hp.hue z hx hy i (hi.trans hc); have hβ:0< β:=h.positive
   let T':= heartV hp.habit.1 hD hc
   apply concrete; intro L'
   have hw:= cubits F η (μ z) (V z) (ZB) D (fun i=> L' (f i)) (gS β hβ).1 he (fun i hi=>(hG i hi).1) (L'.continuous.comp_stronglyMeasurable ((h'.1.meas.smul hv.meas).stronglyMeasurable))
   rw [← L'.integral_comp_comm hf,map_smul, ← L'.integral_comp_comm hh, recommendsV _ (T'.gram 0 (by simp [T'.pos])).1.inv]; change (∫ i in S',L' (f i) ∂F.order G) = (m' z) * ∫ i,lens₀ (T 0)⁻¹ i * _; rw [hw,← integral_const_mul,← integral_const_mul, ← integral_indicator (measurableSet_closedBall)]; apply integral_congr_ae; filter_upwards with i
   by_cases ht:i∈ closedBall (0:R) D
   · have hu:= mem_closedBall_zero_iff.mp ht; rw [Set.indicator_of_mem ht,hr i hu,map_smul,ballots, Set.indicator_of_mem ht]
     rw [map_smul]; have hf := reserves F Y η k ρ Ω β D T' hβ hp.habit.2.1 (h.ready.knobs.symm ▸ h.ready.kernel) hx (fun i hi=> (hG i hi).2.2) he (fun i hi=>(hG i hi).1) (fun i hi=> (hG i hi).2.1) i ht
     unfold endoP; dsimp only [smul_eq_mul]; rw [← mul_assoc,← mul_assoc, mul_assoc (ZB ^ _),hf]; ring -- check Par.
   rw [Set.indicator_of_notMem ht,map_smul,ballots,Set.indicator_of_notMem ht]; simp
lemma timber' : (∫ i in S', f₀ z i ∂ F.order G)=m' z * ratify Φ ψ μ T D (ZB,z):= by
   have hG i (hi : ‖(i:R)‖≤ D):= hp.hue z hx hy i (hi.trans hc); exact pricing F Y η k ρ Ω β D (heartV hp.habit.1 hD hc) h.positive hp.habit.2.1 (h.ready.knobs.symm ▸ h.ready.kernel) hx (fun i hi=> (hG i hi).2.2) he (fun i hi=>(hG i hi).1) (fun i hi=> (hG i hi).2.1) (amt F Y Ω β x P h (V z) |>.1.meas.stronglyMeasurable)
end transfer
omit he
-- tails may pay relative any power
lemma midday (hi:1 ≤ n) (hf:Lantern.fee n W (wick G L B x)*eaves G L x≤1)(ht : (G').real (closedBall 0 D)ᶜ ≤ a):
    ratify Φ ψ μ T (wick G L B x) (ZB,z) - ratify Φ ψ μ T D (ZB,z) ≤ a*Real.exp 1:=by
   let g' := ballots Φ ψ μ T r' (ZB,z); let g₀:=g (ZB,z); let r:=G'; let p':= closedBall (0:R) D; let q := closedBall (0:R) r'
   have hu:Golf Φ ψ μ T n D H H W:=heartV hp.habit.1 hD hc
   have hA:‖ZB‖< H:=by rw [Real.norm_of_nonneg (Fare.gS β h.positive).1.le]; exact hp.habit.2.1
   have hg i:g' i≤ Real.exp 1:=by
      by_cases h:i ∈ q
      · exact (Set.indicator_of_mem h _).trans_le (Real.exp_monotone ((ether _ hp.habit.1 hx hA hi (by simpa using hf) _ (mem_closedBall_zero_iff.mp h)).2))
      exact (Set.indicator_of_notMem h _).trans_le (Real.exp_pos _).le
   have he : Integrable g' r := by
      apply Integrable.of_bound (duties r' hp.habit.1 hx hA).aestronglyMeasurable (Real.exp 1)
      exact ae_of_all _ fun i=> by rw [Real.norm_of_nonneg (show 0≤ g' i from Set.indicator_nonneg (fun i _=> (Real.exp_pos _).le) i)]; exact hg i
   have hf : (∫ i in p', g' i ∂r)=∫ i,g₀ i ∂r := by
      rw [← integral_indicator (measurableSet_closedBall)]; apply integral_congr_ae; filter_upwards with i; unfold g' g₀ ballots; by_cases hz:i∈p'
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (closedBall_subset_closedBall hc hz),Set.indicator_of_mem hz] -- q
      rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
   change (∫ i, g' i ∂r)- (∫ i,g₀ i ∂r) ≤_; rw [← hf, ← integral_add_compl (show MeasurableSet p' from measurableSet_closedBall) he]; -- marker infer p'
   rw [add_sub_cancel_left]; exact (integral_mono he.integrableOn (integrable_const _) hg).trans (by rw [setIntegral_const, smul_eq_mul]; exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le)
end YM.QCD.Oasis
