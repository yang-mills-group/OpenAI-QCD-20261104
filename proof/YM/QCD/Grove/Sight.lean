import YM.QCD.Coda.Spoke
import YM.QCD.Purse.Major
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views
/-! # Seam estimates ORD size on ROW with AUX budgets ANY period.
 Local hypotheses certified in Spine. Scope: projection. Works
 for pure Kin at seams and uses strict equality extension BEFORE reg signatures.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard.QG
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X t : ℝ} {f : Config G c→ℝ}
variable {ι E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
-- shadows Pace. No charts across SEAMS of tsum, use income inside.
structure Mains (P:BudgetPoint)(A:ι→ Config G c→E)(T:ℝ):Prop where
   earns : ∃ p:ι→ ℝ,SumBudget p T∧ forall i V, V∈ Boulevard.sunny P → Push.Local.Chart P.order (A i) V ∧∀ l :List (Directions G c),l.length ≤ P.order→(∀ v∈l,‖v‖≤P.threshold)→‖leftDerivs (A i) l V‖≤p i
variable {x:Config G c}{A:ι→ Config G c→E}(hp:Mains P A T)(K : E→L[ℝ]ℝ)(he:‖K‖≤1)
include he hp
lemma oreB(x: Config G c) (hx:x∈sunny P) : let f:=K ∘ (fun V=>∑' i,A i V); Push.Local.Chart P.order f x ∧∀ l:List (Directions G c), l.length≤P.order→ (∀ v∈l,‖v‖≤P.threshold)→ ‖leftDerivs f l x‖ ≤ T:=by
    obtain ⟨p,hp,hh⟩:=hp.earns
    have hK X:‖K X‖≤ ‖X‖:= (K.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
    intro f; let C i:= K ∘ A i; let H V:=∑' i,C i V; have he V (hv:V∈sunny P):f V=H V:= K.map_tsum (Summable.of_norm_bounded hp.2.1 (fun i=> (hh i V hv).2 [] (by simp) (by simp))) -- signature
    have hX:f=ᶠ[𝓝 x] H:= ((Boulevard.sky P).mem_nhds hx |> fun h=> Eventually.mono h (fun i hi=> he i hi))
    have hg i V (hx: V∈sunny P): Push.Local.Chart P.order (C i) V:= K.contDiff.contDiffAt.comp 0 (hh i V hx).1
    have hu i V (hx:V∈sunny P) (l:List (Directions G c))(hl:l.length≤ P.order)(hp:∀ i∈l,‖i‖≤P.threshold): ‖leftDerivs (C i) l V‖≤ p i:=by unfold C; rw [Push.Local.left_linear K l (hh i V hx).1 hl]; exact (hK _).trans ((hh i V hx).2 l hl hp)
    have hv : Termwise P.order (sunny P) C:=by
       refine ⟨hg,fun l hl=>?_⟩
       let d:= P.threshold + l.toFinset.sum (fun i=> ‖i‖); have hd : 0<d:= add_pos_of_pos_of_nonneg P.threshold_pos (sum_nonneg fun i _=> norm_nonneg _)
       have hV : ∀ i∈l, ‖i‖≤d:= fun i hi=> (single_le_sum (fun a _=> norm_nonneg a) (List.mem_toFinset.mpr hi)).trans (le_add_of_nonneg_left P.threshold_pos.le)
       let b:=d/P.threshold; have hb: 0<b:= div_pos hd P.threshold_pos; let Y:=l.map fun i=> b⁻¹ • i
       have hY:Y.length=l.length:= by simp [Y]
       have ht : Y.map (fun i=>b • i)=l:= by simp [Y,List.map_map,Function.comp_def,smul_smul,hb.ne']
       have hv i (hi:i∈Y): ‖i‖≤P.threshold := by obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hb).le]; apply le_trans (mul_le_mul_of_nonneg_left (hV _ ha) (inv_nonneg.mpr hb.le)); apply le_of_eq; unfold b; field_simp
       refine ⟨fun i=> b^Y.length*p i,hp.2.1.mul_left _,fun i x hx=>?_⟩; rw [← ht,March.expands,norm_smul,Real.norm_of_nonneg (pow_pos hb _).le]; exact mul_le_mul_of_nonneg_left (hu i x hx Y (hY.trans_le hl) hv) (pow_nonneg hb.le _)
    obtain ⟨hg,hv⟩:=Termwise.smooth_exchange (Boulevard.sky P) hv x hx
    have hT : Tendsto (increment x) (𝓝 0) (𝓝 x):=by convert! (increment_cont x).tendsto 0 using 1; rw [Work.G07.at_zero_increment]
    have hf:f ∘ increment x=ᶠ[𝓝 0] H ∘ increment x:= hX.comp_tendsto hT
    refine ⟨hg.congr_of_eventuallyEq hf,fun l hl hV=>?_⟩; rw [Push.Local.left_congr l x hf, show leftDerivs H l x=_ from hv l hl]; have hk:= budget_mono hp (g:=fun i=>‖leftDerivs (C i) l x‖) (fun i=>norm_nonneg _) (fun i=> hu i x hx l hl hV); exact (norm_tsum_le_tsum_norm hk.2.1).trans hk.2.2
omit hp he
-- No centering; H= Sum-Lie low contribution net including vacancy. strict-
variable (G L)
local notation "p'" => eaves G L
local notation "d'" => furl G L
lemma vision (j : ℕ) : ∀ᶠ x in atTop,∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=j →
    ∀ (c:Side) (W:Positions (Uniform.Primary c G)), ‖W‖+2*d' x < p' x →
      flags P.threshold (actual W)=∅ → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E](ι:Type)(u:ι→ Config G c→E)(H f:Config G c→E)
    (v b:ℝ), Mains P u b→Push.Local.Chart P.order H (actual W) → (∀ V∈ sunny P,H V=f V-∑' i,u i V) →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*d' x < p' x → actual W'∈ sunny P→ Brush j v (p' x)⁻¹ (f∘actual) W') →
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs H l (actual W)‖ ≤ ticket j v + b:= by
  obtain ⟨s,hs,he⟩:= oar G j
  obtain ⟨J,d,hS⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hc,hQ⟩:= seek (G:=G) hS.pos
  obtain ⟨p,h,hp⟩:= expCost G 2 1
  let u t:= s*(2*Pressure.fiery G t L); let t x:=(1+ (j:ℝ))* u x; let r:= royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
  have hR : Rate G L (-(1/2)) (fun x=>(1+r)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let w x:= Uniform.shade G* p' x
  have hw: Rate G L vow w:= (Sienna.edge G L).mul_left _
  let g x:=4*(sunLength p (w x) * r)
  have hg : Rate G L vow g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw vow_ok hc,hw.below vow_ok 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=vow*2) (hg.pow 2) (show vow*2 < -(1/2:ℝ) by norm_num [vow]), softly G L, hR.below (by norm_num) 1 zero_lt_one,
    Sienna.contraction G L (a:= j.factorial*J) zero_lt_one hR (show -(1/2:ℝ)<vow by norm_num [vow])] with
    x hx hx' hw hX hZ hv he' P ht hb hP c W hW hh E hE hE' hE'' ι u' H f v b hB h' hT hF l hl hL
  have hC:0<u x:= mul_pos hs (P.threshold_pos.trans_le hb); have hf : 0< t x:= by unfold t; positivity
  have hz:0< p' x:=Real.rpow_pos_of_pos hx _; have hd:0<d' x:=Real.rpow_pos_of_pos hx _
  have hℓ : 0≤j:=Nat.zero_le _
  have hΩ : ‖W‖< p' x:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_pos (by norm_num) hd).le) hW
  let Q (k:ℝ):=actual (k • W)
  have he'' := sunnySoon p (w x) hp W (mul_le_mul_of_nonneg_left hΩ.le (Uniform.shade_pos G).le) ((le_abs_self _).trans hw) hh (by
    change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hx.le]; exact hZ.2)
  let Z:= leftDerivs H l (actual W)
  obtain ⟨K,hK,hvπ⟩:=exists_dual_vector'' ℝ Z
  have hz':‖Z‖ = ‖leftDerivs (K ∘ H) l (Q 1)‖:=by unfold Q; rw [one_smul,Push.Local.left_linear K l h' hl]; change _=‖K Z‖; rw [show K Z=‖Z‖ from hvπ,Real.norm_of_nonneg (norm_nonneg _)]
  change ‖Z‖ ≤ _; rw [hz']
  have h0:Push.Local.Chart P.order (K ∘ H) (Q 1):=by unfold Q; rw [one_smul]; exact K.contDiff.contDiffAt.comp 0 h'
  have h1:Push.Local.Chart 0 (leftDerivs (K ∘ H) l) (Q 1) := Next.Foundations.leftDerivs_chart _ _ (h0.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl)) -- edit
  have hY := (Push.Local.chart_comp h1 (fun i=> radiator 1 W i)).continuousAt.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto hY
  filter_upwards [he'', self_mem_nhdsWithin (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with i hi hk hp'
  let x':=i • W; have hk: ‖x'‖≤ ‖W‖:= by rw [show x'=i • W from rfl,norm_smul,Real.norm_of_nonneg hp']; exact mul_le_of_le_one_left (norm_nonneg _) (show i≤1 from le_of_lt hk)
  have hH:= (hF x' (lt_of_le_of_lt (add_le_add hk le_rfl) hW) hi).report K hK; rw [one_mul] at hH
  have hp:= hires (x:=x') hS (fun a hh=>hQ a (hh.trans hx'.le)) hz (hk.trans hΩ.le) (show Brush j v (eaves G L x)⁻¹ ((K ∘ f) ∘ actual) x' from hH) (show j.factorial*J*((1+r)* t x)≤ p' x from le_of_lt (by rw [one_mul] at he'; exact he')) ((le_abs_self _).trans hv)
    (show Sailor G P.threshold (u x) j from ⟨fun c a hv=> he c _ (P.threshold_pos.trans_le hb).le a (hv.trans hb)⟩) hC hf
    (show (j:ℝ)*(u x) ≤ t x from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC.le)
  let V:= K ∘ (fun w=>∑' k,u' k w); change ‖leftDerivs (K ∘ H) l (Q i)‖ ≤ _; have he:= oreB hB K hK _ hi
  have hR: K ∘ H=ᶠ[𝓝 (Q i)] (K∘ f)-V:=by filter_upwards [(Boulevard.sky P).mem_nhds hi] with a He; change K (H a)= _; rw [hT a He]; exact map_sub ..
  rw [(UVNext.PricedKernels.left_congr hR l).self_of_nhds, VerifiedReset.left_sub hp.1 (show Push.Local.Chart j V (Q i) from hP ▸ he.1) (hl.trans_eq hP)]; exact (norm_sub_le ..).trans (add_le_add (hp.2 _ (hl.trans_eq hP) hL) (he.2 _ hl hL))
end YM.PhysicalNext.Repeat.Boulevard.QG
#print axioms YM.PhysicalNext.Repeat.Boulevard.QG.vision
