import YM.Patria.Sine
/-! Pullback to full-lattice tapered frames. Uniform sums on small volume neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a b θ v A D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open MultiNext.SignedSource PhysicalNext.JointLoad Lyre Metric
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised Display Beacon
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable (H:TaperHol)(b: Cover)(J:Labels.Jet su)
def stature (g:ℝ): Lat.Fields c 6→L[ℝ]SpinPol d:= (((endor (d:=d) g).comp (adapter (glow (c:=c) H.T b 1) (glow (c:=c) H.T b 1))).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
lemma endured (x:SpinPol d):ContDiff ℝ (d:ℕ∞ω) (fun v:ℝ=>endor v x):=by
    conv=> arg 3; ext v; rw [← write x,map_sum]
    simp_rw [map_smul,pieces]
    exact ContDiff.sum fun i _=> ContDiff.const_smul _ ((Complex.ofRealCLM.contDiff.pow _).smul contDiff_const)
lemma knownD : ContDiff ℝ (d:ℕ∞ω) (stature H b (c:=c) (d:=d)):=by
    let M := Module.finBasis ℝ G₀; let f(v:ℝ):= stature H b (c:=c) (d:=d) v; let L:= (adapter (glow H.T b 1) (glow H.T b 1): G₀→ₐ[ℂ] SpinPol d); let u(i):= (M.coord i).toContinuousLinearMap
    change ContDiff _ _ f; have h(i): ContDiff ℝ (d:ℕ∞ω) (fun v=> f v (M i)):= endured (L (M i)); let p(i):SpinPol d →L[ℝ] G₀ →L[ℝ] SpinPol d:= ContinuousLinearMap.smulRightL _ _ _ (u i)
    rw [show f=(fun v=>∑ i,p i (f v (M i))) from ?_]; exact ContDiff.sum fun i _=> (p i).contDiff.comp (h i)
    funext v; ext1 x; rw [ContinuousLinearMap.sum_apply]; change f v x=∑ i, u i x • f v (M i); simp_rw [← map_smul]; rw [← map_sum]; exact congr_arg (f v) (M.sum_repr _).symm
-- budget upper local even non-bump
lemma founded {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] {u : ℝ→ E} (hu:ContDiffAt ℝ (d:ℕ∞ω) u 0) : ∃ C:ℝ,1≤C ∧∀ᶠ x in 𝓝 (0:ℝ), ∀ i≤d, ‖iteratedFDeriv ℝ i u x‖ ≤ C:=by
   let W (i:Fin (d+1)):= ‖iteratedFDeriv ℝ i.val u 0‖+1; have hp: ∀ i:Fin (d+1),∀ᶠ x in 𝓝 (0:ℝ), ‖iteratedFDeriv ℝ i.val u x‖≤ W i :=fun i => ((hu.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.isLt))).norm.eventually (gt_mem_nhds (by unfold W; linarith))).mono fun _ h=>le_of_lt h
   have h(i):0≤W i:=by unfold W; positivity
   refine ⟨1+∑ i,W i,le_add_of_nonneg_right (sum_nonneg fun i _=>h i),?_⟩; filter_upwards [eventually_all.mpr hp] with x hx i hi; refine (hx ⟨i,by omega⟩).trans ((single_le_sum (fun k (_ :k∈Finset.univ)=>h k) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))
abbrev arches (v:ℝ):X₀:= lamp H b (d:=d) (scaledD d J v)
lemma arched : arches H b J (d:=d) (c:=c) 0=0 ∧ ContDiffAt ℝ (d:ℕ∞ω) (arches H b J (c:=c) (d:=d)) 0 ∧ current (c:=c) H b d J =ᶠ[𝓝 (0:ℝ)] increment 1 ∘ arches H b J (d:=d):=by
    have hx:= scaled_smooth d J
    refine ⟨?_,((show ContDiffAt ℝ (d:ℕ∞ω) (lamp H b (c:=c) (d:=d)) (scaledD d J 0) from ?_).comp _ hx),?_⟩
    · unfold arches; rw [scaled_zero]; exact at_dark H b
    · rw [scaled_zero]; exact (fluent ..).contDiffAt.of_le le_top
    have hn:= hx.continuousAt.tendsto; rw [scaled_zero] at hn; exact (at_east H b (c:=c) (d:=d)).comp_tendsto hn
lemma centered : Tendsto (Beacon.current (c:=c) H b d J) (𝓝 0) (𝓝 1):=by
    obtain ⟨hp,hc,hg⟩:= arched H b J (d:=d) (c:=c); let f:=arches H b J (d:=d) (c:=c)
    have h:Tendsto (increment (1:V₀)) (𝓝 0) (𝓝 1):= by
       have h:Continuous (increment (1:V₀)):= by unfold increment; fun_prop
       simpa [increment] using h.tendsto 0
    refine (h.comp ?_).congr' hg.symm; exact (hp ▸ hc.continuousAt.tendsto)
end YM.Massive.Patria
#print axioms YM.Massive.Patria.centered
#print axioms YM.Massive.Patria.knownD
