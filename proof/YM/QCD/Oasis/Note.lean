import YM.QCD.Oasis.Silky
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 120000
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Input Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure
open ConnectedActivityE6 Blaze Brush Poll Coat
open PhysicalNext.Repeat Lapis Lantern Sienna Fare Tidings
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {n j k : ℕ}{σ C U D b W M w u v d a : ℝ}
open Cove Golden Shield
variable {ι:Type}[Fintype ι][DecidableEq ι]
local notation "R"=> Poll.Body ι
variable {φ ψ:E×Poll.Body ι→ℝ}{ρ:E→Poll.Body ι}{A:E→ Matrix ι ι ℝ}
variable {c:Side}{N:ℕ} (h:Golf φ ψ ρ A k D U U M)
local notation "X"=>EvenA c N
set_option quotPrecheck false
local notation "Δ"=>closedBall (0:Poll.Body ι) D
local notation "ℳ"=>sweep (A 0)⁻¹
-- scaled moment asks on actual (b,x) argument. parity unscaled all-field algebra, continuity
structure Cello (T:Poll.Body ι→ℝ×E→EvenA c N)(K:Poll.Body ι→EvenA c N)(v₁ v₂ D U:ℝ)(j:ℕ):Prop where
 measP : Continuous K
 oddR z : K (-z)=-K z
 small z : ‖z‖≤ D→ ‖K z‖≤ v₁
 faces x : ContinuousOn (fun z=>T z x) (closedBall 0 D) -- global ok draw uses no derivative.
 plays z x :T z x=T (-z) (-x.1,x.2)
 drone z x:T z (0,x)=0 -- exact
 dawn x z:‖x‖<1 → ‖z‖≤ D→ Brush j (U^2*v₂) 1 (fun i:ℝ×E=> T z (U • i)-(U*i.1) • K z) x
lemma moneyL [NormedAddCommGroup F] [NormedSpace ℝ F] (K:Poll.Body ι→ F) (z:R)(hz: ‖K z‖≤ v)(h:0≤ U) (x:ℝ×E)(hx : ‖x‖≤1): Brush k (U*v) 1 (fun i:ℝ×E=>(U*i.1) • K z) x:=by
    let L: (ℝ×E)→L[ℝ] F:= (ContinuousLinearMap.fst ℝ ℝ E).smulRight (U • K z); have hv i:L i=(U*i.1) • K z:=by change i.1 • (U • K z)=_; rw [smul_comm, ←mul_smul]
    have ht: ‖L‖≤ U*v:= ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg h ((norm_nonneg _).trans hz)) fun i=> by
       rw [hv,norm_smul,norm_mul,Real.norm_of_nonneg h]; refine (mul_le_mul (mul_le_mul_of_nonneg_left (show ‖i.1‖ ≤ ‖i‖ from le_max_left ..) h) hz (norm_nonneg _) (mul_nonneg h (norm_nonneg _))).trans_eq ?_; ring -- ℝ×?
    apply (Brush.linearB L ((L.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans ht)) (by rwa [mul_one]) zero_le_one).shimmy -- arguments verify
    exact Eventually.of_forall fun i=>(hv i).symm
lemma recommendsV (M : Matrix ι ι ℝ) [NormedAddCommGroup F] [NormedSpace ℝ F] (h:M.PosDef)(f:Poll.Body ι→F) : (∫ x, f x ∂Poll.sweep M) = ∫ x,lens₀ M x • f x:=by
   rw [magnifies M h]; have ht : Measurable (fun x=> lens₀ M x) := bulbB (S:=fun _ : Poll.Body ι=>M) (fun i j=> measurable_const) (z:=id) measurable_id
   rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ M x)) from ENNReal.measurable_ofReal.comp ht) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]; exact integral_congr_ae (ae_of_all _ (fun y=> by dsimp only; rw [ENNReal.toReal_ofReal (fullFuel M y).le]))
lemma hush (K:Poll.Body ι→X) (hk:∀ z,K (-z)=-K z)(M:Matrix ι ι ℝ)(hp:M.PosDef): (∫ z,(Δ).indicator K z ∂sweep M)=0:=by
    rw [recommendsV M hp]; let g z:=lens₀ M z • (Δ).indicator K z; let I:=∫ z,g z; have h:I=-I:=by
      unfold I; nth_rw 1 [← integral_neg_eq_self g]; rw [← integral_neg]; apply integral_congr_ae; filter_upwards with z; unfold g; rw [symL]; by_cases he:z∈Δ
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem (by simpa only [mem_closedBall_zero_iff,norm_neg] using he), hk,smul_neg]
      rw [Set.indicator_of_notMem he,Set.indicator_of_notMem (by simpa only [mem_closedBall_zero_iff,norm_neg] using he),smul_zero,neg_zero]
    have hz : (2:ℝ) • I=0:=by rw [show (2:ℝ)=1+1 by norm_num,add_smul,one_smul]; nth_rw 2 [h]; rw [add_neg_cancel]
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num) -- indent fix
include h
variable {K: Poll.Body ι→ EvenA c N} {T:Poll.Body ι→ℝ×E→EvenA c N}(hz:Cello T K u v D U k)
local notation "g"=>ballots φ ψ ρ A D
-- **ball** location always native
omit h in
def humV (φ ψ:E×Poll.Body ι→ℝ)(ρ:E→Poll.Body ι)(A:E→ Matrix ι ι ℝ)(T:R→ℝ×E→EvenA c N)(D:ℝ)(x:ℝ×E):=∫z, (ballots φ ψ ρ A D x z) • T z x ∂sweep (A 0)⁻¹
local notation "V"=>humV φ ψ ρ A T D
variable (hj:1≤ k)(hM: Lantern.fee k M D *U≤1)(hs:∀ i∈ Set.Icc (-1:ℝ) 1, Brush k a 1 Real.exp i)
include hz
lemma balanced (x:ℝ×E): V (-x.1,x.2)= V x:=by
    have he := (h.gram 0 (show ‖(0:E)‖ < U from norm_zero.trans_lt h.pos)).1.inv; rw [humV,humV,recommendsV _ he,recommendsV _ he]; nth_rw 1 [← integral_neg_eq_self]; apply integral_congr_ae; filter_upwards with z
    rw [symL,← hz.plays]; unfold ballots; by_cases ht:z∈ Δ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (by simpa only [mem_closedBall_zero_iff,norm_neg] using ht),oppositeC]
    rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem (by simpa only [mem_closedBall_zero_iff,norm_neg] using ht)]
include hj hM hs
def mast (u v M D a:ℝ)(j:ℕ):ℝ:=v+(clump j (Lantern.fee j M D) a+1)*(v+u)*(1+(1+1))^j
set_option maxHeartbeats 800000 in
lemma wakenV (x:ℝ×E)(hx:‖x‖<1): Brush k (U^2*mast u v M D a k) 1 (fun i=> V (U • i)) x:=by
   let W (i:ℝ×E) z:= g (U • i) z • T z (U • i)-(Δ).indicator (fun (z:R)=>(U*i.1) • K z) z
   let J:= U^2*mast u v M D a k; let Q:=(A 0)⁻¹; let Y:=ℳ
   have hq (i:ℝ×E)(hi:‖i‖<1)(z:R)(hv:‖z‖ ≤ D):= stallR h hj hM hs hi hv; have hh : 0 < U:=h.pos
   have hp y (hy:‖(y:ℝ×E)‖<1) z (ht:z∈Δ): Brush k J 1 (fun i=>W i z) y:=by
     have hs:= mem_closedBall_zero_iff.mp ht; have hv:= hz.dawn y z hy hs; have hc:= moneyL K z (hz.small z hs) h.pos.le y hy.le (k:=k)
     have ht': Brush k (U^2*v+U*u) 1 (fun i=> T z (U • i)) y := (hv.gathering hc).shimmy (Eventually.of_forall fun i=> (sub_add_cancel ..).symm)
     refine ((hv.gathering ((Golden.brushR (hq _ hy _ hs) ht').trim)).climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=> ?_)
     · unfold J mast; let a':=clump k (Lantern.fee k M D) a +1; have h':0≤ U^2*v:=hv.nonneg; have hU:0 ≤ a'*U:=(hq _ hy _ hs).nonneg
       have hc:U^2*v ≤ U*v:=by nlinarith [h.small, show 0≤v from nonneg_of_mul_nonneg_right h' (by positivity)] -- lemma variant
       calc _ ≤U^2*v+(a'*U)*(U*v+U*u)*(1+(1+1))^k:=add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_left hc _) hU) (by positivity))
            _ = _ :=by unfold a'; ring
     dsimp only [W,ballots]; rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]; rw [sub_smul,one_smul]; abel
   have hm:0 ≤ J:= (hp x hx 0 (mem_closedBall_self h.off)).nonneg
   have hh y (hy:‖(y:ℝ×E)‖<1) : (∀ z, Brush k J 1 (fun i=> W i z) y) ∧ Measurable (W y) := by
       constructor
       · intro z; by_cases he:z∈ Δ
         · exact hp y hy z he
         exact ((Brush.certified (k:=k) (x:=y) zero_le_one (0:X)).climb (norm_zero.trans_le hm) le_rfl).shimmy (Eventually.of_forall fun i=>by change W i z=0; unfold W ballots; rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he,zero_smul,sub_zero])
       apply measurable_of_restrict_of_restrict_compl (s:=Δ) measurableSet_closedBall
       · apply Continuous.measurable; let f(z):=Real.exp (grace φ ψ ρ A z (U • y)) • T z (U • y)-(U*y.1) • K z; have hx: ‖U • y‖ < U := by rw [norm_smul,Real.norm_of_nonneg h.pos.le]; exact mul_lt_of_lt_one_right h.pos hy
         have he:= max_lt_iff.mp (show max _ _ < U from hx); have hc:ContinuousOn f (Δ):= ((Real.continuous_exp.comp_continuousOn (gallon D h he.2 he.1)).smul (hz.faces _)).sub ((hz.measP.const_smul _).continuousOn); rw [show (Δ).restrict (W y)=(Δ).restrict f from funext fun z=>by dsimp only [Set.restrict,W,ballots]; rw [Set.indicator_of_mem z.2,Set.indicator_of_mem z.2]]; exact continuousOn_iff_continuous_restrict.mp hc
       rw [show (Δ)ᶜ.restrict (W y)=(fun _=>0) from funext fun z=>by dsimp only [Set.restrict,W,ballots]; rw [Set.indicator_of_notMem z.2,Set.indicator_of_notMem z.2,zero_smul,sub_zero]]; exact measurable_const
   have hO:∀ᶠ i in 𝓝 x, ‖i‖<1:=continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
   obtain ⟨hH,hY⟩:= meritX W Y ⟨fun _=> J,integrable_const _, hO.mono fun i hi=>(hh _ hi).1⟩ (hO.mono fun i hi=> (hh _ hi).2)
   apply (hH.buds (fun _=> J) (integrable_const _) zero_le_one (by simp [Y,J]) (ae_of_all _ (hh x hx).1)).shimmy
   filter_upwards [hY] with i hi
   let S':=closedBall (0:R) D; let k z:= (U*i.1) • (S').indicator K z
   have hz' z: k z= (Δ).indicator (fun z=> (U*i.1) • K z) z:= by
     unfold k S'; by_cases he:z∈ Δ
     · rw [Set.indicator_of_mem he,Set.indicator_of_mem he]
     rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he,smul_zero]
   have hk: Integrable ((Δ).indicator K) Y:= (integrable_indicator_iff measurableSet_closedBall).mpr (hz.measP.continuousOn.integrableOn_compact (isCompact_closedBall ..))
   have hK: Integrable k Y:= hk.smul _
   change (∫ z, g (U • i) z • _ ∂Y)=∫ z,W i z ∂Y
   rw [show (fun z=>g (U • i) z • T z (U • i))=(fun z=> W i z+k z) from funext fun z=> by rw [hz']; exact (sub_add_cancel _ _).symm, integral_add hi hK]; unfold k Y; rw [integral_smul,hush _ hz.oddR _ ((h.gram 0 ((norm_zero.trans_lt h.pos))).1.inv),smul_zero,add_zero]
end YM.QCD.Oasis
