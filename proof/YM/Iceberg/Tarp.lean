import YM.Iceberg.Grey
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
variable (V:Face→K.W)(hv:Tense T V)(E:Canopy P φ K) (X:Lanterns T E)
open Lanterns Tawny Tawny.Cast Perla Carnal Drill
open Work.A05 Heron Table
open Maxwell.Free (fromCenter exportFlux shell_cost)
variable {d:ℕ}(x:Points 2)(hx:x∈conf _)(g:Ortho.Skew){χ:E4→ℝ}(hw:Physics.Window x χ)
variable (k p q:ℕ)(P':Label d)(Q':Label d)(a b:Axis)
noncomputable def Storm (k:ℕ)(z:E4) (a b:Axis): Label 8→ₗ[ℂ]ℂ:= weight χ a (arm x g b) z • (headG (![cost T E X k P',cost T E X k Q']) ((E.B k).r • Points.cons z x) ∘ₗ bullet E X 8 k)
noncomputable def ghostQ (z:E4) (a b:Axis): Label 8→ₗ[ℂ]ℂ:= weight χ a (arm x g b) z • (trioL z x (![P'.val,Q'.val]) ∘ₗ (labels 8).subtype)
#check Storm
#check ghostQ
variable (t:Label 8)
noncomputable abbrev viva (t:Label 8)(p q:Label d): (i:Fin 3)→ Label (hill d i):= Fin.cons t (![p,q])
include hw hx
set_option quotPrecheck false
local notation "SF" k:arg y:arg=> Storm E X x g P' Q' (χ:=χ) k y a b t
local notation "SG" k:arg => ghostQ x g P' Q' (χ:=χ) k a b t
local notation "massW" y:arg=> weight χ a (arm x g b) y
lemma tarH (z:E4): SF k z = (weight χ a (arm x g b) z) * (LoomZ T E K.total (hill d) (viva t P' Q') X k (Points.cons z x)):= by
    change _ * headG _ _ _=_; rw[heads]; congr 1; unfold LoomZ; apply congr_arg; funext i; fin_cases i<;>rfl
lemma tarG (z:E4): SG z = (weight χ a (arm x g b) z) * UV.Free.wick (hill d) (Points.cons z x) (viva t P' Q'):=by
     change (Work.A05.weight χ a (arm x g b) z) * trioL z x (![P'.val,Q'.val]) t.val=_; rw[show trioL _ _ _ _=_ from (?_ : trioL z x (![P'.val,Q'.val]) t.val=triangle z x t.val (![P'.val,Q'.val]))]
     swap; · change UV.Free.moment _ _ (update _ (0:Fin 3) _)=_; exact congr_arg (UV.Free.moment _ _) (Fin.update_cons_zero ..) -- fix indent
     refine congr_arg (fun f:ℂ=> Work.A05.weight χ a (arm x g b) z * f) ?_; unfold triangle; apply congr_arg (moment _ _); funext i; fin_cases i<;>rfl
lemma tarbG: Integrable fun z:E4=> ghostQ x g P' Q' (χ:=χ) z a b t:=by
    simp_rw[tarG x hx g hw] -- order
    simp_rw [Work.A05.weight,Complex.ofReal_mul,mul_assoc]; change Integrable fun z:E4=> Maxwell.grad a χ z • ((arm x g b z:ℂ)*_); apply shell_cost hw.1 hw.2.1; intro y hy
    have hW:= UV.Free.Sip.smoothC (torchD x hx y χ hw hy) (hill d) (fun j=>(viva t P' Q' j).val)
    exact (Complex.continuous_ofReal.comp (arm_continuous x g b)).continuousAt.mul (hW.continuousAt.comp (x:=y) (f:=fun y:E4=>Points.cons y x) (show Continuous (fun y:E4=>Points.cons y x) from (by unfold Points.cons points; fun_prop)).continuousAt)
lemma aliveS (Y:RawTensor 1 8) : plumes x χ g Y.val P'.val Q'.val= -∑ a:Axis,∑ b:Axis,∫ z:E4,ghostQ x g P' Q' (χ:=χ) z a b (Y.val (a,b)):=by
     unfold plumes Maxwell.Free.exportFlux; congr 1; apply Finset.sum_congr rfl; intro i _; have h(b:Axis):=tarbG x hx g hw P' Q' i b (Y.val (i,b)) -- fix name
     rw [← integral_finsetSum Finset.univ (fun b _=>h b)]; apply integral_congr_ae; refine Eventually.of_forall fun z=>?_ ; dsimp only; unfold actS; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; change ((Maxwell.grad i χ z:ℝ) • ((arm x g j z) • (_:ℂ)):ℂ)= (weight χ i (arm x g j) z)*_; rw[smul_smul]; rfl
include hHQ
lemma tarbS: Integrable (fun z:E4=> Storm E X x g P' Q' (χ:=χ) k z a b t):=by
    simp_rw[tarH E X x hx g hw]; simp_rw [Work.A05.weight,Complex.ofReal_mul,mul_assoc]; change Integrable fun z:E4=> Maxwell.grad a χ z • ((arm x g b z:ℂ)*_); apply shell_cost hw.1 hw.2.1; intro y hy
    let r:=(E.B k).r; let p0(i:Fin 3):= cost T E X k (viva t P' Q' i); have ht:r • Points.cons y x∈ conf 3:= Compass.vital P φ K hHQ _ (torchD x hx y χ hw hy) r (E.B k).realH; have hp:Continuous (fun z:E4=>r • Points.cons z x):=by unfold Points.cons points; fun_prop
    exact (Complex.continuous_ofReal.comp (arm_continuous x g b)).continuousAt.mul (((hHQ.h.smooth 3 p0).continuousOn.continuousAt ((conf_open _).mem_nhds ht)).comp (f:=fun z:E4=>r • Points.cons z x) hp.continuousAt)
-- integral cost by Intag.Sprig.
lemma cup : Tendsto (fun k=> ∫ z:E4, Storm E X x g P' Q' (χ:=χ) k z a b t) atTop (𝓝 (∫ z:E4, ghostQ x g P' Q' (χ:=χ) z a b t)):=by
    apply Metric.tendsto_nhds.mpr; intro ε he
    let u:=(tsupport (fderiv ℝ χ)); let W:=(weight χ a (arm x g b)); have h(B:E4)(hp:W B≠0): B∈u:=subset_closure (show fderiv ℝ χ B≠0 from fun h=>hp (by simp [W,Work.A05.weight,D,h]))
    let D'(z:E4):= Points.cons z x; have hC:Continuous D':=by unfold D' Points.cons points; fun_prop
    let Y:=D' '' u; have hY:IsCompact Y:= (hw.2.1.fderiv (𝕜:=ℝ)).image hC  -- implicit ℝ
    have hK:Y ⊆ conf 3:=by rintro z ⟨y,hy,rfl⟩; exact Work.A01.window_separated hx hw hy
    have hWV:Integrable fun z:E4=>‖W z‖:= (integrable_weight hw.1 hw.2.1 _ (arm_continuous x g b)).norm
    let c:= ∫ z:E4,‖W z‖; have hc:0≤c:=integral_nonneg (fun _=>norm_nonneg _); let ζ:=ε/(c+1); have hz:0<ζ:=by unfold ζ; positivity
    filter_upwards [genuine T E hHQ X _ (hill d) (viva t P' Q') (Canopy.assay E) (Canopy.reliable hHQ) (Canopy.measureE E) 0 Y hY hK 0 ζ hz] with k hk
    rw [dist_eq_norm, ←integral_sub (tarbS hHQ E X x hx g hw k ..) (tarbG x hx g hw ..)] -- explicit
    apply lt_of_le_of_lt (norm_integral_le_of_norm_le (hWV.mul_const ζ) ?_) ?_
    · refine Eventually.of_forall fun y=>?_ ; rw [tarH E X x hx g hw,tarG x hx g hw]; by_cases hh:W y=0; · rw [show weight χ a (arm x g b) y=0 from hh]; simp[hh]
      specialize hk _ ⟨y,h y hh,rfl⟩; simp only [Zenith,pow_zero,norm_iteratedFDeriv_zero,one_mul] at hk; rw [← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    rw[integral_mul_const]; refine (mul_lt_mul_of_pos_right (lt_add_one c) hz).trans_eq ?_; unfold ζ; rw[mul_comm,div_mul_cancel₀ _ (by linarith)]
end YM.Iceberg
#print axioms YM.Iceberg.tarbS
#print axioms YM.Iceberg.aliveS
#print axioms YM.Iceberg.cup
