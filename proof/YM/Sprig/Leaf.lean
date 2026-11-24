import YM.Sprig.Stuck
/-! Matrix bounds from authenticated probes.C_H independent of Pane; the motion calculus here only for Euclidean deriv. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
namespace Compass
variable (A:Compass C D)
variable (φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
variable (K:DiscP P A φ V Q) (L:Vale.Laurel d)(J:Vale.Landing P.sym L) (B:Inn P A J)
variable (u:Q.W)(p:Fin n)(x:Points n)(a:Axis)
open Function Set Finset Metric
noncomputable def bright (w:ℝ)(a:Axis):Q.W→ₗ[ℂ]Q.W:= (w:ℂ) • Q.arc a
local notation "TQ"=> Q.total
noncomputable abbrev blast (w:ℝ)(v:Fin n→Q.W)(y:Points n):= Q.total n (w • y) v
variable (v:Fin n→ Q.W)
local notation "Ba" => blast Q A.r
include hQ
lemma vital (u:Points n)(hu:u∈conf n)(w:ℝ)(hw:0<w): w • u∈ conf n :=by intro i j he; change w • u i=w • u j at he; exact hu (smul_right_injective E4 hw.ne' he)
omit hQ
local instance choir (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
include hQ
set_option maxHeartbeats 570000
lemma lifeX (u:Points n)(hu:u∈conf n):ContDiffAt ℝ ∞ (blast Q A.r v) u:=by
     let R :Points n→L[ℝ] Points n:= A.r • ContinuousLinearMap.id _ _; exact ((hQ.h.smooth n v).contDiffAt ((conf_open n).mem_nhds (vital P φ Q hQ u hu A.r A.realH))).comp u R.contDiff.contDiffAt
lemma blasted (hx:x∈conf n):YM.Analysis.D (Points.direction p a) (blast Q A.r v) x= blast Q A.r (update v p (bright Q A.r a (v p))) x:=by
     let w:=A.r; let R:Points n→L[ℝ]Points n:= w • ContinuousLinearMap.id _ _; let S(u:Points n):= Q.total n u v
     have hp:R x∈ conf n:= vital P φ Q hQ x hx A.r A.realH
     have h:= ((hQ.h.smooth n v).differentiableOn (by simp)).differentiableAt ((conf_open n).mem_nhds hp)
     change fderiv ℝ (S ∘R) x _= _
     rw [fderiv_comp x h R.differentiableAt,R.fderiv]; change fderiv ℝ S (R x) (w • Points.direction p a)=TQ n (R x) (update v p ((w:ℂ) • Q.arc a (v p)))
     rw [map_smul,(TQ n (R x)).map_update_smul]; exact congr_arg (fun z:ℂ=> (w:ℂ) • z) (hQ.h.derivatives _ _ hp v p a)
-- geometry detector intervals.
omit hQ
noncomputable def scout (t:ℝ):= J.a+t • basis a
local notation "Y"=> scout P L J a
local notation "ℓ"=> J.l/2
lemma rocks (t:ℝ)(h:t ∈ Set.uIcc 0 (J.l/2)) : scout P L J a t ∈ ball J.a J.l:=by
      rw [uIcc_of_le (half_pos J.breadth).le] at h; rw [Metric.mem_ball, dist_eq_norm]; unfold scout; rw [add_sub_cancel_left,norm_smul,basis_norm,mul_one,Real.norm_of_nonneg h.1]; exact h.2.trans_lt (half_lt_self J.breadth)
lemma heads(h:ℝ) : points ![0,scout P L J a h]= points ![0,scout P L J a 0]+h • Points.direction (1:Fin 2) a:=by apply PiLp.ext; intro i; unfold scout; fin_cases i<;>simp [Points.direction]
include B hQ K
noncomputable abbrev saver (i:Stokes d):ℝ→ℂ:=fun s=> tap A Q (oppositeX P V Q L i) (scout P L J a s) u
#print saver -- binder args
-- v arc world motion ray.
lemma touchL (x:E4)(h:x∈ball J.a J.l): points (![0,x])∈conf 2:=noCol _ _ _ (J.pose x (ball_subset_closedBall h)).1 (by linarith only [J.far])
variable {x₀:Q.W}
lemma flying (t:ℝ)(he:t∈ uIcc 0 (J.l/2)):ContDiffAt ℝ ∞ (fun s=> glimpseT A Q x₀ u (scout P L J a s)) t:=by
      let f(s:ℝ):=points ![0,(Y s)]; exact (lifeX P A φ Q hQ (![x₀,u]) (f t) (touchL P A φ V Q hQ K L J B ((Y) t) (rocks P L J a t he))).comp t (show ContDiffAt ℝ ∞ f t from by rw[show f=(fun t=> f 0+t • Points.direction (1:Fin 2) a) from funext (fun i=> heads P L J a i)]; fun_prop) -- `fun_prop` ContDiffAt?
local notation "Φ"=> glimpseT A Q x₀ u
set_option maxHeartbeats 700000
lemma skyArc (t:ℝ)(he:t∈ uIcc 0 (J.l/2)): HasDerivAt (fun s=> glimpseT A Q x₀ u (scout P L J a s)) (glimpseT A Q x₀ (bright Q A.r a u) ((Y) t)) t:=by
      let F (t:ℝ):=points (![0,(Y t)]); have hx(h:ℝ):F h=F 0+h • Points.direction (1:Fin 2) a:=heads P L J a h
      have hp:HasDerivAt F (Points.direction (1:Fin 2) a) t:=by
             let b:= Points.direction (1:Fin 2) a; have hD : HasDerivAt (fun h:ℝ=> F 0+h • b) ((1:ℝ) • b) t:= ((hasDerivAt_id' t).smul_const b).const_add (F 0); rw[← funext hx] at hD; simpa only[one_smul] using hD
      let g:=blast Q A.r (![x₀,u]); have ht:F t∈conf 2:= touchL P A φ V Q hQ K L J B ((Y) t) (rocks P L J a t he); have hv := (lifeX P A φ Q hQ (![x₀,u]) (F t) ht).differentiableAt (by simp); have hz:glimpseT A Q x₀ (bright Q A.r a u) ((Y) t)= fderiv ℝ g (F t) (Points.direction (1:Fin 2) a):=by
             rw [show fderiv ℝ g (F t) (Points.direction (1:Fin 2) a)=_ from blasted P A φ Q hQ _ (F t) a (![x₀,u]) ht]; unfold glimpseT blast; apply congr_arg (TQ 2 _); funext i; fin_cases i<;>simp
      rw[hz]; exact hv.hasFDerivAt.comp_hasDerivAt t hp
noncomputable def moonGate (i j:Stokes d):= ((J.l/2:ℝ)⁻¹ :ℝ) • ∫ t in (0:ℝ)..(J.l/2), curveP P A V Q L ((scout P L J a) t) i j
#print moonGate
lemma integrated (i:Stokes d):IntervalIntegrable (fun s=> tap A Q (oppositeX P V Q L i) ((Y) s) u) volume 0 (J.l/2):=by
      simp_rw[pours]; exact (show ContinuousOn _ _ from (fun t ht=>(flying P A φ V Q hQ K L J B u a (x₀:=oppositeX P V Q L i) t ht).continuousAt.continuousWithinAt)).intervalIntegrable
lemma iturn(i j:Stokes d) : IntervalIntegrable (fun s=> curveP P A V Q L (scout P L J a s) i j) volume 0 (J.l/2):=by
      simp only[curveP]; simp_rw[←pours]; exact integrated P A φ V Q hQ K L J B _ a i
lemma glowing: nearG P.sym L J.ε (moonGate P A V Q L J a):=by
     let f:=moonGate P A V Q L J a; intro i j; let F(t):=curveP P A V Q L (scout P L J a t) i j; let U:=ΦGram P.sym L (basis timeAxis) i j; let r:=ℓ; have hr:0 < r:= half_pos J.breadth
     change ‖(f i j)-U‖ ≤ J.ε; rw [show f i j - U=r⁻¹ • ∫ t in (0:ℝ)..r, F t-U from ?_]; swap
     · change _ = _; rw [intervalIntegral.integral_sub (iturn P A φ V Q hQ K L J B a i j) intervalIntegrable_const,intervalIntegral.integral_const,smul_sub,sub_zero,inv_smul_smul₀ hr.ne']; rfl
     rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,inv_mul_eq_div,div_le_iff₀ hr]; have h:= intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun s=>F s-U) (C:=J.ε) (a:= (0:ℝ)) (b:=r) (fun t ht=>(mediator P A φ V Q K L J B (Y t) (rocks P L J a t (Set.uIoc_subset_uIcc ht))) i j)
     rw [sub_zero,abs_of_pos hr] at h; exact h
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.skyArc
#print axioms YM.Intag.Sprig.Compass.glowing
