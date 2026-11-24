import YM.MassiveBridge.Contour
import YM.MassiveBridge.SpinAction
import YM.Work.C09
import YM.Work.C07
/-!
# Infinitesimal coordinate rotations give tested boost identities

Adapted from YM/Work/C07/{Euclid,Integrate,Continue}. Keep all fields including odd.
No swapping or assumption of Lorentz covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Rotate
open Set Filter Function Analysis MeasureTheory LineDeriv Mink Complex
open Boundary hiding Fields Surface Waves
open Work.C07 (orbit integral_orbit orbit_image foldE fold_smooth fold_derivative testField test_zero_off test_one test_imag analytic_integral incline_cont stretchY scaledTimes scaled_imag scaled_one scaled_strict_imag)
open Bid (inclined realTerm)
open Spinor
open MassiveTwoEstimates
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {Q:Massive.Sequence} {P:Calibration Q} {X:Massive.Fields} {S:X.Kernel}
variable {Y:Waves X} {n:ℕ}
private abbrev turning (a : SpaceAxis) := Ortho.plane timeAxis a.castSucc

-- lift a derivative that stays in a (closed) filtered level.
lemma level_derivative (d:ℕ) [FiniteDimensional ℂ (X.level d)] (f:ℝ → Wd X d) (x:ℝ) (z:X.W)
    (hz:HasDerivAt (fun t => (f t).val) z x) : ∃ y:Wd X d,y.val=z ∧ HasDerivAt f y x := by
  have he:=hz.tendsto_slope_zero
  have hc : IsClosed ((X.level d):Set X.W) := (X.level d).closed_of_finiteDimensional
  have h : z∈ X.level d:= hc.mem_of_tendsto he (Eventually.of_forall (fun i=> (X.level d).smul_of_tower_mem _ ((X.level d).sub_mem (f _).property (f _).property)))
  refine ⟨⟨z,h⟩,rfl,?_⟩; rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_subtype_rng]; exact he
lemma cover_cap (E:X.System P) (v:Fin n→X.W) : ∃ d:ℕ, ∃ f:Fin n→ Wd X d,v=(X.level d).subtype ∘ f := by
  classical
  choose m hm using fun i=> E.exhaustive (v i)
  let d:=Finset.univ.sup m
  exact ⟨d,fun i=>⟨v i,E.increases (Finset.le_sup (f:=m) (Finset.mem_univ i)) (hm i)⟩,rfl⟩
private def actionOnTuple {n : ℕ} (p : Points n) : M4 →L[ℝ] Points n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => points fun i => M4.move A (p i)
      map_add' := fun A B => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (A+B) (p i) =
          Matrix.toEuclideanLin A (p i) + Matrix.toEuclideanLin B (p i)
        rw [map_add]; rfl
      map_smul' := fun c A => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (c • A) (p i) = c • Matrix.toEuclideanLin A (p i)
        rw [map_smul]; rfl }

private lemma turnsTuple {n : ℕ} (x : Points n) (Ω : Ortho.Skew) :
    HasDerivAt (fun t : ℝ => Points.move (Ortho.oneParameter Ω t) x)
      (points fun i => M4.move Ω.val (x i)) 0 := by
  have hA : HasDerivAt (fun t => NormedSpace.exp (t • Ω.val)) Ω.val (0 : ℝ) := by
    simpa using! (hasDerivAt_exp_smul_const Ω.val (0 : ℝ))
  exact (actionOnTuple x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA

/-- Version of the finite basis expansion with constant rectangle used for continuity. -/
lemma continuous_cap_multilinear {n : ℕ} (d : ℕ) [FiniteDimensional ℂ (X.level d)]
    (P : MultilinearMap ℂ (fun _ : Fin n => (X.level d)) ℂ) : Continuous P := by
  classical
  let E (i : Fin n) := Module.finBasis ℂ ((X.level d))
  let c (i : Fin n) := LinearEquiv.toContinuousLinearEquiv (E i).equivFun
  have hw (w : ∀ i : Fin n, (X.level d)) :
      P w = ∑ v : ((i : Fin n) → Fin (Module.finrank ℂ ((X.level d)))),
        (∏ i, c i (w i) (v i)) • P (fun i => E i (v i)) := by
    rw [Multilabel.expansion E P w]
    change (∑ e ∈ Fintype.piFinset _, ((∏ i, (E i).repr (w i) (e i)) • (P _))) =
      ∑ e : ((i : Fin n) → Fin (Module.finrank ℂ ((X.level d)))),
        (∏ i, (E i).repr (w i) (e i)) • P (fun i => E i (e i))
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    obtain ⟨j,hj⟩ : ∃ j, (E j).repr (w j) (a j) = 0 := by simpa using ha
    have hz : ∏ i : Fin n, (E i).repr (w i) (a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hz, zero_smul]
  rw [funext hw]
  refine continuous_finsetSum _ fun v _ => ?_
  have h : Continuous fun w : (∀ i : Fin n, (X.level d)) => ∏ i, c i (w i) (v i) := by
    refine continuous_finsetProd _ fun i _ => ?_
    exact (continuous_apply (v i)).comp ((c i).continuous.comp (continuous_apply i))
  exact h.smul (continuous_const (y := P (fun i => E i (v i))))


private lemma rotate_labels (E:X.System P) (a:SpaceAxis) (x:Points n) (v : Fin n → X.W) :
    HasDerivAt (fun t : ℝ=> S n x (X.action (Spinor.Lift.daylight a (-t)) ∘ v))
      (-(∑ i, S n x (update v i (X.lie (turning a) (v i))))) 0:=by
  obtain ⟨d,w,H⟩:=cover_cap E v
  let P:=X.level d; let R:=Lift.daylight a
  haveI:=E.finite d
  let u(t:ℝ)(i:Fin n): Wd X d:= ⟨X.action (R (-t)) (w i).val, E.lift _ (w i).property _⟩
  have hf (i:Fin n):HasDerivAt (fun t=> (u t i).val) (-(X.lie (turning a) (w i).val)) 0:=by
    simpa [u,R,Function.comp_def] using
      ((E.infinitesimal (turning a) _ _ (Lift.way a)).scomp_of_eq (0:ℝ) (hasDerivAt_id' (0:ℝ)).neg (by simp)) -- tag p
  choose L hL hd using fun i=> level_derivative d (fun t=>u t i) 0 _ (hf i)
  have hh:= hasDerivAt_pi.mpr (show ∀ i:Fin n, HasDerivAt (fun t : ℝ=>u t i) (L i) 0 from hd)
  let U : MultilinearMap ℂ (fun _ : Fin n=>Wd X d) ℂ := (S _ x).compLinearMap (fun _=> P.subtype)
  let M : ContinuousMultilinearMap ℂ _ ℂ := ⟨U,continuous_cap_multilinear d U⟩
  let A:= M.restrictScalars ℝ
  have he := (A.hasFDerivAt (u 0)).comp_hasDerivAt 0 (show HasDerivAt u L 0 from hh)
  have hb : u 0=w:=by funext i; apply Subtype.ext; simp only [u,R,neg_zero,(Lift.way a).1,map_one]; rfl
  rw [hb,ContinuousMultilinearMap.linearDeriv_apply] at he
  subst v
  change HasDerivAt _ _ _ at he
  apply (show HasDerivAt (fun t=> U (u t)) (∑ i, U (update w i (L i))) 0 from he).congr_deriv
  have H (i:Fin n) : U (update w i (L i)) = -S n x (update (P.subtype ∘ w) i (X.lie (turning a) (w i).val)) := by
      unfold U; rw [MultilinearMap.compLinearMap_apply, ← MultilinearMap.map_update_neg]
      congr 1; funext j; by_cases h:j=i <;> simp [h,hL]
  simp_rw [H, Finset.sum_neg_distrib]; rfl

lemma oriented (E:X.System P) (H: Fields.Euclidean S) (a:SpaceAxis) {x:Points n} (hx:x∈ conf n) (v:Fin n→ X.W) :
    D (points fun i=> M4.move (turning a).val (x i)) (fun y=>S n y v) x= -(∑ i,S n x (update v i (X.lie (turning a) (v i)))):=by
  let U:=Lift.daylight a; let f t := Ortho.oneParameter (turning a) t
  have hQ : x=Points.move (f 0) x:=by rw [show f 0=1 from congrArg EuPin.coord (Lift.way a).1]; exact PiLp.ext (by simp)
  have ht : DifferentiableAt ℝ (fun y=>S n y v) x:= ((H.smooth n v x hx).contDiffAt ((conf_open n).mem_nhds hx)).differentiableAt (by simp)
  have hp:= ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 (turnsTuple x (turning a)) hQ
  have heq(t:ℝ): S n (Points.move (f t) x) v = S n x (X.action (U (-t)) ∘ v) :=by
      let V:=fun i=> X.action (U (-t)) (v i)
      have hU: U t*U (-t)=1:=by rw [← SpinParity.additive (Lift.way a), add_neg_cancel]; exact (Lift.way a).1
      have he : X.action (U t) ∘ V=v:=funext (fun i=> by
          change X.action _ (X.action _ (v i))=v i; rw [← LinearEquiv.mul_apply,← map_mul,hU,map_one]; rfl)
      exact (show S n _ v=_ by rw [← he]; nth_rw 2 [he]; exact H.rotation n x hx _ (Lift.over_spin a t) V)
  change HasDerivAt (fun t=> S n (Points.move (f t) x) v) _ 0 at hp; simp_rw [heq] at hp; exact hp.unique (rotate_labels E a x v)

def kick (X:Fields) (a:SpaceAxis) (v:X.W) := (-I) • X.lie (turning a) v
/-- Wave on the path. -/
def seen (Y : Waves X) (q : Fin n → X.W) (y : Heights n) (z : ℂ) (p : Points n) :=
  Y.F n (scaledTimes y z p) (trace p) q

def errorTerm (Y : Waves X) (a : SpaceAxis) (y : Heights n) (v : Fin n → X.W)
    (f : Joint n) (z : ℂ) (p : Points n) :=
  seen Y (v) y z p * testField a y z f p -
    z * (∑ i, seen Y (update (v) i (kick X a (v i))) y z p) * f p

private lemma seen_kick (hr : Y.Region S) (p : Points n) (a : SpaceAxis) (y : Heights n) (v : Fin n → X.W) (i : Fin n)
    (w : ℝ) (hp : stretchY y w p ∈ east n) :
    seen Y (update v i (kick X a (v i))) y ((w : ℂ)*I) p =
      (-I) * S n (foldE y w p) (update v i (X.lie (turning a) (v i))) := by
  rw [seen, scaled_imag, hr.roots n _ _ _ hp]; exact MultilinearMap.map_update_smul _ v _ _ _

private lemma field_flows (E : X.System P) (H : Fields.Euclidean S)
    (hr : Y.Region S) (p : Points n) (a : SpaceAxis) (y : Heights n) (v : Fin n → X.W)
    (w : ℝ) (hp : stretchY y w p ∈ east n) :
    fderiv ℝ (fun x => S n (foldE y w x) v) p (orbit a y w p) =
      -(((w : ℂ)*I) * ∑ i, seen Y (update (v) i (kick X a (v i))) y ((w : ℂ)*I) p) := by
  let q := foldE y w p
  let gA := Ortho.plane timeAxis a.castSucc
  have hq : q ∈ conf n := clear hp _
  have hd : DifferentiableAt ℝ (fun x => S n x v) q :=
    ((H.smooth n v q hq).contDiffAt ((conf_open n).mem_nhds hq)).differentiableAt (by simp)
  have HH := ((hd.hasFDerivAt).comp p (fold_derivative y w p)).fderiv
  change fderiv ℝ ((fun x => S n x v) ∘ foldE y w) p _ = _
  rw [HH, ContinuousLinearMap.comp_apply, orbit_image, map_smul]
  change w • D _ _ q = _
  rw [oriented E H a hq]
  simp_rw [seen_kick hr p a y v _ w hp, ← Finset.mul_sum, real_smul]
  have he (z b : ℂ) : -(z*I*(-I*b)) = z * -b := by
    calc
      _ = z * (I*I) * b := by ring
      _ = _ := by rw [I_mul_I]; ring
  exact (he _ _).symm

theorem error_imag (E : X.System P) (H : Fields.Euclidean S)
    (hr : Y.Region S) (a : SpaceAxis) (y : Heights n) (v : Fin n → X.W) (f : Joint n)
    (w : ℝ) (hK : HasCompactSupport ⇑f)
    (he : ∀ p ∈ tsupport f, scaledTimes y ((w : ℂ)*I) p ∈ strict n) :
    (∫ p in tsupport f, errorTerm Y a y v f ((w : ℂ)*I) p) = 0 := by
  have hE (p) (hp : p ∈ tsupport f) : stretchY y w p ∈ east n :=
    (scaled_strict_imag y w p).mp (he p hp)
  let u (p : Points n) := S n (foldE y w p) v
  have hU (p) (hp : p ∈ tsupport f) : ContDiffAt ℝ ∞ u p := by
    have hx : foldE y w p ∈ conf n := clear (hE p hp) _
    exact (((H.smooth n v (foldE y w p) hx).contDiffAt
      ((conf_open _).mem_nhds hx)).comp p (fold_smooth y w).contDiffAt)
  let g (p : Points n) := u p * f p
  have hG : tsupport g ⊆ tsupport f := tsupport_mul_subset_right
  have hc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _) hG
  have hg : ContDiff ℝ 1 g := contDiff_iff_contDiffAt.mpr fun p => by
    by_cases hx : p ∈ tsupport f
    · exact ((hU p hx).of_le (by norm_num)).mul (f.smooth 1).contDiffAt
    have H := notMem_tsupport_iff_eventuallyEq.mp (fun hi => hx (hG hi))
    exact contDiffAt_const.congr_of_eventuallyEq H
  calc
    _ = ∫ p in tsupport f, fderiv ℝ g p (orbit a y w p) := by
      apply setIntegral_congr_fun (isClosed_tsupport _).measurableSet
      intro p hp
      rw [errorTerm, test_imag]
      have hbase : seen Y (v) y ((w : ℂ)*I) p = u p := by
        rw [seen, scaled_imag]; exact hr.roots n v (trace p) (stretchY y w p) (hE p hp)
      change _ = fderiv ℝ (fun z => u z * f z) p (orbit a y w p)
      have hVp : fderiv ℝ u p (orbit a y w p) = _ :=
        field_flows E H hr p a y v w (hE p hp)
      rw [hbase, fderiv_fun_mul ((hU p hp).differentiableAt (by simp)) f.differentiableAt]
      simp [hVp]; ring
    _ = (∫ p, fderiv ℝ g p (orbit a y w p)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (hG h))]; rfl
    _ = 0 := integral_orbit a y w hg hc


end YM.Massive.Bridge.Rotate
