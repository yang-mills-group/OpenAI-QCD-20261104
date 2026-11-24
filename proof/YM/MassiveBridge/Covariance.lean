import YM.MassiveBridge.Slash
import YM.Work.C08
/-!
# At the boundary, derive covariance under the proper orthochronous double cover

Reuse scalar boost integration argument of Work.C09 after obtaining our
field-wide `Boosty`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Rotate
open Set Filter Function Analysis MeasureTheory Mink Mink.Poincare Complex
open Boundary hiding Fields Surface Waves
open Work.C09 (push_one push_mul motion_push time_compare spatialMap move_position)
open Bid (inclined C08 realTerm)
open MassiveTwoEstimates
open MassiveTwoEstimates.BoostMotion (point)
open Spinor
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {Q:Massive.Sequence} {P:Calibration Q} {X:Fields} {S:X.Kernel}
variable {Y:Waves X} {W:Surface X} {K:WSpins X} {n:ℕ}
theorem restricted_translation (hT : Fields.Euclidean S) (he : Y.Region S)
    (v : Fin n → X.W) (x : Points n) (a : E4) {y : Heights n} (hy : y∈east n) :
    Y.restricted v y ((translation a).zusammen n x) = Y.restricted v y x := by
  let z := shift x y
  have hz : z ∈ strict n := by
    simpa [z] using on_profile x y 1 (by norm_num) hy
  let p : SpacePoints n := trace x
  let p' : SpacePoints n := fun i => spatial (x i)+spatial a
  have hs : trace ((translation a).zusammen n x) = p' := by
    funext i; simp [trace,zusammen,p']
  have ht : shift ((translation a).zusammen n x) y = fun i => z i + (↑(YM.time a):ℂ) := by
    funext i
    simp [z,zusammen,shift,add_left_comm,add_comm]
  unfold Waves.restricted; rw [hs, ht]
  refine time_compare (fun u => Y.F n u p' v) (fun u => Y.F n u p v)
    (he.hol n v p') (he.hol n v p) (YM.time a) ?_ z hz
  intro u hu b
  let u' : Heights n := fun i => u i + b*YM.time a
  have hu' : u'∈east n := fun _ _ hij => add_lt_add_left (hu hij) _
  have hpp : place p' u' = Points.across (position (spatial a) (b*YM.time a)) (place p u) := by
    ext1 i
    apply Mink.ext_by <;> simp [place,p',p,u',trace]
  rw [he.roots n v p' u' hu',he.roots n v p u hu,hpp]
  exact hT.translation n (place p u) (clear hu _) _ v

theorem restricted_spatial (H:Fields.Euclidean S) (he : Y.Region S) (v : Fin n → X.W)
    (x : Points n) (e : EuPin) (hr : Lorentz.spatialTurn e.coord) {y : Heights n} (hy : y∈east n) :
    Y.restricted (X.action e ∘ v) y ((motion (Lorentz.room e.coord hr)).zusammen n x) =
      Y.restricted v y x := by
  let r:= e.coord
  let z := shift x y
  have hz : z ∈ strict n := by
    simpa [z] using on_profile x y 1 (by norm_num) hy
  let p := trace x
  let p' : SpacePoints n := spatialMap r ∘ p
  let t := (motion (Lorentz.room r hr)).zusammen n x
  have heq i : t i = r.move (x i) := by
    simp only [t,zusammen,points,WithLp.ofLp_toLp,as_active]; rfl
  have hpp (i) : t i = position (p' i) (YM.time (x i)) := by
    change t i = position (spatialMap r (p i)) _
    rw [heq, ← move_position r hr (p i)]; simp [p,trace]
  have hs : trace t = p' := by funext i; simp [trace,hpp]
  have ht : shift t y = z := by
    funext i; simp only [z,shift]; rw [show YM.time (t i)=YM.time (x i) by rw [hpp,time_position]]
  let v' := X.action e ∘ v
  have hg (u : Heights n) : place p' u = Points.move r (place p u) := by
    ext1 i; exact (move_position r hr _ _).symm
  change Y.F n (shift t y) (trace t) v' = Y.F n z p v
  rw [ht,hs]
  have hj (u : Heights n) (hu : u∈east n) (b : ℝ) :
      Y.F n (fun i => (↑(u i+b*0):ℂ)*I) p' v' = Y.F n (fun i => (↑(u i):ℂ)*I) p v := by
    rw [he.roots n v p u hu]
    simp only [mul_zero,add_zero]
    rw [he.roots n v' p' u hu,hg]
    exact H.rotation _ _ (clear hu _) e hr.1 v
  simpa using time_compare (fun u => Y.F n u p' v') (fun u => Y.F n u p v)
    (he.hol _ _ _) (he.hol _ _ _) 0 hj z hz

/-- Transfer point covariance with unchanged strict heights to W. Here used
for spatial rotations and all real translations; not assuming such a
strict-height covariance for boosts. -/
theorem corner_maps (hw : Y.NonTangentialFree W) (p : Poincare) (v u : Fin n → X.W)
    (h : ∀ x y, y∈east n → Y.restricted u y (p.zusammen n x) = Y.restricted v y x)
    (f : Joint n) : W.W n u (Joint.gpush n p f) = W.W n v f := by
  have he (p : Poincare) : LeftInverse (p⁻¹.zusammen n) (p.zusammen n) := by
    intro x; ext1 i; exact p.unmade (x i)
  let e : Points n ≃ᵐ Points n := {
    toFun := p.zusammen n
    invFun := p⁻¹.zusammen n
    left_inv := he p
    right_inv := by simpa only [Function.RightInverse,inv_inv] using he p⁻¹
    measurable_toFun := (p.together n).measurable
    measurable_invFun := (p⁻¹.together n).measurable }
  let f' := Joint.gpush n p f
  have hp (y : Heights n) (hy : y∈east n) : Y.psi u y f' = Y.psi v y f := by
    unfold Waves.psi
    rw [← (p.together n).integral_comp e.measurableEmbedding]
    simp_rw [h _ _ hy, f', Joint.gpush_at, he p _]
  haveI := awaits (light n)
  have hf : Tendsto (fun y => Y.psi u y f') (𝓝[east n] 0) (𝓝 (W.W n u f')) := hw.corner ..
  refine tendsto_nhds_unique hf ?_
  have hg : Tendsto (fun y => Y.psi v y f) (𝓝[east n] 0) (𝓝 (W.W n v f)) := hw.corner ..
  exact hg.congr' <| Eventually.mono self_mem_nhdsWithin fun x hx => (hp x hx).symm

/-- Boost identity passes to the boundary. We only need corner convergence
on fixed tests, including the extra tests appearing with a coefficient that
vanishes with the ordered height. -/
theorem boost_corner (hb : Boosty Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → X.W) (a : SpaceAxis) (f : Joint n) :
    (∑ i, W.W n (update v i (kick X a (v i))) f) = W.W n v (inclined a 0 f) := by
  let F := 𝓝[east n] (0:Heights n)
  haveI : F.NeBot := awaits (light n)
  let u := v
  have he (w : Fin n → X.W) (g : Joint n) : Tendsto (fun y => Y.psi w y g) F (𝓝 (W.W n w g)) := hw.corner ..
  let l := fun (i : Fin n) => realTerm i a.castSucc f
  let c := fun (i : Fin n) (y : Heights n) => (y i : ℂ)*I
  have hc (y : Heights n) : inclined a y f = inclined a 0 f + ∑ i, c i y • l i := by
    simp [inclined,c,l,Finset.sum_add_distrib]
  let P (y : Heights n) (hy : y∈east n) : Joint n →ₗ[ℂ] ℂ := {
    toFun := Y.psi u y
    map_add' g j := by
      unfold Waves.psi
      rw [← integral_add (hw.int n u y hy g) (hw.int n u y hy j)]
      apply integral_congr_ae; filter_upwards with x; simp [mul_add]
    map_smul' z g := by
      change Y.psi u y (z • g) = z * Y.psi u y g
      unfold Waves.psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  have hh (y) (hy : y∈east n) : Y.psi u y (inclined a y f) = Y.psi u y (inclined a 0 f) +
      ∑ i, c i y * Y.psi u y (l i) := by
    rw [hc y]
    change P y hy _ = P y hy _ + ∑ i, c i y • (P y hy) (l i)
    simp only [map_add,map_sum,map_smul]
  have hz (i : Fin n) : Tendsto (fun y => c i y * Y.psi u y (l i)) F (𝓝 0) := by
    have hp : Continuous (c i) := by unfold c; fun_prop
    have ht := ((hp.tendsto 0).mono_left (nhdsWithin_le_nhds (s:= east n))).mul (he u (l i))
    simpa only [c,Pi.zero_apply,ofReal_zero,zero_mul] using ht
  have hs : Tendsto (fun y => ∑ i, c i y * Y.psi u y (l i)) F (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hz i)
  let w := fun i => update u i (kick X a (v i))
  refine tendsto_nhds_unique (tendsto_finsetSum Finset.univ (fun i _ => he (w i) f)) ?_
  have ht := (he u (inclined a 0 f)).add hs
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s:=east n)] with y hy
  exact (hh y hy).symm.trans (hb n v a f y hy).symm

/-- Differentiate a joint expectation with labels and tests both moving.
This uses only derivatives of pairings at *fixed* labels together with
label derivatives within finite-dimensional spaces (here a common cap).
In particular no continuity assumption on joint distributions as functions
on the whole Union, nor any norm-differentiability in a dual space. -/
theorem moving_eval {d : ℕ} [FiniteDimensional ℂ (X.level d)]
    (M : MultilinearMap ℂ (fun _ : Fin n => (Spinor.Wd X d)) (Distn (Points n)))
    (v : ℝ → Fin n → (Spinor.Wd X d)) (v' : Fin n → (Spinor.Wd X d))
    (f : ℝ → Joint n) (f' : Joint n)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) 0)
    (hf : ∀ u, HasDerivAt (fun t => M u (f t)) (M u f') (0:ℝ)) :
    HasDerivAt (fun t => M (v t) (f t))
      ((∑ i, M (update (v 0) i (v' i)) (f 0)) + M (v 0) f') (0:ℝ) := by
  classical
  let B := Module.finBasis ℂ ((Spinor.Wd X d))
  let c (i) : (Spinor.Wd X d) →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap (B.coord i)).restrictScalars ℝ
  let p (j : Fin n → Fin (Module.finrank ℂ ((Spinor.Wd X d)))) (u : Fin n → (Spinor.Wd X d)) :=
    ∏ i, c (j i) (u i)
  let A (j : Fin n → Fin (Module.finrank ℂ ((Spinor.Wd X d)))) := M (fun i => B (j i))
  have he (u : Fin n → (Spinor.Wd X d)) : M u = ∑ j, p j u • A j := by
    have hh i : ∑ j, c j (u i) • B j = u i := B.sum_repr _
    conv_lhs => rw [← funext hh]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun j _ => M.map_smul_univ _ _
  have hh (u : Fin n → (Spinor.Wd X d)) (g : Joint n) : M u g = ∑ j, p j u * A j g := by
    rw [he, sum_apply]; rfl
  have hl (i j) : HasDerivAt (fun t => c j (v t i)) (c j (v' i)) (0:ℝ) :=
    (c j).hasFDerivAt.comp_hasDerivAt 0 (hv i)
  have ht (j : Fin n → Fin (Module.finrank ℂ ((Spinor.Wd X d)))) :
      HasDerivAt (fun t => p j (v t)) (∑ i, p j (update (v 0) i (v' i))) (0:ℝ) := by
    have hg (i : Fin n) : p j (update (v 0) i (v' i)) =
        (∏ k ∈ Finset.univ.erase i, c (j k) (v 0 k)) • c (j i) (v' i) := by
      unfold p
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      simp only [update_self,smul_eq_mul]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by rw [update_of_ne (Finset.mem_erase.mp hk).1]
    simp_rw [hg]
    exact HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _ => hl i (j i))
  simp_rw [hh]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum; intro j _
  simpa [Finset.sum_mul,A] using! (ht j).mul (hf (fun i => B (j i)))

def ride (W : Surface X) (K : WSpins X) (a : SpaceAxis)
    (v : Fin n → X.W) (f : Joint n) (t : ℝ) :=
  W.W n (fun i => K.spin (point (Ray.fromAxis a) t) (v i))
    (Joint.gpush n (motion ((Ray.fromAxis a).boost t)) f)



theorem boost_origin (hpush : C08)
    (E:X.System P) (K:WSpins X)
    (hb : Boosty Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → X.W) (f : Joint n) (a : SpaceAxis) :
    HasDerivAt (ride W K a v f) 0 (0:ℝ) := by
  classical
  obtain ⟨d,u,rfl⟩ := cover_cap E v
  haveI := E.finite d
  let M : MultilinearMap ℂ (fun _ : Fin n => (Spinor.Wd X d)) (Distn (Points n)) :=
    (W.W n).compLinearMap (fun _ => (X.level d).subtype)
  let b := Ray.fromAxis a
  let l (t : ℝ) := fun i:Fin n => (⟨K.spin (point b t) (u i).val, K.lives _ _ _ (u i).property⟩ : Spinor.Wd X d)
  choose l' hl' Hl using fun i :Fin n=> level_derivative d (fun t=>l t i) 0 _ (K.boost a _ (Lift.path a) (u i).val)
  let g (t) := Joint.gpush n (motion (b.boost t)) f
  have hg : g 0=f := by rw [show g 0 = Joint.gpush n 1 f by simp [g],push_one]
  let g' := -inclined a 0 f
  have hg' (w) : HasDerivAt (fun t => M w (g t)) (M w g') (0:ℝ) := by
    let D := (M w).restrictScalars ℝ
    change HasDerivAt (fun t => D (g t)) (D g') 0
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have ht : Tendsto (fun t : ℝ => t⁻¹ • (g t - f)) (𝓝[≠] 0) (𝓝 g') := hpush.2 n f a
    have hs := (D.continuous.tendsto _).comp ht
    simpa only [Function.comp_def,map_smul,map_sub,zero_add,hg] using hs
  have he : HasDerivAt (fun t => M (l t) (g t))
      ((∑ i, M (update (l 0) i (l' i)) (g 0)) + M (l 0) g') (0:ℝ) :=
    moving_eval M l l' g g' Hl hg'
  have hl : l 0 = u := by
    funext i; apply Subtype.ext; change K.spin (point b 0) _=_; rw [Lift.begins,map_one]; rfl
  let w : Fin n → X.W := fun i => (u i).val
  have hu (i) : M (update u i (l' i)) = W.W n (update w i (kick X a (w i))) := by
    unfold M; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg (W.W n)
    funext j; by_cases h : j=i <;> simp [h,w,kick,hl']
  rw [hg,hl] at he
  simp_rw [hu] at he
  rw [boost_corner hb hw w a f] at he
  change HasDerivAt (fun t => M (l t) (g t)) (_ + W.W n w (-inclined a 0 f)) (0:ℝ) at he
  rw [map_neg,add_neg_cancel] at he
  have hid : ride W K a ((X.level d).subtype ∘ u) f = fun t => M (l t) (g t) := by
    funext t
    rfl
  rw [hid]; exact he

theorem boost_invariant (hpush : C08)
    (E:X.System P) (K:WSpins X)
    (hb : Boosty Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → X.W) (f : Joint n) (a : SpaceAxis) :
    ∀ r : ℝ, ride W K a v f r = W.W n v f := by
  let p := ride W K a v f
  have hp (t : ℝ) : HasDerivAt p 0 t := by
    let b := Ray.fromAxis a
    let v' : Fin n → X.W := fun i => K.spin (point b t) (v i)
    let g := Joint.gpush n (motion (b.boost t)) f
    let q := ride W K a v' g
    have he (s : ℝ) : p (t+s) = q s := by
      unfold p q ride
      rw [add_comm t s,b.boost_add,overL,push_mul]
      rw [← Lift.point_mul b s t,map_mul]; rfl
    have ht : p t=q 0 := by simpa using he 0
    have hq : HasDerivAt q 0 0 := boost_origin hpush E K hb hw v' g a
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simp_rw [he, ht]
    simpa only [zero_add] using hq.tendsto_slope_zero
  have h0 : p 0 = W.W n v f := by simp [p,ride,Lift.begins,push_one]
  suffices h : p = fun _ => W.W n v f from congr_fun h
  apply eq_of_fderiv_eq (𝕜:=ℝ) (fun t => (hp t).differentiableAt) (differentiable_const _) _ 0 h0
  intro x
  rw [fderiv_fun_const, (hp x).hasFDerivAt.fderiv]
  ext; simp


lemma every_motion (E:X.System P) (e:Fields.Euclidean S) (K:WSpins X) (h:Y.Region S) (hw:Y.NonTangentialFree W) (hp:Y.Breathes) (q:RealSpin) (v:Fin n → X.W) (f:Joint n) : W.W n (K.spin q ∘ v) (Joint.gpush n (motion q.coord) f) = W.W n v f := by
   have hm p q : (p*q:RealSpin).coord=p.coord*q.coord:=rfl
   have hf : (1:RealSpin).coord=1:=rfl
   have ht := Spinor.reaches q; induction ht using Subgroup.closure_induction generalizing v f with
   | mem g hg=>
     rcases hg with ⟨c,hc,hg,he⟩|⟨i,t,rfl⟩
     · rw [K.spatial c hc g hg.symm he.symm,←hg]; exact corner_maps hw _ v _ (fun x y => restricted_spatial e h v x c hc) f
     exact boost_invariant Work.C08.answer E K (analytic_boost E e h hp) hw v f i t
   | one=> rw [map_one,hf,inactive,push_one]; rfl
   | mul x y hx hy ha he=> rw [hm,overL,push_mul,map_mul]; exact (ha (K.spin y ∘ v) _).trans (he v f)
   | inv x hx Hx=>
     rw [← Hx (K.spin x⁻¹ ∘ v) _]
     rw [← push_mul, ← overL,← hm,mul_inv_cancel,hf,inactive,push_one]
     simp [Function.comp_def]
lemma translations (H:Fields.Euclidean S) (h:Y.Region S) (hw:Y.NonTangentialFree W)
    (v:Fin n→ X.W)(f:Joint n)(b:E4): W.W n v (Joint.gpush n (translation b) f)= W.W n v f:=
   corner_maps hw _ _ _ (fun x _=>restricted_translation H h v x b) f
end YM.Massive.Bridge.Rotate
