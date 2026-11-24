import YM.MassiveBridge.Contact

/-!
# Continuation of field derivative laws

 From Aurora and real slice continue the LITERAL unsmeared derivative to
 any stricty ordered Mink imaginary times. Y corner convergence already for
 derivatives too; integration by parts now gives complex factor required by
 Wightman Theory. No rank test or comparison limit used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Directional
open Function Set Filter Analysis MeasureTheory Distribution
open Boundary hiding Fields Surface Waves Letter Sentence
open Probe Mink Mink.Poincare Complex
open Work.C20 hiding answer
open Work.C09 (time_compare)
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace
variable {n : ℕ} {X:Fields} {S:X.Kernel} {Y:Waves X} {W:Surface X} {B:∀ n, Blanket n} {A:W.Aurora B}

private lemma emit_s (ht:Y.Region S)(hp:A.FullBody Y)(w:Fin n→X.W){q:Points n}(h:q∈ordered n): A.emit w (wickSlice n q)=S n q w:=by
    let t := Boundary.trace q
    have hy : readings q∈east n:=h
    have hspace: Boundary.trace (place t 0)=t:=by funext i; simp [Boundary.trace,place,t]
    have htime: shift (place t 0) (readings q)=(fun i=> (time (q i):ℂ)*I):=by funext i; simp [shift,readings,place]
    rw [wick_glow,hp.pure n w _ _ hy,Waves.restricted,htime,hspace]
    exact (ht.roots n w t _ hy).trans (by rw [show place t (readings q)=q from place_same q])
lemma ordered_distinct {q:Points n}(h:q∈ ordered n) : q ∈ conf n := by
   have ht: readings q ∈ east n:=h
   simpa [place_same] using (clear ht (Boundary.trace q))

lemma slice_deriv (hs:Fields.Euclidean S) (ht:Y.Region S) (hp:A.FullBody Y)
    (w:Fin n → X.W) (q:Points n) (h:q∈ordered n) (i:Fin n) (a:Axis) :
    fderiv ℂ (A.emit w) (wickSlice n q) (wickSlice n (Points.direction i a)) =
      A.emit (update w i (X.partialD a (w i))) (wickSlice n q) := by
  have he : A.emit w ∘ wickSlice n =ᶠ[𝓝 q] fun t => S n t w := by
    filter_upwards [(ordered_open n).mem_nhds h] with t H using emit_s ht hp w H
  rw [emit_s ht hp _ h,←hs.derivatives n w i q (ordered_distinct h), Analysis.D, ←he.fderiv_eq]
  have hh := (hp.hol n w (wickSlice n q) (wick_tube h)).differentiableAt.hasFDerivAt
  rw [((hh.restrictScalars ℝ).comp q (wickSlice n).hasFDerivAt).fderiv]
  rfl
-- real-linear embedding as glow on a time tube

def minkLine (x : SpacePoints n) (z : Times n) : Full n :=
    glow (place x (fun i=> (z i).re)) (dawn fun i=> (z i).im)
lemma minkLine_diff (x : SpacePoints n) (z:Times n): DifferentiableAt ℂ (minkLine x) z:=by
  let f : Times n →ₗ[ℂ] Full n := {
     toFun t := WithLp.toLp 2 (fun i:Fin n × Axis=> if i.2=timeAxis then t i.1 else 0)
     map_add' t u := by ext1 i; by_cases i.2=timeAxis <;> simp [*]
     map_smul' t u := by ext1 i; by_cases i.2=timeAxis <;> simp [*] }
  let F:=LinearMap.toContinuousLinearMap f
  have he : minkLine x=fun z=>minkLine x 0 + F z := by
    funext z; ext1 i; obtain ⟨i,a⟩:=i; refine Fin.lastCases ?_ (fun j=>?_) a <;> change _=(_+f z) _
    · apply Complex.ext <;> simp [minkLine, place, dawn, glow, position, f, show timeAxis = Fin.last 3 from rfl] <;> (rw [show (3: Axis) = Fin.last 3 from rfl, Fin.snoc_last, Fin.snoc_last]; simp)
    apply Complex.ext <;> simp [minkLine, place, dawn, glow, position, f]
  rw [he]; exact differentiableAt_const _ |>.add F.differentiableAt
lemma minkLine_maps (x:SpacePoints n) : MapsTo (minkLine x) (strict n) (tube n):= fun z hz=> by
  simpa [minkLine,tube] using (etched (show (fun i=> (z i).im)∈east n from hz))
lemma minkLine_shift (q:Points n)(y:Heights n):
    minkLine (Boundary.trace q) (shift q y) = glow q (dawn y) := by
  unfold minkLine
  simp [shift, show place (Boundary.trace q) (fun i=> time (q i))=q from place_same _]
lemma minkLine_wick (p: SpacePoints n)(y:Heights n): minkLine p (fun i=>(y i:ℂ)*I) = wickSlice n (place p y):=by
  rw [minkLine, wick_glow, readings_place]
  congr 1 <;> simp [Boundary.trace,place,points]

lemma mix_deriv (hs : Fields.Euclidean S) (ht:Y.Region S) (hp:A.FullBody Y) (w:Fin n→X.W)
    (q:Points n) (y:Heights n) (h:y∈east n) (i:Fin n) (a:Axis) :
    fderiv ℂ (A.emit w) (glow q (dawn y)) (wickSlice n (Points.direction i a)) =
      A.emit (update w i (X.partialD a (w i))) (glow q (dawn y)) := by
  let W := update w i (X.partialD a (w i))
  let d := wickSlice n (Points.direction i a)
  let x := Boundary.trace q
  let l := minkLine x
  let F(z) := fderiv ℂ (A.emit w) (l z) d
  let G := A.emit W ∘ l
  have hF : DifferentiableOn ℂ F (strict n) := by
    intro z hz
    have he :=((hp.hol _ w (l z) (minkLine_maps x hz)).fderiv).differentiableAt
    exact ((ContinuousLinearMap.apply ℂ ℂ d).differentiableAt.comp _ (he.comp _ (minkLine_diff _ _))).differentiableWithinAt
  have hG : DifferentiableOn ℂ G (strict n) := fun z hz=> (((hp.hol _ W _ (minkLine_maps x hz)).differentiableAt).comp _ (minkLine_diff _ _)).differentiableWithinAt
  have pp (u: Heights n) (p:u∈east n) (b:ℝ) : F (fun i=>(↑(u i + b*0):ℂ)*I) = G (fun i=>(u i:ℂ)*I) := by
    unfold F G l; rw [comp_apply]; simp only [mul_zero, add_zero, minkLine_wick]
    exact slice_deriv hs ht hp w _ (by simp [ordered, readings_place, p]) i a
  have he := time_compare F G hF hG 0 pp (shift q y) (Waves.shift_strict q h)
  simpa only [ofReal_zero, add_zero, F, G, l, x, comp_apply, minkLine_shift] using he

def repose (n:ℕ) : Points n →L[ℝ] Full n := LinearMap.toContinuousLinearMap
  { toFun x:= glow x 0
    map_add' x y := by ext1 i; simp [glow]
    map_smul' b x := by ext1 i; simp [glow, real_smul] }

lemma repose_rel (i: Fin n)(a:Axis) : wickSlice n (Points.direction i a)=
    (if a=timeAxis then I else 1) • repose n (Points.direction i a):=by
   ext1 j; obtain ⟨j,b⟩:=j
   change _=((if a=timeAxis then I else 1:ℂ) • glow (Points.direction i a) 0) _
   by_cases j=i <;> by_cases a=b <;> by_cases b=timeAxis <;> by_cases a=timeAxis <;> simp_all [glow,wick_apply,Points.direction,basis]

lemma restricted_real (hs : Fields.Euclidean S) (ht:Y.Region S) (hp:A.FullBody Y) (w:Fin n→X.W)
    (q:Points n) (y:Heights n) (h:y∈east n) (i:Fin n) (a:Axis) :
    HasLineDerivAt ℝ (Y.restricted w y)
      ((if a=timeAxis then I else 1)⁻¹ * Y.restricted (update w i (X.partialD a (w i))) y q) q (Points.direction i a):= by
  let k := fun q : Points n=> glow q (dawn y)
  have hu: HasFDerivAt k (repose n) q := by
    have he : k = fun q=> repose n q + k 0 := by
      funext t; ext1 i; change glow _ _ _=(glow t 0 + glow 0 (dawn y)) _; simp [glow]
    rw [he]; exact (repose n).hasFDerivAt.add_const _
  have hv := ((hp.hol _ w (k q) (by simpa only [k,tube, mem_preimage, im_glow] using etched h)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp q hu
  let b := if a = timeAxis then I else 1
  have hb : b ≠ 0 := by by_cases a=timeAxis <;> simp [*,b]
  have he:= mix_deriv hs ht hp w q y h i a
  rw [repose_rel, map_smul, smul_eq_mul, hp.pure n _ q y h] at he
  rw [←he, ←mul_assoc, inv_mul_cancel₀ hb, one_mul]
  exact (hv.hasLineDerivAt _).congr_of_eventuallyEq (Eventually.of_forall (fun q=> (hp.pure _ w q y h).symm))

lemma psi_deriv (hs : Fields.Euclidean S) (ht:Y.Region S) (hp:A.FullBody Y) (hj:Y.NonTangentialFree W) (w:Fin n→X.W)
    (f : Joint n)(y:Heights n) (h:y∈east n) (i:Fin n) (a:Axis) :
    Y.psi (update w i (X.partialD a (w i))) y f = -(if a=timeAxis then I else 1)* Y.psi w y
       (LineDeriv.lineDerivOpCLM ℂ (Joint n) (Points.direction i a) f) := by
   let b := if a = timeAxis then I else 1
   have hb : b ≠ 0 := by by_cases a=timeAxis <;> simp [*,b]
   let g := Y.restricted w y
   let w':= update w i (X.partialD a (w i))
   let Q := Y.restricted w' y
   let f' := LineDeriv.lineDerivOpCLM ℂ (Joint n) (Points.direction i a) f
   have he' : Integrable (fun x : Points n=> b⁻¹ * Q x * f x) := by
     simp_rw [mul_assoc]; exact (hj.int n w' y h f).const_mul _
   have tp : (∫ x, g x * f' x) = -(∫ x, b⁻¹ * Q x * f x) :=
     integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
       (B := ContinuousLinearMap.mul ℝ ℂ) (v := Points.direction i a)
       (f := g) (g := ⇑f) (f' := fun x=> b⁻¹ * Q x) (g' := ⇑f') he'
       (hj.int n w y h f') (hj.int n w y h f)
       (fun x _ => restricted_real hs ht hp w x y h i a)
       (fun x _ => (f.hasFDerivAt x).hasLineDerivAt _)
   change (∫ x, Q x * f x)=(-b)*(∫ x, g x * f' x)
   rw [tp]
   simp_rw [mul_assoc]; rw [integral_const_mul,mul_comm,neg_mul_neg, mul_comm, ←mul_assoc,mul_inv_cancel₀ hb,one_mul]

lemma W_deriv (hs : Fields.Euclidean S) (ht:Y.Region S) (hp:A.FullBody Y) (hj:Y.NonTangentialFree W)
    (w:Fin n→X.W) (f : Joint n)(i:Fin n) (a:Axis) :
    W.W n (update w i (X.partialD a (w i))) f = -(if a=timeAxis then I else 1)* W.W n w
       (LineDeriv.lineDerivOpCLM ℂ (Joint n) (Points.direction i a) f) := by
  haveI := awaits (light n)
  exact tendsto_nhds_unique_of_eventuallyEq (hj.corner ..) (tendsto_const_nhds.mul (hj.corner ..))
      (Eventually.mono self_mem_nhdsWithin fun y h=> psi_deriv hs ht hp hj w f y h i a)

-- The direction of a product test still a single product, not a sum.
lemma product_deriv(f: Fin n→ Test4)(i:Fin n) (a:Axis) :
    LineDeriv.lineDerivOpCLM ℂ (Joint n) (Points.direction i a) (Joint.materialize n f)=
      Joint.materialize n (update f i (Reconstruction.direction a (f i))) := by
   let m:=Joint.materialize n f
   ext1 x
   let p:=fun t: ℝ => x + t • Points.direction i a
   let C:=∏ k∈ Finset.univ.erase i, f k (x k)
   have he: (fun t:ℝ=>m (p t)) = fun t=> C * f i (x i + t • basis a):=by
     funext t; unfold m; rw [Joint.material_at,← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
     congr 1
     · exact Finset.prod_congr rfl fun k hk=> by
         have := (Finset.mem_erase.mp hk).1
         simp [p,Points.direction, *]
     simp [p,Points.direction]
   let U:= Reconstruction.direction a (f i)
   have hh: HasLineDerivAt ℝ (m:Points n→ℂ) (C * U (x i)) x (Points.direction i a) := by
     change HasDerivAt (fun t=> m (p t)) _ 0
     rw [he]
     exact ((f i).hasFDerivAt (x i)).hasLineDerivAt (basis a) |>.const_mul C
   change fderiv ℝ m x (Points.direction i a) = _
   calc
      _ = C * U (x i) := by
        have hj: HasLineDerivAt ℝ (m:Points n→ℂ) (fderiv ℝ m x (Points.direction i a)) x (Points.direction i a):= (m.hasFDerivAt x).differentiableAt.hasFDerivAt.hasLineDerivAt _
        exact hj.lineDeriv.symm.trans hh.lineDeriv
      _ = _ := by
        rw [Joint.material_at, ←Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self]; congr 1
        exact Finset.prod_congr rfl (fun k hk=>by rw [update_of_ne (Finset.mem_erase.mp hk).1])
end YM.Massive.Bridge.Directional
