import YM.Kly.Cops
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Filter Analysis Set MeasureTheory
open Fields (pointMoment distinct)
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace ComplexOrder
variable {F:Fields}{S:F.Kernel} {a:Axis}{V:Chamber S a}{n:ℕ}
variable {m : ℕ}

def headPoints (x : Points n) (y : Points m) : Points (n + m) :=
  points (Fin.append x.ofLp y.ofLp)

theorem realize_headPoints (v : Fin n → F.W) (u : Fin m → F.W)
    (x : Points n) (y : Points m) :
    realize (Fin.append v u) (headPoints x y) = realize v x ++ realize u y := by
  unfold realize
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]

def headL (n m : ℕ) : Points n →L[ℝ] Points (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => headPoints x 0
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints] }

theorem headPoints_deriv (x : Points n) (y : Points m) :
    HasFDerivAt (fun z : Points n => headPoints z y) (headL n m) x := by
  rw [show (fun z : Points n => headPoints z y) =
    fun z => headL n m z + headPoints (0 : Points n) y from ?eq]
  · exact (headL n m).hasFDerivAt.add_const _
  case eq =>
    funext z
    apply PiLp.ext
    intro i
    change headPoints z y i = (headPoints z (0 : Points m) + headPoints (0 : Points n) y) i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]

theorem headL_column (m : ℕ) (b : Fin n × Axis) :
    headL n m (Points.direction b.1 b.2) = Points.direction (Fin.castAdd m b.1) b.2 := by
  apply PiLp.ext
  intro i
  change headPoints (Points.direction b.1 b.2) (0 : Points m) i = _
  refine Fin.addCases ?_ ?_ i
  · intro j
    by_cases hj : j = b.1 <;> simp [headPoints, Points.direction, hj]
  intro j
  have h : Fin.natAdd n j ≠ Fin.castAdd m b.1 := by
    intro e
    have hv : n + j.val = b.1.val := congrArg Fin.val e
    have hb := b.1.isLt
    omega
  simp [headPoints, Points.direction, h]

theorem nextLabels_append (v : Fin n → F.W) (u : Fin m → F.W) (b : Fin n × Axis) :
    nextLabels F (Fin.append v u) (Fin.castAdd m b.1, b.2) = Fin.append (nextLabels F v b) u := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    by_cases hj : j = b.1
    · subst j
      simp [nextLabels]
    simp [nextLabels, hj]
  intro j
  have h : Fin.natAdd n j ≠ Fin.castAdd m b.1 := by
    intro e
    have hv : n + j.val = b.1.val := congrArg Fin.val e
    have hb := b.1.isLt
    omega
  simp [nextLabels, h]

def tailG(n m:ℕ): Points m→L[ℝ] Points (n+m):= LinearMap.toContinuousLinearMap {
      toFun:=fun x=> headPoints 0 x,map_add':=by intro x y; apply PiLp.ext; intro i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [headPoints]
      map_smul':=by intro c x; apply PiLp.ext; intro i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [headPoints] }
lemma headPieces (x:Points n)(y:Points m): HasFDerivAt (fun z:Points m=> headPoints x z) (tailG n m) y:=by
      rw [show (fun z:Points m=> headPoints x z)=(fun z=>tailG n m z+ headPoints x (0: Points m)) from ?_]; · exact (tailG n m).hasFDerivAt.add_const _
      funext i; apply PiLp.ext; intro l; change headPoints x i l=(headPoints (0:Points n) i + headPoints x (0:Points m)) l; refine Fin.addCases ?_ ?_ l <;>(intro l; simp[headPoints])
lemma tailCols(n:ℕ) (b: Fin m × Axis): tailG n m (Points.direction b.1 b.2) = Points.direction (Fin.natAdd n b.1) b.2 :=by
      apply PiLp.ext; intro i; change headPoints (0:Points n) (Points.direction b.1 b.2) i=_; refine Fin.addCases ?_ ?_ i
      · intro i; have h: Fin.castAdd m i ≠ Fin.natAdd n b.1:= by intro h; have he: i.val=n+b.1.val:= congr_arg Fin.val h; have hx:=i.isLt; omega
        simp[headPoints,Points.direction,h]
      intro j; by_cases h:j=b.1<;> simp[headPoints,Points.direction,h]
lemma tailP (v:Fin n→F.W)(x:Fin m→F.W)(b:Fin m × Axis): nextLabels F (Fin.append v x) (Fin.natAdd n b.1,b.2)=Fin.append v (nextLabels F x b):=by
      funext i; refine Fin.addCases ?_ ?_ i
      · intro j; have h:Fin.castAdd m j ≠ Fin.natAdd n b.1:=by intro h; have he:j.val=n+b.1.val:=congr_arg Fin.val h; have hx:=j.isLt; omega
        simp[nextLabels,h]
      intro j; by_cases h:j=b.1 <;>simp[nextLabels,h]
lemma knit (v: Cluster F):realize (tokens v) (positions v)=v:= List.ofFn_get _
variable (J: Spread V)(H: Fields.Euclidean S){C:Sequence}{P:Calibration C}(E:F.System P)(d:ℝ≥0)
local notation "Obs"=>Work.B02.observe
variable (l r: Cluster F)
abbrev tput (x:Points n): Points (l.length + (n+r.length)):= headPoints (positions l) (headPoints x (positions r))
abbrev mput (v:Fin n→ F.W):Fin (l.length+(n+r.length))→F.W:=Fin.append (tokens l) (Fin.append v (tokens r))
lemma packedQ(x:Points n)(v:Fin n→ F.W) : realize (mput l r v) (tput l r x)=l++(realize v x++r):=by unfold mput tput; rw[realize_headPoints,realize_headPoints,knit,knit]
lemma observing (v:Fin n→F.W)(p q:Future F a) (l r:Cluster F) (hL:l=reflect p.val a)(hR:r=raised a d q.val) (x:Points n)(hx:x∈region a d n) : tput l r x ∈ conf _ ∧ Obs (V.GNS.plant p) (V.GNS.plant q) (J.place d (realize v x))= S _ (tput l r x) (mput l r v):=by
     subst l r; let w:= realize v x; have hV:= (in_region d v x).mpr hx
     have ht:= twoSides p.property (entering hV q).property; change distinct (reflect (↑p) a ++ (realize v x ++ raised a d ↑q)) at ht; rw [show reflect p.val a ++ _= _ from (packedQ (reflect p.val a) (raised a d q.val) x v).symm] at ht
     refine ⟨(realized ..).mp ht,?_⟩; rw [Work.B02.observe_apply,J.reads hV,V.GNS.measure]; change pointMoment S _=_; rw [← readAt,packedQ]; rfl
include H
lemma plant_deriv (v:Fin n→ F.W)(x:Points n)(hx:x∈region a d n)(p q:Future F a) : HasFDerivAt (fun y=> Obs (V.GNS.plant p) (V.GNS.plant q) (J.place d (realize v y))) ((Obs (V.GNS.plant p) (V.GNS.plant q)).comp (columnD J d v x)) x:=by
     let L:= reflect p.val a; let R:=raised a d q.val; let A:=tput (n:=n) L R; let D:= mput L R v; let W:= fun y=> S _ y D; have hp:A x∈conf _:= (observing J d v p q L R rfl rfl x hx).1; have he:= (((H.smooth _ D).contDiffAt ((conf_open _).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt; let P':=tailG L.length (n+R.length); have hA: HasFDerivAt A (P'.comp (headL n R.length)) x:= (headPieces (positions L) _).comp _ (headPoints_deriv x _)
     have hg:= he.comp x hA; refine HasFDerivAt.congr_fderiv (hg.congr_of_eventuallyEq (((region_open d n (a:=a)).eventually_mem hx).mono fun y hy=> (observing J d v p q L R rfl rfl y hy).2)) ?_
     let B:= (fderiv ℝ W (A x)).comp (P'.comp (headL n R.length)); let O:= Obs (V.GNS.plant p) (V.GNS.plant q); have hh(b:Fin n × Axis) : B (columns n b)=(O.comp (columnD J d v x)) (columns n b):=by
           rw [columns_eq]; simp only [ContinuousLinearMap.comp_apply, columnD_column]; unfold B; simp only [ContinuousLinearMap.comp_apply]; rw [headL_column, show P' _=_ from tailCols _ (Fin.castAdd R.length b.1,b.2)]; rw[show O (J.place _ _)=_ from (observing J d (nextLabels F v b) p q L R rfl rfl x hx).2]; let i:= Fin.castAdd R.length b.1; let y:=Fin.natAdd L.length i; have ht: nextLabels F D (y,b.2)= mput L R (nextLabels F v b):=by unfold D y i mput; rw [show nextLabels F _ (Fin.natAdd L.length _,b.2)=_ from (tailP (tokens L) (Fin.append v (tokens R)) (Fin.castAdd R.length b.1,b.2)),nextLabels_append]
           rw[←ht]; exact H.derivatives _ D y _ hp b.2
     ext1 y; change B y=(O.comp (columnD J d v x)) y; rw [←(columns n).sum_repr y,map_sum,map_sum]; simp only[map_smul,hh]
omit H
private theorem columnD_contDiff {k : ℕ} (v : Fin n → F.W)
    (h : ∀ w : Fin n → F.W,
      ContDiffOn ℝ k (fun y => J.place d (realize w y)) (region a d n)) :
    ContDiffOn ℝ k (columnD J d v) (region a d n) := by
  apply ContDiffOn.sum
  intro b _
  let Lb := ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op (innerSL ℝ (columns n b))
  have hc : ContDiff ℝ k Lb := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := k)
    (E := V.GNS.H.Op) (F := Points n →L[ℝ] V.GNS.H.Op) Lb
  exact hc.comp_contDiffOn (h _)



include H E

theorem cont_place (v : Fin n → F.W) {x : Points n} (hx : x ∈ region a d n) :
    ContinuousAt (fun y => J.place d (realize v y)) x := by
  obtain ⟨C, hC, hc⟩ := columnD_bound J H E d v hx
  apply Work.B02.continuousAt_of_plant_derivs V.GNS _ hC hc
  filter_upwards [(region_open d n).mem_nhds hx] with z hz
  exact plant_deriv J H d v z hz

theorem deriv_place (v : Fin n → F.W) {x : Points n} (hx : x ∈ region a d n) :
    HasFDerivAt (fun y => J.place d (realize v y)) (columnD J d v x) x := by
  have hc : ContinuousOn (columnD J d v) (region a d n) := by
    have hh := columnD_contDiff J d (k := 0) v fun w =>
      contDiffOn_zero.mpr fun y hy => (cont_place J H E d w hy).continuousWithinAt
    exact hh.continuousOn
  apply Work.B02.hasFDerivAt_of_plant_derivs V.GNS _ (hc.continuousAt ((region_open d n).mem_nhds hx))
  filter_upwards [(region_open d n).mem_nhds hx] with z hz
  exact plant_deriv J H d v z hz

theorem smooth_place (v : Fin n → F.W) :
    ContDiffOn ℝ ∞ (fun y => J.place d (realize v y)) (region a d n) := by
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing v with
  | zero =>
    exact contDiffOn_zero.mpr fun x hx =>
      (cont_place J H E d v hx).continuousWithinAt
  | succ k ih =>
    push_cast
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (region_open d n)).mpr
    have he (x : Points n) (hx : x ∈ region a d n) := deriv_place J H E d v hx
    exact ⟨fun x hx => (he x hx).differentiableAt.differentiableWithinAt, by simp,
      (columnD_contDiff J d v ih).congr (fun x hx => (he x hx).fderiv)⟩

end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.smooth_place
