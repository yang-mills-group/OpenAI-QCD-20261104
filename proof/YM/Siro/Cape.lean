import YM.Massive.Target.Euclidean
import YM.OS.Dynamics

/-!
# Weakened Eu hypotheses, port Bridge Cap. Only remove rotation and unused h.

Gram completion and coordinate flows for the specified hierarchy

We work directly with the massive target `YM.Massive.Fields.Placements`, without
restricting to even words (or indeed to parity-homogeneous labels). No exchange/reordering
is needed. Cf. `YM/{OS/{Schwinger,Caps,Flow,Dynamics},Euclid/Words}` for the YM versions,
some of whose proofs we adapt for this graded setting.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fields
open Function QCD QCD.Lat Lattice Wilson UV MeasureTheory Filter Set
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder ContDiff
variable {F:Fields}(S:Kernel F)
/-- Translation invariant, no rotation hypothesis, positive in every cap.
Candidate uses same adj prescriptions and slot faithfulness after vacuum selection too. -/
structure SimpleK : Prop where
  translation n (x : Points n) (hx : x ∈ conf n) z u : S n (points fun i => x i+z) u = S n x u
  conjugate a (l : Placements F) (h : distinct l) : pointMoment S (reflect a l) = star (pointMoment S l)
  parity n (x : Points n) (hx : x ∈ conf n) u : S n x (F.parity ∘ u) = S n x u
  swap (l r : Placements F) (x y : E4 × F.W) (h : distinct (l ++ x :: y :: r)) p q
      (hp : F.homogeneous p x.2) (hq : F.homogeneous q y.2) :
    pointMoment S (l ++ x :: y :: r) = (if p && q then -1 else 1) * pointMoment S (l ++ y :: x :: r)
  empty : S 0 0 0 = 1
  unit n (x : Points (n+1)) (hx : x ∈ conf _) (p : Fin n → F.W) :
    S _ x (Fin.cons F.unit p) = S n (Points.tail x) p
  smooth n (u : Fin n → F.W) : ContDiffOn ℝ ∞ (fun x => S n x u) (conf n)
  capped n (u : Fin n → F.W) (j : ℕ) : ∃ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
    ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
      ‖iteratedFDeriv ℝ j (fun y => S n y u) x‖ ≤ A * r⁻¹^m
  derivatives n (u : Fin n → F.W) (i : Fin n) (x : Points n) (hx : x ∈ conf _) (a : Axis) :
    YM.Analysis.D (Points.direction i a) (fun x => S n x u) x = S n x (update u i (F.partialD a (u i)))
  rp a n (l : Fin n → Placements F) (he : ∀ i, positive (l i) a) (u : Fin n → ℂ) : 0 ≤ gram S a l u

end YM.Massive.Fields
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Fields (pointMoment distinct located prepend)
open OS (Cross)
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder ContDiff

-- use List abbrev throughout (Fields.Placements is reducible too)
abbrev Plant (F : Fields) := E4 × F.W
abbrev Cluster (F : Fields) := List (Plant F)
abbrev positions {F : Fields} (w : Cluster F) := @located F w
abbrev tokens {F : Fields} (w : Cluster F) (i : Fin w.length) := (w.get i).2
abbrev Positive {F : Fields} (w : Cluster F) (a : Axis) := Fields.positive (F:=F) w a
abbrev Future (F : Fields) a := {w : Cluster F // Positive (F:=F) w a}
abbrev reflect {F : Fields} (w : Cluster F) (a : Axis) := Fields.reflect (F:=F) a w
abbrev kernel {F : Fields} (S : F.Kernel) (a : Axis) (w v : Cluster F) :=
    pointMoment S (reflect (F:=F) w a ++ v)

variable {F : Fields} {n : ℕ}
def realize (v : Fin n → F.W) (x : Points n) : Cluster F := List.ofFn fun i => (x i,v i)
def carry (w : Cluster F) (x : E4) : Cluster F := w.map fun p => (p.1+x,p.2)

-- g: size-cast reading; don't re-order
lemma readCast (S : F.Kernel) {w : Cluster F} (h : n=w.length) (p : Fin n → Plant F) (x : Points n) (v : Fin n → F.W)
    (hp : ∀ i, w.get (Fin.cast h i) = p i) (he : ∀ i, p i = (x i,v i)) : pointMoment S w = S n x v := by
  subst n
  have hv (i) : w.get i = (x i,v i) := (hp i).trans (he i)
  unfold pointMoment; change S _ _ _ = _
  congr 1
  · congr 1
    exact PiLp.ext fun i => congr_arg Prod.fst (hv i)
  exact funext fun i => congr_arg Prod.snd (hv i)

@[simp] lemma readAt (S : F.Kernel) (v : Fin n → F.W) (x : Points n) : pointMoment S (realize v x) = S n x v := by
  refine readCast S (by simp [realize]) (fun i => (x i,v i)) x v ?_ (fun _ => rfl)
  simp [realize]

theorem locations {w : Cluster F} : distinct w ↔ (w.map Prod.fst).Nodup := by
  let f := fun i => (w.get i).1
  have he : w.map Prod.fst = List.ofFn f := by
    rw [show f = Prod.fst ∘ w.get from rfl,← List.map_ofFn,List.ofFn_get]
  rw [he,List.nodup_ofFn]; rfl

@[simp] theorem realized (v : Fin n → F.W) (x : Points n) : distinct (realize v x) ↔ x ∈ conf n := by
  rw [locations,realize,List.map_ofFn,List.nodup_ofFn]; rfl

theorem still {v : Cluster F} (hv : distinct v) (x : E4) : distinct (carry v x) := by
  rw [locations]
  rw [show List.map Prod.fst (carry v x) = (v.map Prod.fst).map (fun y => y+x) by simp [carry,List.map_map]]
  exact (locations.mp hv).map (fun _ _ he => add_right_cancel he)

@[simp] theorem reflectedPoint (w : Cluster F) (a : Axis) :
    reflect w a=w.reverse.map fun x => (Ortho.move (Signed.reflect a) x.1,F.adj a x.2) := rfl

-- retain statement without simplification loops for reflect.
attribute [-simp] reflectedPoint

lemma reflect_twice (a : Axis) (h : Function.Involutive (F.adj a)) (v : Cluster F) : reflect (reflect v a) a=v := by
  simp only [reflectedPoint,← List.map_reverse,List.reverse_reverse,List.map_map]
  have he (x : E4) : Ortho.move (Signed.reflect a) (Ortho.move (Signed.reflect a) x) = x := by
    ext i; by_cases hi : i=a <;> simp [Signed.mirrored,hi]
  convert! List.map_id v using 1
  congr 1; ext1 p; rcases p with ⟨t,p⟩
  exact Prod.ext (he t) (h _)

theorem strictly {w : Cluster F} {a : Axis} (h : Positive w a) {p} (hp : p ∈ reflect w a) : p.1 a < 0 := by
  rw [reflectedPoint,List.mem_map] at hp
  obtain ⟨x,hx,rfl⟩ := hp
  simp [Signed.mirrored,h.2 x (by simpa using hx)]

theorem reflects {w : Cluster F} (a) (h : distinct w) : distinct (reflect w a) := by
  rw [locations, show (reflect w a).map Prod.fst = (w.map Prod.fst).reverse.map (Ortho.move (Signed.reflect a)) by
    simp only [reflectedPoint,List.map_map, ← List.map_reverse]; rfl]
  exact (List.nodup_reverse.mpr (locations.mp h)).map (Ortho.move_injective _)

theorem twoSides {w v : Cluster F} {a} (H : Positive w a) (K : Positive v a) : distinct (F:=F) (reflect w a ++ v) := by
  rw [locations,List.map_append,List.nodup_append]
  refine ⟨locations.mp (reflects a H.1),locations.mp K.1,?_⟩
  intro x
  simp only [List.mem_map]
  rintro ⟨p,hp,rfl⟩ y ⟨q,hq,rfl⟩ he
  exact (strictly H hp).not_ge (he.symm ▸ (K.2 q hq).le)

lemma invariance {S : F.Kernel} (Ht : Fields.SimpleK S) {x : Cluster F} (hx : distinct x) (t : E4) :
    pointMoment S (carry x t)=pointMoment S x := by
  rw [show carry x t = realize (tokens x) (Points.across t (positions x)) from by
    unfold carry realize
    let f := fun p : Plant F => (p.1+t,p.2)
    have he : (List.ofFn x.get).map f = List.ofFn (f ∘ x.get) := List.map_ofFn
    rw [List.ofFn_get] at he; exact he]
  rw [readAt]; exact Ht.translation _ _ hx t _

lemma refl_over (v : Cluster F) (x : E4) (a : Axis) : reflect (carry v x) a =
    carry (reflect v a) (Ortho.move (Signed.reflect a) x) := by
  simp only [carry,reflectedPoint,← List.map_reverse,List.map_map]; congr 1
  ext1 i; exact Prod.ext ((Ortho.motion _).map_add _ _) rfl

variable {a : Axis} {S : F.Kernel}

def air (a : Axis) : Future F a := ⟨[], (show distinct (F:=F) [] from (@locations _ ([] : Cluster F)).mpr (by simp)),by simp⟩
def travel (v : Future F a) (t : ℝ≥0) : Future F a :=
  ⟨carry v.val ((t:ℝ) • basis a), still v.property.1 _, by
    intro p hp; obtain ⟨x,h,rfl⟩ := List.mem_map.mp hp
    change 0 < x.1 a + _
    exact add_pos_of_pos_of_nonneg (v.property.2 x h) (by simp)⟩

def over (v : Future F a) (u : Cross a) : Future F a :=
  ⟨carry v.val u.val, still v.property.1 _, by
    intro p hp; obtain ⟨x,h,rfl⟩ := List.mem_map.mp hp
    change 0 < x.1 a + u.val a; rw [u.property, add_zero]; exact v.property.2 _ h⟩

@[simp] lemma paths (p : Cluster F) (a b : E4) : carry (carry p a) b=carry p (a+b) := by
  unfold carry; rw [List.map_map]; congr 1; ext1 x; simp [add_assoc]
@[simp] lemma rest (p : Cluster F) : carry p 0=p := by simp [carry]
@[simp] lemma distribute (p v : Cluster F) (a : E4) : carry (p++v) a=carry p a++carry v a := by simp [carry]
lemma sym_time (h : Fields.SimpleK S) (a : Axis) (x y : Future F a) t :
    kernel S a (travel x t).val y.val = kernel S a x.val (travel y t).val := by
  unfold kernel
  let s : E4 := (t:ℝ) • basis a
  rw [← invariance h (twoSides (travel x t).property y.property) s]; congr 1; simp only [distribute, travel]
  rw [refl_over, paths, show Ortho.move (Signed.reflect a) s = -s by
    ext i; by_cases e : i=a <;> simp [s, Signed.mirrored,e], neg_add_cancel, rest]

lemma sym_space (h : Fields.SimpleK S) (a : Axis) (x y : Future F a) t :
    kernel S a (over x t).val (over y t).val = kernel S a x.val y.val := by
  unfold kernel over; simp only [refl_over]
  rw [show Ortho.move (Signed.reflect a) t.val=t.val from by
    ext i; by_cases hi : i=a <;> simp [Signed.mirrored,hi,show t.val a=0 from t.property], ← distribute]
  apply invariance h (twoSides x.property y.property)

@[simp] theorem done (w : Future F a) : travel w 0 = w := Subtype.ext (show _ from by simp [travel])
@[simp] theorem advances (w : Future F a) (t u) : travel (travel w t) u = travel w (t+u) := by
  apply Subtype.ext; simp [travel,add_smul]
@[simp] theorem inAir (t : ℝ≥0) : travel (air a (F := F)) t=air a := Subtype.ext rfl
@[simp] theorem pause (w : Future F a) : over w 0 = w := Subtype.ext (show _ from by simp [over])
@[simp] theorem parallel (w : Future F a) (t u) : over (over w t) u=over w (t+u) := by apply Subtype.ext; simp [over]
@[simp] theorem overAir (t) : over (air a (F := F)) t=air a := Subtype.ext rfl
@[simp] theorem switch (w : Future F a) (t u) : over (travel w t) u=travel (over w u) t := by apply Subtype.ext; simp [over,travel,add_comm]

def composite (v w : Cluster F) (x : E4) : Points (v.length+w.length) :=
  points (Fin.append (positions v).ofLp (Points.across x (positions w)).ofLp)

lemma placements (v w : Cluster F) (x : E4) : v ++ carry w x =
    realize (Fin.append (tokens v) (tokens w)) (composite v w x) := by
  let A := fun p : Plant F => (p.1+x,p.2)
  let b := A ∘ w.get
  unfold realize
  have he : carry w x = List.ofFn b := by
    have ht : (List.ofFn w.get).map A= List.ofFn b := List.map_ofFn
    rw [List.ofFn_get] at ht; exact ht
  rw [he, show (fun i => ((composite v w x).ofLp i, Fin.append (tokens v) (tokens w) i)) = Fin.append v.get b from ?eq]
  · rw [List.ofFn_fin_append,List.ofFn_get]
  case eq =>
    ext1 i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [composite]; rfl
    intro j; simp [composite]; rfl

lemma translations_cont (v w : Cluster F) : Continuous (composite v w) := by
  let n := v.length+w.length
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
  have he : Continuous (fun x : E4 => (composite v w x).ofLp) := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [composite]; exact continuous_const
    simp [composite]; fun_prop
  exact L.symm.continuous.comp he

lemma no_collision (a) (v w : Future F a) {x : E4} (hx : 0 ≤ x a) :
    composite (reflect v.val a) w.val x ∈ conf _ := by
  apply (realized _ _).1
  rw [← placements]
  apply twoSides v.property
  refine ⟨still w.property.1 x,?_⟩
  intro p hp; obtain ⟨q,h,rfl⟩ := List.mem_map.mp hp
  exact add_pos_of_pos_of_nonneg (w.property.2 _ h) hx

lemma uniformAway (a) (v w : Future F a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x : E4, 0 ≤ x a → spaced r (composite (reflect v.val a) w.val x) := by
  let A := reflect v.val a
  let p := composite A w.val
  have hs (i) : 0 < positions w.val i a := w.property.2 _ (List.get_mem ..)
  have ht (i) : positions A i a < 0 := strictly v.property (List.get_mem ..)
  have he (i : Fin (A.length+w.val.length)) (j : Fin (A.length+w.val.length)) : ∀ᶠ r : ℝ in 𝓝[>] 0, i ≠ j →
      ∀ x : E4, 0 ≤ x a → r ≤ cubedist (p x i) (p x j) := by
    rcases eq_or_ne i j with hk|hk
    · exact Eventually.of_forall fun _ h => (h hk).elim
    have hd : 0 < cubedist (p 0 i) (p 0 j) := by
      unfold cubedist
      exact dist_pos.mpr fun H => hk ((show Function.Injective _ from no_collision a v w (x := 0) le_rfl)
        (WithLp.ofLp_injective _ H))
    have hcr (s : Fin A.length) (t : Fin w.val.length) : ∀ᶠ r : ℝ in 𝓝[>] 0,
        ∀ (x : E4), 0 ≤ x a → r ≤ cubedist (positions A s) ((Points.across x (positions w.val)) t) := by
      filter_upwards [(gt_mem_nhds (hs t)).filter_mono nhdsWithin_le_nhds] with r hr x hx
      let Y := (Points.across x (positions w.val)) t
      apply le_trans _ (dist_le_pi_dist (positions A s).ofLp Y.ofLp a)
      rw [Real.dist_eq,abs_of_nonpos]
      · have Ht : r < positions w.val t a := hr
        change _ ≤ -(positions A s a - (positions w.val t a + x a))
        linarith [ht s]
      change positions A s a - (positions w.val t a+x a) ≤ 0
      linarith [ht s,hs t]
    revert hk hd
    refine Fin.addCases ?_ ?_ i
    · intro l
      refine Fin.addCases ?_ ?_ j
      · intro t H he
        filter_upwards [(gt_mem_nhds he).filter_mono nhdsWithin_le_nhds] with r hr h x hx
        simp only [p,composite,points_apply,Fin.append_left] at *
        exact le_of_lt hr
      intro t _ _
      filter_upwards [hcr l t] with r hr _ x hx
      simpa only [p, composite, points_apply, Fin.append_left, Fin.append_right] using hr x hx
    intro k
    refine Fin.addCases ?_ ?_ j
    · intro l _ _
      filter_upwards [hcr l k] with r hr _ x hx
      simp only [p, composite, points_apply, Fin.append_left, Fin.append_right, cubedist] at *
      rw [dist_comm]; exact hr x hx
    intro l _ he
    filter_upwards [(gt_mem_nhds he).filter_mono nhdsWithin_le_nhds] with r hr _ x hx
    simp only [p, composite, points_apply, Fin.append_right, Points.across_coord, add_zero] at *
    apply le_trans (le_of_lt hr)
    simp only [cubedist, WithLp.ofLp_add]
    rw [dist_add_right]
  have ht' : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioc 0 (1 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨r, hr,h'⟩ := (ht'.and (eventually_all.mpr fun i => eventually_all.mpr (he i))).exists
  exact ⟨r, hr.1, hr.2, fun x hx i j h => h' i j h x hx⟩

lemma correl (H : Fields.SimpleK S) (a : Axis) (v w : Future F a) :
    let f := fun x => pointMoment S (reflect v.val a ++ carry w.val x)
    ContinuousOn f {x | 0 ≤ x a} ∧ ∃ C : ℝ, ∀ x, 0 ≤ x a → ‖f x‖ ≤ C := by
  intro f
  let W := reflect v.val a
  let b := Fin.append (tokens W) (tokens w.val)
  let p := composite W w.val
  have he (x : E4) : f x = S _ (p x) b := by unfold f; rw [placements,readAt]
  obtain ⟨r,hp, hr, h⟩ := uniformAway a v w
  constructor
  · rw [funext he]; exact ((H.smooth _ b).continuousOn).comp
      (translations_cont W w.val).continuousOn (fun _ hx => no_collision _ _ _ hx)
  obtain ⟨A,D,-,hd⟩ := H.capped _ b 0
  refine ⟨D * r⁻¹^A, fun x hx => ?_⟩
  rw [he]; exact (norm_iteratedFDeriv_zero (𝕜 := ℝ) (x := p x) (f := fun y => S _ y b)).symm.trans_le (hd _ hp hr (p x) (h x hx))
end YM.Massive.Siro
