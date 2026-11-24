import YM.QCD.Flume.Ladder
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# from successive divisions to a strictly positive analytic metric

The successive divided differences need not be positive. Pay once at fixed J for
another, still analytic, set of coefficients with positivity, then take roots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}
lemma motions {f : ι→Momentum→ℂ} (h : Moderate (fun _:ι=>1) f) {ε : ℝ} (he : 0<ε) : ∃ η t : ℝ,0<η ∧ 0<t ∧ ∀ i, ∀ (x y : Momentum),x∈cube η→ dist y x<t → ‖f i y-f i x‖ < ε:= by
  obtain ⟨η,C,hp,hc,H⟩:=h
  let σ:=η/4
  let R:=η/2
  let B:= (C+C)/R
  have hs:0<σ:=by unfold σ; positivity
  have hr:0<R:=by unfold R; positivity
  have hb:0<B:=by unfold B; positivity
  refine ⟨σ,min R (ε/B),hs,lt_min hr (div_pos he hb),fun i x y hx hy=>?_⟩
  have he : ball x R⊆cube η:=(Metric.ball_subset_ball (show R≤η-σ from by unfold R σ; linarith)).trans (ball_inside_cube hx)
  have hk := hy.trans_le (min_le_left ..)
  have hw (p) (hp:p∈ball x R): ‖f i p‖≤C:=by simpa using (H i).bound p (he hp)
  have hT: MapsTo (f i) (ball x R) (closedBall (f i x) (C+C)):=fun p hg=> Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact (norm_sub_le ..).trans (add_le_add (hw p hg) (hw x (Metric.mem_ball_self hr))))
  have ht : dist (f i y) (f i x)≤ B*dist y x:= Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun p hb=>((H i).hol p (he hb)).differentiableWithinAt) hT (Metric.mem_ball.mpr hk)
  rw [← dist_eq_norm]; refine lt_of_le_of_lt ht ((mul_lt_mul_of_pos_left (hy.trans_le (min_le_right ..)) hb).trans_le (le_of_eq ?_)); field_simp

lemma rise_zone (hj : 2≤j): ∃ t b : ℝ,0<t ∧ 0<b ∧ ∀ (v : Train j) a (p : Momentum), ‖p‖<t → b ≤ (steps v a p).re:=by
  obtain ⟨c,hc,h⟩:=positive_home hj
  obtain ⟨η,t,hp,ht,H⟩:=motions (sensitivity hj (fun p:Train j × Axis=>p.1) (fun p=>p.2)) (show 0<c/2 by positivity)
  refine ⟨t,c/2,ht,by positivity,fun v a p hu=>?_⟩
  have he := H (v,a) 0 p (cube_zero _ hp) (by simpa using hu)
  have hm : |(steps v a p - steps v a 0).re|<c/2:= (Complex.abs_re_le_norm _).trans_lt he
  rw [Complex.sub_re] at hm; linarith [(abs_lt.mp hm).1,h v a]

lemma toward (p) : ∑ i:Axis, plusD p i=divisor 1 p:=by simp [plusD,divisor,seedQ,narrow]
lemma divisor_real (p : Momentum) (hp : physical p) : (((divisor 1 p).re):ℂ)=divisor 1 p ∧ 0≤(divisor 1 p).re:=by
  rw [divisor_normSq _ hp]; simp only [Complex.ofReal_re]; exact ⟨trivial,by positivity⟩

def hall (v : Train j) (δ : ℝ) (p : Momentum) (a) := (hemi v p+(δ:ℂ)*steps v a p)/(divisor 1 p + (δ:ℂ))
lemma hall_per (v : Train j) (δ : ℝ) (a) : Overlaps zone fun p=> hall v δ p a := by
  intro p hp x hx; unfold hall; dsimp only; rw [show hemi v (p+_) =_ from roof_overlaps v p hp _ hx,stair_stable v a p x,chipSq_stable]; -- dsimp
lemma hall_sym (hj : 2≤j) (v : Train j) (δ : ℝ) (p : Momentum) (hp : p∈baseCube) (a) :
    star (hall v δ p a)=hall v δ p a ∧ hall v δ (-p) a=hall v δ p a:= by
  have hh : star (divisor 1 p)= divisor 1 p:=by rw [← (divisor_real p hp.1).1]; simp
  have he:= stitch hj v a hp
  have hs : divisor 1 (-p)=divisor 1 p:=by unfold divisor; simp only [neg_neg,mul_comm]
  unfold hall; rw [hs,he.2,show hemi v (-p)=hemi v p from (by unfold hemi; rw [evenD v p (base_subset_realCube zone_pos hp)]; rfl),star_div₀]; simp only [star_add,star_mul,he.1, hh,show star (hemi v p)=hemi v p from (native_dir _ _ hp.1).1]; simp [mul_comm]
lemma hallH (hj : 2≤j) {δ : ℝ} (hd : 0<δ) (v : ι→Train j) (a : ι→Axis) : Moderate (fun _:ι=>1) fun i p=> hall (v i) δ p (a i):=by
  have hh := (divisor_control (fun _ : ι=>1)).add (Moderate.const (δ:ℂ))
  have hk : Firm (fun _ : ι=>1) fun (_ : ι) p=>divisor 1 p+(δ:ℂ) := by
    refine ⟨zone,δ,zone_pos,hd,fun i p hp=>?_⟩; rw [mul_one]; apply le_trans _ (Complex.re_le_norm _); rw [Complex.add_re]; exact le_add_of_nonneg_left (divisor_real p hp.1).2
  have hZ := hh.inv hk fun _=>one_pos
  have hu : Moderate (fun _ : ι=>1) fun i p=> hemi (v i) p+(δ:ℂ)*steps (v i) (a i) p:= by
    apply ((Dir_budget hj v).scalar).add; simpa only [one_mul] using (Moderate.const (δ:ℂ)).mul (sensitivity hj v a)
  simpa only [hall, inv_one,one_mul,div_eq_mul_inv] using hu.mul hZ

lemma hull_sum (hj : 2≤j) {δ : ℝ} (hd : 0<δ) (v : Train j) {p : Momentum} (hp : p∈baseCube):
    ∑ i:Axis, plusD p i* hall v δ p i= hemi v p :=by
  have hZ : divisor 1 p+(δ:ℂ)≠0:=by
    intro h; have ht:= congr_arg Complex.re h; rw [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at ht; linarith [(divisor_real p hp.1).2]
  apply mul_right_cancel₀ hZ
  rw [sum_mul]
  have hh i : plusD p i*hall v δ p i*(divisor 1 p+(δ:ℂ))=plusD p i*hemi v p+(δ:ℂ)*(plusD p i*steps v i p):=by
    rw [hall,mul_assoc,div_mul_cancel₀ _ hZ]; ring
  simp_rw [hh]; rw [sum_add_distrib,← sum_mul,← mul_sum,chosen_steps hj _ _ hp,toward]; ring

lemma new_law (hj : 2≤j):∃ δ τ : ℝ,0<δ∧0<τ∧∀ (v : Train j) p,p∈baseCube → ∀ i, τ≤(hall v δ p i).re:=by
  obtain ⟨η,c,hp,-,hc,H⟩:=size_q hj
  obtain ⟨t,b,ht,hb,h⟩:=rise_zone hj
  obtain ⟨θ,B,hθ,hB,hh⟩:=sensitivity hj (fun i:Train j × Axis=>i.1) fun i=>i.2
  obtain ⟨s,C,hs,hC,w⟩:=divisor_control (fun _ : Unit=> (1: Side))
  let δ:ℝ:= c*t^2/(2*B)
  have hd : 0<δ := by unfold δ; positivity
  refine ⟨δ,min (δ*b/(C+δ)) (δ*B/(C+δ)),hd,lt_min (by positivity) (by positivity),fun v p hu i=>?_⟩
  have hc' : c*lengthSq p ≤ (hemi v p).re:= (H v p (base_subset_realCube hp hu)).2
  let X:=divisor 1 p
  have hz:0<X.re+δ:= add_pos_of_nonneg_of_pos (divisor_real p hu.1).2 hd
  have hA:X.re+δ≤C+δ:=by gcongr; apply (Complex.re_le_norm _).trans; simpa using (w ()).bound p (mem_cube_real (base_subset_realCube hs hu) hs)
  have hy : ((steps v i p).re:ℂ)=steps v i p:=Complex.ext rfl (Eq.symm (Complex.conj_eq_iff_im.mp (stitch hj v i hu).1))
  have hEq : (hall v δ p i).re=((hemi v p).re +δ*(steps v i p).re)/(X.re+δ):=by
    have hi : (hall v δ p i) = (((((hemi v p).re +δ*(steps v i p).re)/(X.re+δ)):ℝ):ℂ):=by
      unfold hall; simp only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,hy,show ((hemi v p).re:ℂ)=hemi v p from (native_dir v p hu.1).caste,show (X.re:ℂ)=_ from (divisor_real p hu.1).1]
    rw [hi,Complex.ofReal_re]
  rw [hEq]
  by_cases hk : ‖p‖ < t
  · apply (min_le_left ..).trans; apply div_le_div₀ _ _ hz hA
    · apply add_nonneg; · exact le_trans (by apply mul_nonneg hc.le; unfold lengthSq; positivity) hc'
      exact mul_nonneg hd.le (hb.le.trans (h v i p hk))
    have he:0≤lengthSq p:=by unfold lengthSq; positivity
    nlinarith [h v i p hk]
  have hlen : t^2 ≤ lengthSq p:= by
    refine (pow_le_pow_left₀ ht.le (not_lt.mp hk) _).trans ?_
    obtain ⟨a,ha⟩ : ∃ i, ‖p‖=‖p i‖:= by
      rw [← coe_nnnorm]; change ∃ i, ↑(univ.sup fun i=>‖p i‖₊)=(‖p i‖:ℝ)
      obtain ⟨i,_,he⟩:=Finset.exists_mem_eq_sup univ univ_nonempty fun i=> ‖p i‖₊; exact ⟨i,by rw [he]; rfl⟩
    rw [ha]; exact single_le_sum (fun j _=>sq_nonneg ‖p j‖) (mem_univ a)
  have hk : ‖steps v i p‖≤B:=by simpa using (hh (v,i)).bound p (mem_cube_real (base_subset_realCube hθ hu) hθ)
  have hn : δ*B ≤ (hemi v p).re+δ*(steps v i p).re := by
    have he : 2*δ*B=c*t^2:= by unfold δ; field_simp
    nlinarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans hk)).1]
  exact (min_le_right ..).trans (div_le_div₀ ((mul_pos hd hB).le.trans hn) hn hz hA)
end YM.QCD.Flume
