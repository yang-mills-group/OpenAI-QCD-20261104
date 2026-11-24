import YM.QCD.Flume.Divvy

/-! # exporting analytic positive roots of signed-diagonal completion -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ} (hj : 2 ≤ j)

/- symmetrize -/
abbrev cubeCounts := Fintype.card Signed
lemma counts_pos : 0<cubeCounts:=Fintype.card_pos

def ranked (v : Train j) (δ : ℝ) (p : Momentum) (a : Axis) := (cubeCounts:ℂ)⁻¹*∑ s:Signed,hall v δ (s.act p) (s.perm a)
lemma ranks (s : Signed) (v : Train j) (δ p a) : ranked v δ (s.act p) (s.perm a)=ranked v δ p a:=by
  unfold ranked; rw [← Equiv.sum_comp (Equiv.mulRight s) (fun s:Signed=> hall v δ (s.act p) (s.perm a))]; simp only [Equiv.coe_mulRight,Signed.mul_perm_apply,Signed.act_mul]
lemma laplace_s (s : Signed) (p : Momentum) (a) : plusD (s.act p) (s.perm a)=plusD p a:=by
  unfold plusD; rw [Pi.neg_apply,Signed.act_at]; split <;> simp [mul_comm]
lemma follows_r (s : Signed) (x : Cover) : s.act (Laurent.reciprocal x)=Laurent.reciprocal (s.act x):=by
  funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; unfold Laurent.reciprocal; rw [Signed.act_at]; split <;> simp
lemma rang (v : Train j) (δ:ℝ) (a) : Overlaps zone fun p=>ranked v δ p a:=by
  intro p hp x hx; unfold ranked; dsimp only; apply congr_arg (fun z : ℂ=> (cubeCounts:ℂ)⁻¹*z); apply sum_congr rfl; intro i _
  rw [Signed.act_add,follows_r]
  exact hall_per v δ (i.perm a) _ (real_signed i hp) _ (by rw [← follows_r,← Signed.act_add]; exact real_signed i hx)
lemma band_signed (s : Signed) {η:ℝ} (p : Momentum) (hp : p∈cube η) : s.act p∈cube η:=by
  constructor <;> intro i <;> obtain ⟨i,rfl⟩:=s.perm.surjective i <;> rw [Signed.act_at]
  · split <;> simpa using hp.1 i
  split <;> simpa using hp.2 i

include hj
lemma rated (v : ι → Train j) {δ : ℝ} (hd : 0<δ) (a : ι→Axis):Moderate (fun _ : ι=>1) fun i p=> ranked (v i) δ p (a i):=by
  have hh : Moderate (fun _ : ι=>1) fun i p=> ∑ s:Signed, hall (v i) δ (s.act p) (s.perm (a i)) := by
    refine Moderate.sum _ _ (fun _=>zero_le_one) (fun s _=> ?_)
    obtain ⟨η,C,hp,hc,h⟩:=hallH (j:=j) (by exact hj) hd v (fun i=>s.perm (a i))
    refine ⟨η,C,hp,hc,fun i=>⟨fun p hh=> ?_,fun p hh=>(h i).bound _ (band_signed s _ hh)⟩⟩
    have he : Differentiable ℂ (fun p:Momentum=>s.act p):= by apply differentiable_pi.mpr; intro i; obtain ⟨i,rfl⟩:=s.perm.surjective i; simp only [Signed.act_at]; split <;> fun_prop
    exact ((h i).hol _ (band_signed s p hh)).comp p he.differentiableAt
  unfold ranked; simpa only [one_mul] using (Moderate.const _).mul hh
omit hj in
lemma drop (δ : ℝ) (p : Momentum) (v : Train j) (a) (hp : p∈realCube zone) : ranked v δ (inside p) a=ranked v δ p a:= rang v δ a p hp _ (base_subset_realCube zone_pos (inside_base hp.1))
include hj
lemma symmetry (δ : ℝ) (p : Momentum) (v : Train j) (a) (hp : p∈realCube zone) : star (ranked v δ p a)=ranked v δ p a ∧ ranked v δ (-p) a=ranked v δ p a:=by
  refine ⟨?_, ranks ⟨1,fun _=>true⟩ v δ p a⟩
  rw [← drop δ p v a hp]; unfold ranked; simp only [star_mul,star_inv₀,star_sum]; simp_rw [fun s : Signed=> (hall_sym hj v δ _ (bank_acts (inside p) (inside_base hp.1) s) (s.perm a)).1]; simp only [Complex.star_def,map_natCast,mul_comm]
lemma rank_law (v : Train j) (δ : ℝ) (hd : 0<δ) (p : Momentum) (hp : p∈baseCube) :
    ∑ a:Axis,plusD p a* ranked v δ p a=hemi v p:=by
  have hh (s:Signed):∑ a:Axis,plusD p a*hall v δ (s.act p) (s.perm a)=hemi v p:=by
    rw [← north s v p (base_subset_realCube zone_pos hp),← hull_sum hj hd v (bank_acts _ hp s),← Equiv.sum_comp s.perm (fun i=> plusD (s.act p) i* hall v δ (s.act p) i)] -- placeholder
    simp_rw [laplace_s s p]
  have hv (a:Axis):plusD p a* ranked v δ p a=(cubeCounts:ℂ)⁻¹ * ∑ s:Signed, plusD p a*hall v δ (s.act p) (s.perm a):=by unfold ranked; rw [mul_left_comm,← Finset.mul_sum]
  simp_rw [hv]; rw [← Finset.mul_sum,Finset.sum_comm]; simp_rw [hh,Finset.sum_const,card_univ,nsmul_eq_mul,← mul_assoc, inv_mul_cancel₀ (show (cubeCounts:ℂ)≠0 by exact_mod_cast counts_pos.ne'),one_mul]

omit hj in
lemma ranking {δ b : ℝ} (he : ∀ (v : Train j) p,p∈baseCube → ∀ i,b ≤ (hall v δ p i).re) (p : Momentum) (hp : p∈realCube zone) (v : Train j) (a) : b ≤ (ranked v δ p a).re:=by
  rw [← drop _ _ _ a hp]; unfold ranked; rw [← Complex.ofReal_natCast,← Complex.ofReal_inv]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum]
  have hm := sum_le_sum (s:=Finset.univ) fun i _=> he v _ (bank_acts _ (inside_base hp.1) i) (i.perm a)
  rw [sum_const,card_univ,nsmul_eq_mul] at hm; rw [inv_mul_eq_div,le_div_iff₀ (by exact_mod_cast counts_pos)]; exact (mul_comm ..).trans_le hm
omit hj in
lemma cmag {x : ℂ} (h : x≠0) : Complex.sqrt x * Complex.sqrt x = x:= by
  rw [sqrt_eq_exp h,← Complex.exp_add, show Complex.log x/2+Complex.log x/2=Complex.log x by ring,Complex.exp_log h]
omit hj in
lemma radiant {B : ι→Momentum→ℂ} {t τ : ℝ} (hB : Moderate (fun _=>1) B) (ht : 0<t) (hh:0<τ) (hx : ∀ i p,p∈realCube t → τ≤ (B i p).re) :
    Moderate (fun _ : ι => 1) fun i p=> Complex.sqrt (B i p):=by
  obtain ⟨η,ρ,hp,hρ,h⟩:=motions hB hh
  obtain ⟨s,C,hs,hc,H⟩:= hB
  let z:=min (min η s) (min t (ρ/2))
  have hz:0<z:=lt_min (lt_min hp hs) (lt_min ht (by positivity))
  have he (i : ι) (p : Momentum) (hu:p∈cube z) : 0 < (B i p).re:=by
    have hq : rpart p ∈ realCube z:= rpart_mem_realCube hu
    have hw:= hx i _ (realCube_mono ((min_le_right ..).trans (min_le_left ..)) hq)
    have he:= h i (rpart p) p (cube_mono ((min_le_left ..).trans (min_le_left ..)) (mem_cube_real hq hz)) ((thin_dist hz hu).trans_lt (((min_le_right ..).trans (min_le_right ..)).trans_lt (half_lt_self hρ)))
    have hr:= (Complex.abs_re_le_norm _).trans_lt he
    rw [Complex.sub_re] at hr; linarith [(abs_lt.mp hr).1]
  refine ⟨z,Real.sqrt C,hz,Real.sqrt_pos.mpr hc,fun i=>⟨fun p hv=>?_,fun p hv=> ?_⟩⟩
  · exact (Complex.differentiableAt_sqrt (show B i p∈ Complex.slitPlane from Or.inl (he i p hv))).comp p ((H i).hol p (cube_mono ((min_le_left ..).trans (min_le_right ..)) hv))
  have hm := (H i).bound p (cube_mono ((min_le_left ..).trans (min_le_right ..)) hv)
  rw [mul_one]; apply le_of_sq_le_sq _ (by positivity)
  rw [Real.sq_sqrt hc.le]; dsimp only; rw [pow_two,← norm_mul,cmag (norm_pos_iff.mp ((he i p hv).trans_le (Complex.re_le_norm _)))]
  simpa using hm
end YM.QCD.Flume
