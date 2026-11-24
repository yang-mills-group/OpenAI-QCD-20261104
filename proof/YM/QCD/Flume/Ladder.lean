import YM.QCD.Flume.Factor

/-! # the quotients can be chosen analytic uniformly positive on the entire real cube -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}
lemma re_cost {w : ι→ℝ} {F : ι → Cover → ℝ} (h : SoundTape w F): Moderate w fun i=> RRead (F i):=by
  obtain ⟨η,C,he,hc,h⟩:=h
  refine ⟨η/2,C,by positivity,hc,fun i=>⟨fun p hp=>(Work.F07.readDeriv (budgeted_real (h i)) (by linarith) (show η/2<η by linarith) hp.1).1,fun p hp=>?_⟩⟩
  exact (budgeted_real (h i)).estimate _ (fun a=> (hp.1 a).le.trans (by linarith))
lemma sensitivity (hj : 2≤j) (v : ι→Train j) (a : ι→Axis) : Moderate (fun _ : ι => 1) fun i=> steps (v i) (a i):=by
  have he : Moderate (fun _ : ι => 1) (fun i p=> mode p (step (a i))):=by
    refine ⟨zone, Real.exp domainRadius,zone_pos,Real.exp_pos _,fun i=>⟨fun p _=>?_,fun p h=> ?_⟩⟩
    · unfold mode; fun_prop
    dsimp only; rw [mul_one,Exterior.factor,Complex.norm_exp]; apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (by rw [norm_mul,Complex.norm_I,one_mul]; exact zone_in_disk p h _)
  simpa only [steps,one_mul] using! he.neg.mul (re_cost (income_a hj v a 2))
lemma clinical (hj : 2 ≤ j) (v : Train j) (a : Axis) {p : Momentum} (hp : p∈baseCube): ContinuousAt (steps v a) p:=by obtain ⟨η,C,hθ,hc,h⟩:= sensitivity hj (fun _ : Unit=>v) fun _=>a; exact ((h ()).hol _ (mem_cube_real (base_subset_realCube hθ hp) hθ)).continuousAt
lemma stair_stable (v : Train j) (a : Axis): Stable (steps v a):=by
  intro p x; unfold steps RRead; rw [mode_phase,mode_periodic,mul_one,Laurent.periodic]
lemma powerD (p : Momentum) (a : Axis) (hp : physical p) : plusD p a=(↑(‖chip (p a)‖^2):ℂ):=by
  have hh : chip ((-p) a)=star (chip (p a)):=by rw [flip_chip,show star (p a)=p a from congr_fun hp a]; rfl
  rw [plusD,hh,Complex.star_def,Complex.mul_conj,← Complex.sq_norm]
lemma W0 : (0: Momentum)∈baseCube:=⟨by simp [physical],fun i=>by simp [Real.pi_pos.le]⟩
lemma Wb {p:Momentum} (hp : p∈baseCube): -p∈baseCube:=bank_acts _ hp ⟨1,fun _=>true⟩
lemma stitch (hj : 2 ≤ j) (v : Train j) (a : Axis) {p : Momentum} (hp : p∈baseCube):
    star (steps v a p)=steps v a p ∧ steps v a (-p)=steps v a p:=by
  have hh (n):∀ (p : Momentum),p∈baseCube→star (hemi v (Tuck n p))=hemi v (Tuck n p):=fun p hp=>(native_dir _ _ (shelve _ _ zone_pos (base_subset_realCube zone_pos hp)).1).1
  have he (n):∀ p: Momentum, p∈baseCube→ hemi v (Tuck n (-p))=hemi v (Tuck n p):=fun p hp=> (hh n _ (Wb hp)).symm.trans (customary v n p (base_subset_realCube zone_pos hp))
  have hq (p : Momentum) (hp : p∈baseCube) (hi : Exterior.q p a≠0):plusD p a≠0:=by
    rw [powerD p a hp.1]; exact_mod_cast (pow_pos (norm_pos_iff.mpr (show chip (p a)≠0 from hi)) 2).ne'
  constructor
  · apply renew_q (fun p=>star (steps v a p)) (steps v a) a _ _ _ p hp
    · exact fun p hp=> (clinical hj v a hp).star
    · exact fun p hp=>clinical hj v a hp
    intro p hp hi; apply mul_left_cancel₀ (hq p hp hi); have hr:=congr_arg star (second_rise hj v a p hp)
    change _ * star _= _
    have hv : star (plusD p a)=plusD p a:=by rw [powerD p a hp.1]; simp
    rw [star_mul, hv,star_sub,hh _ p hp,hh _ p hp,← second_rise hj v a p hp,mul_comm] at hr; exact hr
  apply renew_q (fun p=>steps v a (-p)) (steps v a) a _ _ _ p hp
  · exact fun p hp=> (clinical hj v a (Wb hp)).comp (continuous_neg.continuousAt)
  · exact fun p hp=>clinical hj v a hp
  intro p hp hi; apply mul_left_cancel₀ (hq p hp hi); have hr:=second_rise hj v a (-p) (Wb hp)
  rw [show plusD (-p) a=plusD p a by simp [plusD,mul_comm],he _ p hp,he _ p hp,← second_rise hj v a p hp] at hr; exact hr

lemma positive_home (hj : 2≤j) : ∃ c:ℝ,0<c∧∀ (v : Train j) a,c≤(steps v a 0).re:=by
  obtain ⟨η,c,hp,hη,hc,H⟩:=size_q hj
  have hv := meter.high_pos
  refine ⟨c/(meter.high^2),by positivity,fun v a=>?_⟩
  let u (t : ℝ): Momentum:= update 0 a (t:ℂ)
  have he : u 0=0:=by unfold u; simp
  have hL : Continuous u:=by apply continuous_pi; intro i; by_cases h:i=a <;> simp [u,h,Complex.continuous_ofReal]; exact continuous_const
  let N:=𝓝[>] (0:ℝ)
  have hh: Tendsto u N (𝓝 (0 : Momentum)):= he ▸ hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hy : Tendsto (fun t=>(steps v a (u t)).re) N (𝓝 (steps v a 0).re) := Complex.continuous_re.continuousAt.tendsto.comp ((clinical hj v a W0).tendsto.comp hh)
  refine ge_of_tendsto hy ?_
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),mem_nhdsWithin_of_mem_nhds (gt_mem_nhds Real.pi_pos)] with t ht hx
  have ht' : 0<t:=ht; have hu:t<Real.pi:=hx
  have h : u t∈baseCube:=by
    refine ⟨(physical_iff _).mpr ?_,?_⟩
    · intro i; by_cases h:i=a <;> simp [u,h]
    intro i; by_cases h:i=a
    · simpa [u,h,abs_of_pos ht'] using hu.le
    simp [u,h,Real.pi_pos.le]
  have hz := second_rise hj v a _ h
  have hn : Tuck a.val (u t)=0:=by
    funext i; by_cases h:i=a; · subst i; simp [Tuck]
    simp [Tuck,u,h]
  have hm : Tuck (a.val+1) (u t)=u t:=by funext i; by_cases h:i=a <;> simp [Tuck,h,u]
  have hX : plusD (u t) a=(↑(‖chip (t:ℂ)‖^2):ℂ):=by rw [powerD _ _ h.1]; simp only [u, update_self]
  rw [hm,hn,show hemi v 0=0 by simp [hemi],sub_zero,hX] at hz
  have hQ : lengthSq (u t)=t^2:=by
    unfold lengthSq; rw [sum_eq_single a]; simp [u,Real.norm_of_nonneg ht'.le]; · intro b _ hb; simp [u,hb]
    simp
  have hs : c*t^2≤ ‖chip (t:ℂ)‖^2 * (steps v a (u t)).re:=by
    have hj := (H v _ (base_subset_realCube hp h)).2; change c* _ ≤ (hemi v _).re at hj; rw [← hz,hQ,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hj; exact hj
  have hF:= lt_of_lt_of_le (show 0<c*t^2 by positivity) hs
  have hs' := pos_of_mul_pos_right hF (sq_nonneg _)
  rw [div_le_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ (pow_pos ht' 2)
  have he : ‖chip (t:ℂ)‖≤meter.high*t:=by simpa only [Complex.norm_real,Real.norm_of_nonneg ht'.le] using meter.above ((t:ℂ)) (by simpa only [Complex.norm_real,Real.norm_of_nonneg ht'.le] using (hu.le.trans (by unfold domainRadius; linarith [Real.pi_pos])))
  exact hs.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) he 2) hs'.le).trans (le_of_eq (by ring)))
end YM.QCD.Flume
