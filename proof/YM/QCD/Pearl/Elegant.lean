import YM.QCD.Pearl.Angle

/-! # Uniform sectors at momenta of size k -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {j:ℕ}{p k:Momentum} {r ρ C c ε : ℝ} {F : Momentum→Para}
lemma diremp (hj:2≤j):∃ C r:ℝ,0<C∧0<r∧∀ v:Train j,∀ p∈cube r,DifferentiableAt ℂ (Dir v) p ∧ ‖Dir v p‖≤ C := by
  let G (i:Train j)(a:Axis)(p:Momentum):=(Dir i p).2 a
  have hh:=Dir_budget hj (id : Train j→ Train j)
  obtain ⟨r,c,hp,hc,H⟩:=hh.scalar
  obtain ⟨z,Z,hz,hZ,K⟩ : ∃ z Z:ℝ,0<z∧0<Z∧ ∀ a:Axis, ∀ i:Train j, SafeCube z Z (G i a):=by
    apply staple
    · intro a; obtain ⟨t,V,ht,hv,H⟩:=hh.vector a; exact ⟨t,V,ht,hv,fun i=>by simpa only [mul_one,id_eq] using H i⟩
    intro i _ _ _ _ h hv hp hb j; exact (h j).mono hv hb -- check
  refine ⟨max c Z,min r z,lt_max_of_lt_left hc,lt_min hp hz,fun v p hv=> ?_⟩
  have hx := cube_mono (min_le_left ..) hv; have hu:=cube_mono (min_le_right ..) hv
  refine ⟨((H v).hol p hx).prodMk (differentiableAt_pi.mpr fun i=> (K i v).hol p hu), max_le ?_ ?_⟩
  · exact (H v).bound p hx|>.trans (by rw [mul_one]; exact le_max_left ..)
  refine le_trans (pi_norm_le_iff_of_nonneg hZ.le |>.mpr ?_) (le_max_right ..); exact fun i=> (K i v).bound _ hu

def shaft (p:Momentum):Para:= (0,p)
lemma nerve (p:Momentum):‖shaft p‖=‖p‖:=by simp[shaft,Prod.norm_def]
lemma nerve0 (hp:p∈baseCube): ‖p‖^2≤ ‖quad (shaft p)‖:=by
  have he: Native (shaft p):=⟨star_zero _,hp.1⟩
  rw [he.magnitude,he.quad_m,Complex.ofReal_re]; apply (vector_max _).trans; simp only [shaft,Complex.zero_re,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_add];
  unfold lengthSq; refine sum_le_sum fun i _=> ?_; rw [← cast_real hp.1 i]; simp only [Real.norm_eq_abs,Complex.norm_real,sq_abs,shaft,Complex.ofReal_re]; rfl
structure Pinch (F:Momentum→Para)(r c C:ℝ): Prop where
 hr : 0<r
 hc : 0<c
 hC : 0<C
 hD (p:Momentum) (_:p∈cube r): DifferentiableAt ℂ F p
 bounded (p:Momentum)(_:p∈cube r): ‖F p‖≤ C
 phase (p:Momentum)(_:p∈baseCube): c*‖p‖^2≤ ‖quad (F p)‖
 aligns : F 0=0
 firm (v:Momentum): dew v F 0=shaft v
lemma boot (hj:2≤j): ∃ r c C,∀ v:Train j,Pinch (Dir v) r c C:=by
  obtain ⟨z,Z,hz,hZ,H⟩:= diremp hj; obtain ⟨u,c,hp,hu,hc,L⟩:=size_q hj
  refine ⟨Z,c,z,fun v=> ⟨hZ,hc,hz,fun _ hv=>(H v _ hv).1,fun i hi=>(H v i hi).2,fun p hv=> ?_,Dir_nil _,steamP hj⟩⟩
  exact (mul_le_mul_of_nonneg_left (vector_max p) hc.le).trans ((L v _ (base_subset_realCube hp hv)).1.trans (Complex.re_le_norm _))
lemma adder (hp:0<r): ∃ C, Pinch shaft r 1 C:=by
  let C:ℝ:= Real.pi+2*r; refine ⟨C,hp,one_pos,by unfold C; positivity,fun p _=>(differentiableAt_const (0:ℂ)).prodMk differentiableAt_id,fun p he=> ?_,fun p h=> ?_,rfl,fun p=>?_⟩ -- prod uses constructor
  -- check
  · rw [nerve]; refine (pi_norm_le_iff_of_nonneg (by unfold C; positivity)).mpr (fun i=>?_)
    have h:= he.1 i; have hh:=he.2 i; unfold C; linarith [Complex.norm_le_abs_re_add_abs_im (p i)]
  · rw [one_mul]; exact nerve0 h
  let L:= ContinuousLinearMap.inr ℂ ℂ Momentum; exact dewp L ..
lemma Pinch.foil (h:Pinch F r c C) (hp:p∈baseCube): ball p (r/2) ⊆ cube r:= by
  have hz:=h.hr; apply (ball_subset_ball (show r/2≤ r-r/2 by linarith)).trans (ball_inside_cube ?_); exact mem_cube_real (base_subset_realCube (half_pos hz) hp) (half_pos hz)
lemma Pinch.reduce (h:Pinch F r c C){D' Y : ℝ}(hr':0<ρ)(hr:ρ≤r)(hp:0<D')(hs:D'≤c)(he:C≤Y):Pinch F ρ D' Y:= ⟨hr',hp,h.hC.trans_le he,fun x hx=> h.hD _ (cube_mono hr hx),fun x hx=>(h.bounded _ (cube_mono hr hx)).trans he,fun p hp=>(mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans (h.phase p hp), h.aligns,h.firm⟩
namespace Pinch
variable (h: Pinch F r c C)
include h
-- budgets only depending displayed params
/-- large momenta also fit second order -/
def baseK (r C:ℝ) := (C/(r/2/2)/(r/2/2/2)+ C/(r/2/2/2)^2+ (r/2/2/2)⁻¹)
lemma lifting (hp:p∈cube r): ‖F p-shaft p‖ ≤ baseK r C*‖p‖^2:=by
  let u:= r/2/2/2
  have hr:= h.hr; have hu : 0<u:=by unfold u; positivity
  have hc:=h.hC
  by_cases he : ‖p‖<u
  · have hh := h.foil Flume.W0
    have ht := versa F (half_pos hr) (0:Momentum) (fun x hx=> h.hD _ (hh hx)) (fun x hx=> h.bounded _ (hh hx)) _ (mem_ball_zero_iff.mpr he);
    rw [sub_zero,h.firm,h.aligns,sub_zero] at ht; apply ht.trans; unfold baseK;
    exact mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))) (sq_nonneg _)
  have hv : u≤‖p‖:=not_lt.mp he
  apply (norm_sub_le _ _).trans; rw [nerve];
  have hx : C ≤ C/u^2*‖p‖^2:= (le_of_eq (div_mul_cancel₀ C (pow_ne_zero _ hu.ne')).symm).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hv _) (by positivity))
  have hy : ‖p‖ ≤ u⁻¹*‖p‖^2:=by rw [inv_mul_eq_div,le_div_iff₀ hu,pow_two]; exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
  apply (add_le_add ((h.bounded p hp).trans hx) hy).trans; unfold baseK; rw [add_mul,add_mul]; exact add_le_add_left (le_add_of_nonneg_left (by positivity)) _

def highwall (r c C:ℝ):ℝ := 2*Real.pi -- unused

lemma boundK : 0<baseK r C:= by have hp:= h.hr; have hc:=h.hC; unfold baseK; positivity
lemma near (hp:p∈ball k (ε*‖k‖)) (he : ε≤1): ‖p‖≤ 2*‖k‖:=by
  have hh := (norm_sub_norm_le p k).trans (show ‖p-k‖≤ε*‖k‖ by rw [mem_ball,dist_eq_norm] at hp; exact hp.le)
  linarith [mul_le_mul_of_nonneg_right he (norm_nonneg k)]
lemma Far (hp:p∈cube r) (hk:k∈baseCube) (ht:‖p‖≤2*‖k‖) :‖F p‖≤ (4*baseK r C*Real.pi+2)*‖k‖:=by
  have he:=(norm_sub_norm_le _ _).trans (h.lifting hp)
  rw [nerve] at he; have hr: 0<baseK r C := h.boundK
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht 2) hr.le; nlinarith only [he,ht,hh,mul_le_mul_of_nonneg_left (cap_base hk) (show 0≤baseK r C*‖k‖ from by positivity)]
lemma leagueX (hp:p∈ball k (ε*‖k‖))(hk:k∈baseCube)(ht:ε*‖k‖≤ r/2/2): ‖F p-F k‖≤ C/(r/2/2)*(ε*‖k‖):= by
  have he:= h.foil hk
  refine (Run.lastwig F (half_pos h.hr) (fun i hi=> h.hD _ (he hi)) (fun i hi=> h.bounded _ (he hi)) (ball_subset_ball ht hp)).trans (mul_le_mul_of_nonneg_left (by rw [mem_ball,dist_eq_norm] at hp; exact hp.le) ?_); have hr:=h.hr; have hh:=h.hC; positivity
end Pinch
end YM.QCD.Pearl
