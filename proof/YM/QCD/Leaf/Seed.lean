import YM.QCD.Leaf.Cord

/-! # Saturation tube width ξ² -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf
open Run Kit Lat Function Finset Lattice RG Rudder Filter Matrix Metric Classical Paths
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {n : Side}
namespace LeafM
variable (W: Slot) (x: Site n)
def qmark := wrap n W.offset+x
def leafC (P: Pulse n)(i:su.ColorIndex):= stringC i ((1/2:ℂ) • (pursueP P x (torch W)-pursueP P (stop x (torch W)) (Lattice.reverse (torch W))))
def purseC (P:Pulse n):ℂ:=∑ i:su.ColorIndex, leafC { W with walk:=[]} (qmark W x) P i ^2
def leafSat (t:ℝ)(P:Pulse n)(i:su.ColorIndex):ℂ:= (t:ℂ)^2/((t:ℂ)^2+purseC W x P) * leafC W x P i
def pulp (t:ℝ)(U:Grid n):su.Color:= (t^2/(t^2+‖W.atSite U x‖^2)) • W.atSite U x
lemma pinning (U:Grid n)(i:su.ColorIndex): leafC W x (settled U) i=((W.atSite U x i:ℝ):ℂ):=by
  simp only [leafC,pursuit,travel_reverse,price_c,recognized]; rfl
lemma leaves (U:Grid n): purseC W x (settled U)=(↑(‖W.atSite U x‖^2):ℂ):=by
  unfold purseC; simp_rw [pinning]
  let P:Slot:= { W with walk:=[] }
  have hp : ‖P.atSite U (qmark W x)‖=‖W.atSite U x‖ := by unfold Slot.atSite Slot.eval; rw [Gauge.norm_adjoint,Gauge.norm_adjoint]; unfold faceValue; rw [travel_at,travel_at]; simp [P,Slot.offset,qmark,stop]
  rw [← hp,EuclideanSpace.norm_sq_eq]; simp [P,Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
lemma connecting (U:Grid n)(t i): leafSat W x t (settled U) i=(↑((pulp W x t U) i):ℂ):=by
  rw [leafSat,pinning,leaves,pulp,PiLp.smul_apply,smul_eq_mul]; push_cast; rfl
lemma same (U: Grid n)(g: Frame n) : su.chord (trueF W x (gauge g U))=su.chord (trueF W x U):=by simp [trueF,face_gauge]
lemma gaugeP (U:Grid n)(t:ℝ)(g : Lat.Frame n): pulp W x t (gauge g U) = su.adjoint (g x) (pulp W x t U):=by unfold pulp; rw [Bloom.slotRot,su.norm_adjoint,map_smul]
lemma uses (U:Grid n)(g : Grid n) (hp : Agrees (YM.Next.Scheduling.Wages.walkCuts W x: Set (Site n)) U g)(t): pulp W x t U=pulp W x t g:=by
  unfold pulp
  have hl : Agrees (W.stencil: Set Cover) (expandAt x U) (expandAt x g):= fun p ha hh=> hp (wrap n p.1+x,p.2) (mem_image_of_mem _ ha) (by
     have hg := mem_image_of_mem (fun y=> wrap n y+x) (show p.1+step p.2∈W.stencil from hh); simp only [map_add,wrap_step] at hg; convert! hg using 1; all_goals try (simp [add_assoc,add_left_comm,add_comm]))
  rw [show W.atSite U x=W.atSite g x from W.covered _ _ hl]

lemma skull (U: Grid n)(i): ‖leafC W x (settled U) i‖ ≤ ‖W.atSite U x‖:=by
  rw [pinning,Complex.norm_real,Real.norm_eq_abs,← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul])
lemma growing (i): Differentiable ℂ (fun P=> leafC W x P i):=by
  obtain ⟨K,h⟩:= string_lin i
  simp_rw [leafC,← h]; exact K.differentiable.comp (((reachP x _).sub (reachP (stop x (torch W)) _)).const_smul (R:=ℂ) (1/2:ℂ))

lemma fnTrace : Differentiable ℂ (purseC W x) := Differentiable.fun_sum (fun i _=> ((growing _ _ i)).pow _)
lemma traceGap : ∃ E:ℝ,0<E∧∀ (n : Side)(W:Slot)(x:Site n)(P:Pulse n)(U:Grid n)(δ : ℝ),δ ≤1 → ‖P-settled U‖< δ → ‖purseC W x P-purseC W x (settled U)‖ ≤ E*δ:=by
  choose K hK using string_lin
  let E:= 1+∑ i:su.ColorIndex, (‖K i‖*(3^4+3^4))^2
  have hE:0<E:=by unfold E; positivity
  refine ⟨E,hE,fun n W x P U δ hz h=>?_⟩
  have hv : P∈ ball (settled U) ((2:ℝ)/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact h.trans_le (hz.trans_eq (by norm_num))
  have hm (Y : Pulse n)(hy:Y∈ball (settled U) 2):‖purseC W x Y‖ ≤ E:=by
    rw [Metric.mem_ball,dist_eq_norm] at hy
    have he (w:Walk)(p:Site n)(ht:w.length=4) : ‖pursueP Y p w‖ ≤ 3^4:= (pose Y U w p hy.le).trans (le_of_eq (by rw [ht]; norm_num))
    refine le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (s:=univ) (g:=fun i:su.ColorIndex=> (‖K i‖*(3^4+3^4))^2) (fun i _=> ?_))) (le_add_of_nonneg_left (by norm_num))
    rw [norm_pow]; gcongr; unfold leafC; rw [← hK]; apply ((K i).le_opNorm _).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg (K i)); rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans ((norm_sub_le ..).trans (add_le_add (he _ _ rfl) (he _ _ rfl)))
  exact (lastwig _ (show 0<(2:ℝ) by norm_num) (fun i _=>fnTrace W x i) hm hv).trans (by simpa using mul_le_mul_of_nonneg_left h.le hE.le)

lemma file (σ:ℝ)(hσ:0<σ):∃ C δ:ℝ, 1≤ C ∧ 0<δ∧∀ (ξ:ℝ),0<ξ→ξ≤1→ ∀ (n: Side)(W:Slot)(x:Site n)(P:Pulse n)(i:su.ColorIndex), P∈Kingdom n (δ*ξ^2) →
      DifferentiableAt ℂ (fun Z=> leafSat W x ξ Z i) P ∧ ‖leafSat W x ξ P i‖ ≤ (C*ξ)*Real.exp (σ*W.length):=by
  -- buy analytic estimate via Cauchy for leafC width b; avoids path powers
  choose K hK using string_lin
  let B:ℝ:=∑ i:su.ColorIndex, ‖K i‖
  have hB:0≤ B:=by unfold B; positivity
  let w:= Real.exp (σ/2)-1
  have hw:0<w:=sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  obtain ⟨E,hE,cashY⟩:= traceGap
  let δ:= min 1 (min (w/2) (1/(2*E)))
  have ht: 0 < δ:=lt_min one_pos (lt_min (by positivity) (by positivity))
  let X:= B*2/(w/2)
  have hx : 0 ≤ X:=by unfold X; positivity
  let C:= 2+2*X; have hC:1≤C:=by unfold C; linarith
  refine ⟨C,δ,hC,ht,fun ξ hξ hc n W x P i hp=>?_⟩
  obtain ⟨U,hU⟩:= Set.mem_iUnion.mp hp
  have hu: ‖P-settled U‖ < δ*ξ^2:=by simpa [Metric.mem_ball,dist_eq_norm] using hU
  have he:δ*ξ^2 ≤ δ:=mul_le_of_le_one_right ht.le (pow_le_one₀ hξ.le hc)
  have hu₀:δ*ξ^2≤ξ:=by calc
    _ ≤ 1*ξ^2:=mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)
    _ ≤ _:=by nlinarith
  let r:=‖W.atSite U x‖
  let Q (z : Pulse n):ℂ:= (ξ:ℂ)^2+purseC W x z
  have hr:0≤r:=norm_nonneg _
  have hi₀:Q (settled U)= (((ξ^2+r^2):ℝ):ℂ):=by unfold Q; rw [leaves]; push_cast; rfl
  have hg:= cashY n W x P U _ (he.trans (min_le_left ..)) hu
  have hm: E*δ≤1/2 :=by
    apply (mul_le_mul_of_nonneg_left (show δ≤1/(2*E) from (min_le_right ..).trans (min_le_right ..)) hE.le).trans; field_simp; linarith
  have hh : ‖Q (settled U)‖ - ‖Q P‖ ≤ ξ^2/2:= (norm_sub_norm_le ..).trans (by
    rw [norm_sub_rev, show Q P-Q (settled U)=purseC W x P - purseC W x (settled U) by unfold Q; abel]; refine hg.trans ?_; linarith only [mul_le_mul_of_nonneg_right hm (show 0≤ ξ^2 from sq_nonneg ξ)])
  rw [hi₀,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at hh
  have hQ : ξ^2+r^2≤2*‖Q P‖:=by nlinarith
  have hq:0 < ‖Q P‖:=by nlinarith
  refine ⟨?_,?_⟩
  · unfold leafSat; simp_rw [div_eq_mul_inv]; have hy: DifferentiableAt ℂ (fun a=> (Q a)⁻¹) P:= DifferentiableAt.inv (h:=Q) ((differentiableAt_const _).add (fnTrace W x P)) (norm_pos_iff.mp hq); exact ((differentiableAt_const _).mul hy).mul (growing W x i P)
  let v:=Real.exp (σ*W.length)
  let f : Pulse n→ℂ:= fun Z=> leafC W x Z i
  have ha (Z) (hz: Z∈ball (settled U) w) : ‖f Z‖ ≤ B*2*v:=by
    have hH: ‖Z-settled U‖ ≤ w:= by simp only [Metric.mem_ball,dist_eq_norm] at hz; exact hz.le
    have hs W' y (hx : List.length W' ≤ 2*W.length): ‖pursueP Z y W'‖≤ v:=by
      apply (pose Z U W' y hH).trans; apply (pow_le_pow_right₀ (le_add_of_nonneg_right hw.le) hx).trans; unfold w v; rw [add_sub_cancel,← Real.exp_nat_mul]; refine le_of_eq ?_; congr 1; push_cast; ring
    unfold f leafC; rw [← hK]; refine ((K i).le_opNorm _).trans ?_; rw [norm_smul]; simp only [norm_div,norm_one, show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    have hN:= hs (torch W) x (length_max W); have hG := hs (Lattice.reverse (torch W)) (stop x (torch W)) (by simpa only [Lattice.reverse,List.length_map,List.length_reverse] using length_max W)
    apply le_trans (mul_le_mul (single_le_sum (s:=univ) (f:=fun i=>‖K i‖) (fun j _=> norm_nonneg (K j)) (mem_univ i)) (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hN hG)) (show 0≤ 1/(2:ℝ) by norm_num)) (by positivity) hB); change B*(1/2*(v+v))≤ _; have hj:0≤v:= (Real.exp_pos _).le; nlinarith
  have hf : ‖f P‖ ≤ X*v*ξ+r :=by
    have hV:P∈ ball (settled U) (w/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact hu.trans_le (he.trans ((min_le_right ..).trans (min_le_left ..)))
    have hD:=lastwig (V:=P) f hw (fun a _=> growing W x i a) ha hV
    have hJ:‖f P‖-‖f (settled U)‖ ≤ X*v*ξ:=le_trans ((norm_sub_norm_le ..).trans hD) (by rw [show B*2*v/(w/2)=X*v by unfold X; ring]; exact mul_le_mul_of_nonneg_left (hu.le.trans hu₀) (by unfold v; positivity))
    have hn:‖f (settled U)‖≤ r:=skull W x U i; linarith
  unfold leafSat; rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hξ.le]; apply le_trans (mul_le_mul_of_nonneg_left hf (by positivity))
  change ξ^2/‖Q P‖*(X*v*ξ+r)≤C*ξ*v
  have hv:1≤v:=Real.one_le_exp (by positivity)
  rw [mul_add]
  have hX: ξ^2/ ‖Q P‖ ≤ 2:= (div_le_iff₀ hq).mpr (by nlinarith)
  have hz : ξ^2/ ‖Q P‖ * r ≤ ξ:=by rw [div_mul_eq_mul_div,div_le_iff₀ hq]; nlinarith [mul_le_mul_of_nonneg_left hQ hξ.le, mul_nonneg hξ.le (sq_nonneg (ξ-r))]
  unfold C; nlinarith only [mul_le_mul_of_nonneg_right hX (show 0≤X*v*ξ by positivity), hz, hv,hξ, mul_le_mul_of_nonneg_right hv hξ.le]
end LeafM
end YM.QCD.Leaf
