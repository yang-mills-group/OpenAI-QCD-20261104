import YM.QCD.Leaf.Bud
/-! Analytic continuation on scale of regulator saturation, not its square. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Run Kit Lat Function Finset Lattice RG Rudder Filter Matrix Metric Classical Paths
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {n : Side}
lemma chordB_num (U:Grid n)(W:Slot)(x:Site n) : ‖({ W with walk:=[]} : Slot).atSite U (qmark W x)‖=‖W.atSite U x‖:=by unfold Slot.atSite Slot.eval; rw [Gauge.norm_adjoint,Gauge.norm_adjoint]; unfold faceValue; rw [travel_at,travel_at]; simp [Slot.offset,qmark,stop]
lemma scaleL_pay (i:su.ColorIndex) : ∃ E:ℝ,0<E∧∀ (n:Side)(W:Slot)(x:Site n)(P:Pulse n)(U:Grid n)(δ:ℝ),δ ≤1 → ‖P-settled U‖< δ → let Q:=leafC ({ W with walk:=[]} : Slot) (qmark W x); ‖Q P i-Q (settled U) i‖ ≤ E*δ:=by
  obtain ⟨K,hK⟩:= string_lin i
  let E:= 1+‖K‖*(3^4+3^4)
  have hE:0<E:=by unfold E; positivity
  refine ⟨E,hE,fun n W x P U δ hz h=>?_⟩; intro Q
  have hv : P ∈ ball (settled U) ((2:ℝ)/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact h.trans_le (hz.trans_eq (by norm_num))
  have hm (Y : Pulse n)(hy:Y∈ball (settled U) 2):‖Q Y i‖ ≤ E:=by
    rw [Metric.mem_ball,dist_eq_norm] at hy
    have he (w:Walk)(p:Site n)(ht:w.length=4) : ‖pursueP Y p w‖ ≤ 3^4:= (pose Y U w p hy.le).trans (le_of_eq (by rw [ht]; norm_num))
    unfold Q leafC; rw [← hK]; apply ((K).le_opNorm _).trans; unfold E; apply le_trans _ (le_add_of_nonneg_left (by norm_num)); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans ((norm_sub_le ..).trans (add_le_add (he _ _ rfl) (he _ _ rfl)))
  exact (lastwig (fun Z=>Q Z i) (show 0<(2:ℝ) by norm_num) (fun i _=> growing ..) hm hv).trans (by simpa using mul_le_mul_of_nonneg_left h.le hE.le)
lemma wavePay : ∃ E:ℝ,1<E ∧∀ (n : Side)(W:Slot)(x:Site n)(P:Pulse n)(U:Grid n)(δ : ℝ),δ ≤1 → ‖P-settled U‖< δ → ‖purseC W x P-purseC W x (settled U)‖ ≤ E*(‖W.atSite U x‖*δ + δ^2):=by
  choose F hF H using scaleL_pay
  let C i:=2+2*F i+(F i)^2; let E:=2+∑ i:su.ColorIndex,C i
  have he : 1<E:=by
    unfold E; have h:0≤ ∑ i:su.ColorIndex,C i:=sum_nonneg fun i _=> by unfold C; have hh:=hF i; positivity
    linarith only [h]
  refine ⟨E,he, fun n W x P U δ hz h=>?_⟩
  let r:= ‖W.atSite U x‖; have hr:0≤r:=norm_nonneg _; have ht:0<δ:=lt_of_le_of_lt (norm_nonneg _) h
  unfold purseC; rw [← sum_sub_distrib]; apply (norm_sum_le ..).trans; let V:=leafC ({W with walk:=[]} : Slot) (qmark W x); refine le_trans (sum_le_sum (g:=fun i=> C i*(r*δ+δ^2)) (s:=univ) (fun j _=> ?_)) ?_
  · let y:=V P j; let v:=V (settled U) j; change ‖y^2-v^2‖≤ _; have hk : ‖y-v‖≤F j*δ:= H j n W x P U δ hz h
    have hm : ‖v‖≤r:=(skull ..).trans_eq (chordB_num ..); have hu : ‖y‖≤r+F j*δ:=by linarith [norm_sub_norm_le y v]
    rw [show y^2-v^2=(y-v)*(y+v) by ring,norm_mul]; apply (mul_le_mul hk ((norm_add_le ..).trans (add_le_add hu hm)) (norm_nonneg _) (by positivity [hF j])).trans; unfold C; have hh:=hF j; nlinarith [show 0≤F j*δ^2 by positivity,show 0≤(2+F j^2)* (r*δ) by positivity]
  rw [← sum_mul]; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) (by positivity)
lemma skiff (σ:ℝ)(hσ:0<σ):∃ C δ:ℝ, 1≤ C ∧ 0<δ∧∀ (ξ:ℝ),0<ξ→ξ≤1→ ∀ (n: Side)(W:Slot)(x:Site n)(P:Pulse n)(i:su.ColorIndex), P∈Kingdom n (δ*ξ) →
      DifferentiableAt ℂ (fun Z=> leafSat W x ξ Z i) P ∧ ‖leafSat W x ξ P i‖ ≤ (C*ξ)*Real.exp (σ*W.length):=by
  -- buy analytic estimate via Cauchy for leafC width b; avoids path powers
  choose K hK using string_lin
  let B:ℝ:=∑ i:su.ColorIndex, ‖K i‖
  have hB:0≤ B:=by unfold B; positivity
  let w:= Real.exp (σ/2)-1
  have hw:0<w:=sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  obtain ⟨E,hE,cashY⟩:= wavePay
  have hXp:0<E:=zero_lt_one.trans hE
  let δ:ℝ:= min 1 (min (w/2) (1/(4*E)))
  have ht: 0 < δ:=lt_min one_pos (lt_min (by positivity) (by positivity))
  let X:= B*2/(w/2)
  have hx : 0 ≤ X:=by unfold X; positivity
  let C:= 2+2*X; have hC:1≤C:=by unfold C; linarith
  refine ⟨C,δ,hC,ht,fun ξ hξ hc n W x P i hp=>?_⟩
  obtain ⟨U,hU⟩:= Set.mem_iUnion.mp hp
  have hu: ‖P-settled U‖ < δ*ξ:=by simpa [Metric.mem_ball,dist_eq_norm] using hU
  have he:δ*ξ ≤ δ:=mul_le_of_le_one_right ht.le hc
  have hu₀:δ*ξ≤ξ:=by calc
    _ ≤ 1*ξ:=mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)
    _ ≤ _:=by nlinarith
  let r:=‖W.atSite U x‖
  let Q (z : Pulse n):ℂ:= (ξ:ℂ)^2+purseC W x z
  have hr:0≤r:=norm_nonneg _
  have hi₀:Q (settled U)= (((ξ^2+r^2):ℝ):ℂ):=by unfold Q; rw [leaves]; push_cast; rfl
  have hg:= cashY n W x P U _ (he.trans (min_le_left ..)) hu
  have hm: E*δ≤1/4 :=by
    apply (mul_le_mul_of_nonneg_left (show δ≤1/(4*E) from (min_le_right ..).trans (min_le_right ..)) hXp.le).trans; field_simp; linarith
  have hh : ‖Q (settled U)‖ - ‖Q P‖ ≤ (ξ^2+r^2)/2:= (norm_sub_norm_le ..).trans (by
    rw [norm_sub_rev, show Q P-Q (settled U)=purseC W x P - purseC W x (settled U) by unfold Q; abel]; refine hg.trans ?_
    have hD':δ≤1:=min_le_left ..; have hh':0≤ r*ξ+ξ^2:=by positivity
    calc
       _ = E*δ*(r*ξ+ δ*ξ^2):=by unfold r; ring
       _ ≤ 1/4*(r*ξ+ξ^2):=by gcongr; exact mul_le_of_le_one_left (by positivity) hD'
       _ ≤ _:=by nlinarith only [sq_nonneg (ξ-r),sq_nonneg ξ,sq_nonneg r])
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
end YM.QCD.Leaf.LeafM
#print axioms YM.QCD.Leaf.LeafM.skiff
