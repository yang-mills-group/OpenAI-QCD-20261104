import YM.QCD.Pearl.Burst

/-!
# absorbing small and outside modes (data all post-L)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p : Site n} {i : Axis} {κ η c s q b B r ε K : ℝ}{j:ℕ}{F : Momentum→Para}{A W: Shine→Bundle}

-- all shifted vertices physically in strip, no complex tube needed when bounding absolute.
def lowCost (r c B b s:ℝ):= (Fintype.card Fiber:ℝ)*((2*purse r c B)^2*b^2+(2*purse r c B)*s)
lemma low_bound {p q:Site n} {z} {v:Train j}(hw: Wall η b A)(hQ:Wall η s W)(he:0<η)(h : Pinch (Dir v) r c B)(e:Bright r c B ε)(hp:physical z)(hg: Fans q z)(htb: beamH n≤1)(hk:tuning p+z∈realCube zone):
    |(spanX (Dir v) A W z (tuning p)).re| ≤ lowCost r c B b s/(beamH n)^2:=by
  let R:=purse r c B
  let k:=tuning p
  let d:=beamH n
  have hd:0<d:=beamP _
  have he' (i:Site n): tuning i ∈strip η:= YM.Work.F07.realStrip _ he ((keyboard (n:=n) i).1)
  have hk': k ∈ strip η:= he' p
  have hz: z∈ strip η:= YM.Work.F07.realStrip _ he hp
  have hu: k+z∈strip η:= YM.Work.F07.realStrip _ he hk.1
  have hR:=h.cost_q
  have hV (i:Site n): ‖drop v (tuning i)‖≤ (2*R)/d:= by
    have hx:= tune_nonzero i; have hg:= keyboard i
    have ht : 0<‖tuning i‖:= norm_pos_iff.mpr hx
    have hy:= (h.protectedV e hg hx (h.friend e hg hx)).2
    apply hy.trans; change R/ _ ≤ _; rw [div_le_div_iff₀ ht hd]; nlinarith only [mul_le_mul_of_nonneg_left (minSize i) hR,show R=purse r c B from rfl]
  have hb:= hw.posX he; have hs:= hQ.posX he
  let U:=2*R/d; have hU:0 ≤ U:=div_nonneg (mul_nonneg (by norm_num) hR) hd.le
  have ht: ‖drop v (k+z)‖≤ U:= (by rw [show drop v (k+z)=drop v (tuning (p+q)) from tinct p hg hk]; exact hV _)
  have ha:= hw.s (-z,k+z) ⟨strip_negX hz, hu⟩; have hZ:=hw.s (z,k) ⟨hz,hk'⟩
  apply (Complex.abs_re_le_norm _).trans; change ‖(drop v k*A (-z,k+z)*drop v (k+z)*A (z,k)).trace- (drop v k* W (z,k)).trace‖ ≤ _
  apply (norm_sub_le ..).trans
  apply (add_le_add ((trace_cost ..).trans (mul_le_mul_of_nonneg_left (show ‖drop v k*A (-z,k+z)*drop v (k+z)*A (z,k)‖≤ ((U*b)*U)*b from ?_) (by positivity))) ((trace_cost ..).trans (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul (hV p) (hQ.s (z,k) ⟨hz,hk'⟩) (by positivity) hU)) (by positivity)))).trans
  · change _ ≤ _ / d^2
    refine le_trans ?_ (le_of_eq (rfl : lowCost r c B b s/d^2 = _))
    unfold U lowCost
    calc
      _ ≤ (↑(Fintype.card Fiber):ℝ)*(((2*R/d*b)*(2*R/d))*b) + ↑(Fintype.card Fiber)*(2*R*s/d^2):= by apply add_le_add_right; gcongr; change _≤_; field_simp; have hv : d≤1:=htb; nlinarith [show 0≤2*R*s from mul_nonneg (mul_nonneg (by norm_num) hR) hs]
      _ = _ := by unfold R; ring
  exact (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul (hV p) ha (norm_nonneg _) hU)) ht (norm_nonneg _) (by positivity))) hZ (norm_nonneg _) (by positivity))
end YM.QCD.Pearl
