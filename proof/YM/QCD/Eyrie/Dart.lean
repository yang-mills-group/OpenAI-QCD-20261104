import YM.QCD.Eyrie.Sphere

/-! # local polynomial envelope along uniform graph. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Metric Lattice Wilson Lat Push.Uniform Tree RG Precision
open Quarry Finset YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {C Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
lemma origin_h {V I : Type}[Fintype V][Fintype I]{n : Side}{l: I→Site n}{k : V→Site n}{X:Positions I→Positions V}{r A:ℝ} (hr : 0<r)(ha : 0≤A)
    (hX:X 0=0)(h:ContDiffAt ℝ ω X 0) (he: Push.Uniform.Envelope l k r 2 X 0 A)(v : V):
    Flock l Push.Uniform.bolt (fun y=> X y v) (k v) r A:=by
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℝ) v
  let g := L∘X
  refine ⟨hr,ha,(contDiffAt_pi.mp h) v,by rw [hX,Pi.zero_apply,norm_zero]; exact ha,?_ ,?_⟩
  · intro i; change ‖blade (Push.Uniform.bolt i) g 0‖ ≤ _; rw [show blade _ _ _=_ from retell _ L h]; simpa [entry,iteratedFDeriv_one_apply,L,glaze,spanSites,Decay] using he 1 (by decide) (by decide) ![i] v
  intro i j; change ‖Jacobi.mixed _ _ g _‖ ≤ _; rw [show Jacobi.mixed _ _ g _=_ from retold _ _ L h,iter _ _ h]
  have hh:= he 2 (by decide) le_rfl ![i,j] v
  simp only [entry,glaze,spanSites,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_add,mul_add,Real.exp_add] at hh
  rw [show ![Push.Uniform.bolt i,Push.Uniform.bolt j]=Push.Uniform.bolt ∘ ![i,j] from funext fun i=> by fin_cases i <;> rfl]; exact hh
variable {f c : Side} {S : StepData c f}
  {H : Forest S.ratio} {Λ μ A Z r : ℝ} {b : Clip} {K : KernelChoices} {N j : ℕ} {M : Before su μ A j K N} {R : PathData su}
  {u : Bid.Dir su c→AxisChart su H}
local notation "P" => M.tables b S.patch

variable (h : M.Service H b R u)(hw:R.Bounds b μ A Λ)(he : Bid.Larger (G:=su) S)(hJ:S.patch.J=j)(ht:S.kernel=K)

-- c location lifted
abbrev beam (ρ : Ratio c f) (i:Road c):= ρ.embed i.1
lemma primedBolt (i:Road c) :(Quarry.mergeC c).symm (Push.Uniform.bolt i)=Push.Uniform.bolt ((i.1,i.2.1),i.2.2):=by
  funext x
  rcases x with ⟨⟨y,k⟩,r⟩; rcases i with ⟨p,i⟩; rcases i with ⟨k',r'⟩
  change Push.Uniform.bolt (p,k',r') (y,k,r)=Push.Uniform.bolt ((p,k'),r') ((y,k),r); simp [Push.Uniform.bolt,Pi.single_apply,and_assoc]
include h hw he hJ ht
lemma glints (i : Push.Uniform.Joint H su):
    0< responseRate (P).coords N (P).value (P).width (P).gap ∧ 0<curveCost (P).coords (P).value (P).width (P).gap 2 ∧
    Flock (beam S.ratio) Push.Uniform.bolt (fun y: Cnr c=> curve (Push.Uniform.station u) ((mergeC c).symm y) i) (address H su i) (responseRate (P).coords N (P).value (P).width (P).gap) (curveCost (P).coords (P).value (P).width (P).gap 2):=by
  let t : S.Choices := Classical.arbitrary _
  have hr := (M.receipt H t hw he hJ ht).1
  have hz:= Metric.mem_ball_self (x:=(0:Clump c)) h.x_pos
  have hx := h.series hz
  let F := curve (Push.Uniform.station u)
  let T:=mergeC c
  have hh: F 0=0:=by
    have hu : Push.Uniform.station u 0=0:=by unfold Push.Uniform.station; simp [h.critical.1]
    unfold F curve; rw [hu]; exact (partSpace _ _).symm.map_zero
  have hp : 2<N:= M.n_ok
  have ha := along hx
  have hm:= envelopes hr hx (h.pricing hz) (h.entered hw he hJ ht hz t) hp
  let x:=fun y=>F y i
  have he := origin_h (rate_pos hr) (zero_le_one.trans (curveCost_ge hr _)) hh ha hm i
  refine ⟨he.fund,lt_of_lt_of_le zero_lt_one (curveCost_ge hr _), he.fund,he.fee, ?_ ,?_,fun i=>?_ ,fun i j=>?_⟩
  · exact ContDiffAt.comp (f:=T.symm) (g:=x) _ (by rw [map_zero]; exact he.host) T.symm.contDiff.contDiffAt
  · rw [map_zero]; exact he.born
  · change ‖blade _ (x∘_) _‖≤ _ -- κ projection
    erw [transfuse (f:=x) (mergeC c).symm.toContinuousLinearMap (Push.Uniform.bolt i) (by rw [map_zero]; exact he.host),ContinuousLinearEquiv.coe_coe,map_zero,primedBolt]; exact he.walks _
  change ‖Jacobi.mixed _ _ (x ∘ ⇑(mergeC c).symm) _‖ ≤ _
  erw [adapt (f:=x) (x:=0) (mergeC c).symm.toContinuousLinearMap _ _ (by rw [map_zero]; exact he.host), ContinuousLinearEquiv.coe_coe, primedBolt i,primedBolt j]; simp only [map_zero]; exact he.wandered _ _
end YM.QCD.Eyrie
