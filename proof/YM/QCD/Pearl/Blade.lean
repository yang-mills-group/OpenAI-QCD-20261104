import YM.QCD.Pearl.Pop

/-! # bring the momentum tape into cutoff function Hessian -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {n : Side} {I J D : Type} {m j : ℕ} {η a b c : ℝ}
variable {G:I→Gleam}{U:J→Bloom 1}{V:D→Bloom 2}(C : su.Color)
lemma earmarked (ha : Wages η a G) (he : 0<η) (u v : Weather n): AnalyticAt ℂ (totals C G n) 0 ∧
    HasSum (fun i=> dew u (silo C 0 (G i)) 0) (dew u (totals C G n) 0) ∧ HasSum (fun i=> dig u v (silo C 0 (G i)) 0) (dig u v (totals C G n) 0):=by
  obtain ⟨δ,h⟩:= appoint C he
  obtain ⟨f,⟨w,H⟩,hh⟩:= silo_swell h (0:Site n); simp_rw [H] at hh
  have hv i z (hz:z∈ball (0:Weather n) δ): ‖silo C 0 (G i) z‖ ≤ w*(G i).rate η:=hh _ z (mem_ball_zero_iff.mp hz).le
  exact ⟨Work.F02.analytic_series _ h.dry (fun i=> siloD C _ _) (ha.val.mul_left w) hv, internal_drop _ u h.dry (fun i=>siloD C _ _) (ha.val.mul_left w) hv 0 (mem_ball_self (half_pos h.dry)),external_drop _ u v h.dry (fun i=>siloD C _ _) (ha.val.mul_left w) hv⟩
lemma trivializes {U:I→Bloom m}(h: Fractal U η a) (he : 0<η) (u v: Weather n):AnalyticAt ℂ (reachouts C U n) 0 ∧
    HasSum (fun i=> dew u (silt C 0 (U i)) 0) (dew u (reachouts C U n) 0) ∧ HasSum (fun i=> dig u v (silt C 0 (U i)) 0) (dig u v (reachouts C U n) 0):=by
  obtain ⟨δ,hδ⟩:= appoint C he; obtain ⟨w,H⟩:= silt_swell hδ m (0:Site n)
  have hp i z (hz:z∈ball (0:Weather n) δ): ‖silt C 0 (U i) z‖ ≤ w*(U i).paid η:= H _ z (mem_ball_zero_iff.mp hz).le
  exact ⟨Work.F02.analytic_series _ hδ.dry (fun i=> siltD C _ _) (h.bills.mul_left w) hp, internal_drop _ u hδ.dry (fun i=>siltD C _ _) (h.bills.mul_left w) hp 0 (mem_ball_self (half_pos hδ.dry)),external_drop _ u v hδ.dry (fun i=> siltD C _ _) (h.bills.mul_left w) hp⟩
lemma cloud0 (G: Site n→ Bundle): cloud 0 G=lined G:=by
  unfold cloud lined; congr 1; · ext1; simp [Equiv.addRight]
  funext i; simp
lemma billBeam (A:I→Sheet n)(Z:I→Site n→Bundle)(R)(h:HasSum A R)(he:∀ i, peel (A i)=lined (Z i)):
    peel R=lined fun k=> ∑' i,Z i k:=by rw [← cloud0]; exact billBand _ _ _ h (fun i=> (he i).trans (cloud0 _|>.symm))
lemma aria {G:I→Gleam} (h: billPack η a b c G U V)(hη:0<η)(n:Side): AnalyticAt ℂ (extent C G U V n) 0:=
    AnalyticAt.add ((earmarked C h.1 (by positivity) (0:Weather n) 0).1.add (trivializes C h.2.1 (by positivity) (0:Weather n) 0).1) (trivializes C h.2.2 (by positivity) (0:Weather n) 0).1
lemma dig_plusA (X Y : Weather n→Sheet n)(hx: AnalyticAt ℂ X 0)(hy:AnalyticAt ℂ Y 0) (u v: Weather n):dig u v (X+Y) 0= dig u v X 0+dig u v Y 0:=by
  have he : dew v (X+Y)=ᶠ[𝓝 0] dew v X+dew v Y:= by
    filter_upwards [hx.eventually_analyticAt,hy.eventually_analyticAt] with i hi hk; exact dew_plus hi.differentiableAt hk.differentiableAt _
  unfold dig; rw [dew_var he,dew_plus (voiced v hx) (voiced v hy)]
lemma hilt (h:billPack η a b c G U V)(he:0<η){p: Site n}{P: Momentum} (hp: Fans p P) (i: Axis):
    let M:= extent C G U V n; let x:= flashT p i; let y:= flashT (-p) i
    peel (dew x M 0)=(cloud p fun k=>v₁ G U C i (P,tuning k))∧ peel (dig x y M 0)= (lined fun k=>v₂ G U V C i (P,tuning k)):=by
  intro M x y; obtain ⟨ht,ht1,ht2⟩:= earmarked C h.1 (by positivity) x y; obtain ⟨hr,hr1,hr2⟩:= trivializes C h.2.1 (by positivity) x y; obtain ⟨hs,hs1,hs2⟩:=trivializes C h.2.2 (by positivity) x y
  rw [show M=totals C G n + reachouts C U n + reachouts C V n from rfl,dew_plus (ht.add hr).differentiableAt hs.differentiableAt, dew_plus ht.differentiableAt hr.differentiableAt, peel_add,peel_add];
  constructor
  · have hew:dew x (reachouts C V n) 0=0:= hs1.unique (by simp only [x,silt₂]; exact hasSum_zero)
    rw [hew,show peel (0:Sheet n)=0 from by simp [peel], add_zero]; rw [billBand _ (fun j k=> boom₁ C (G j) i P (tuning k)) _ ht1 (fun _=> boom_P C _ _ hp),billBand _ (fun j k=>nil₁ C (U j) i P (tuning k)) _ hr1 (fun _=>law_P C _ _ hp)];
    unfold cloud; rw [ride_add]; rfl
  rw [dig_plusA _ _ (ht.add hr) hs,dig_plusA _ _ ht hr,peel_add,peel_add,billBeam _ (fun j k=> boom₂ C (G j) i P (tuning k)) _ ht2 (fun _=>boom_Q C _ _ hp),billBeam _ (fun j k=>yet₁ C (U j) i P (tuning k)) _ hr2 (fun _=>leaf_Q C _ _ hp), billBeam _ (fun j k=>yet₂ C (V j) i P (tuning k)) _ hs2 (fun _=>sky_Q C _ _ hp)]; unfold lined; rw [ride_add,ride_add]; rfl
end YM.QCD.Pearl
