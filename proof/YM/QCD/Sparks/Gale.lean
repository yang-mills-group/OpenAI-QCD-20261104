import YM.QCD.Sparks.Priest

/-! # doubling spin period summation at rooted jets -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Eyrie Quarry Tree RG Precision Rudder Flume Pine Finset Set
open YM.Further.PhysicalPeriodLimitF933 Macrame Jacobi Stationary Tavern
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n N: Side} {k m M:ℕ}
lemma pinhead {G : Window n N M} {F: trackG n}{J:trackG N}(hf : ContDiffAt ℝ ω F 0)(hJ:ContDiffAt ℝ ω J 0) (v: Fin k→ Cnr n) {d : Site N→ℂ}{L:Cnr n→L[ℝ] Cnr N}
    (h: ∀ᶠ x in 𝓝 0,J (L x)*stream G d=stream G d*F x):
    surge J (L∘v)*stream G d=stream G d*surge F v:=by
  let P := stream G d
  let A : Sheet n→L[ℝ] Rail N n:=LinearMap.toContinuousLinearMap { toFun:=fun M=>P*M, map_add':=fun _ _=> Matrix.mul_add ..,map_smul':=fun _ _=> Matrix.mul_smul .. }
  let B : Sheet N→L[ℝ] Rail N n:=LinearMap.toContinuousLinearMap { toFun:=fun M=>M*P,map_add':=fun _ _=>Matrix.add_mul ..,map_smul':=fun _ _=>Matrix.smul_mul .. }
  change B∘ J ∘ L=ᶠ[𝓝 0] A ∘ F at h
  have hL : ContDiffAt ℝ ω J (L 0):=by rw [map_zero]; exact hJ
  have h' := DFunLike.congr_fun ((h.iteratedFDeriv ℝ k).eq_of_nhds) v
  rw [B.iteratedFDeriv_comp_left (hL.comp (f:=L) _ L.contDiff.contDiffAt) le_top,A.iteratedFDeriv_comp_left hf le_top, iter_lin_at (L:=L) (hL.of_le le_top),map_zero] at h'; exact h'
lemma clad (P:Bundle)(z:ℂ): (show Bundle from (z • P)) = z • P:=rfl
lemma velvet (L: Window n N M) (d: Site N→ℂ)(A:Sheet N)(Q:Sheet n)(H:A*stream L d=stream L d*Q) (x : Site N)(y:Site n):
    d x • Run.cell Q (L.cut x) y=∑ i:Site N, if L.cut i=y then d i • Run.cell A x i else 0:=by
  ext a b; have he:= Matrix.ext_iff.mpr H (x,a) (y,b) -- check
  rw [streams,Matrix.mul_apply,Fintype.sum_prod_type] at he
  rw [Matrix.sum_apply]; change d x*Q _ _ = _; rw [← he]; apply Finset.sum_congr rfl; intro i _; split
  next hy => simp [stream,hy,mul_comm]; exact Or.inl rfl
  next hy => simp [stream,hy]

lemma bolt_add (V:Cnr n) : V=∑ i:Road n, V i • Push.Uniform.bolt i:=by funext x; rw [Finset.sum_apply, sum_eq_single x] <;> simp [Push.Uniform.bolt, Pi.single_apply, eq_comm (a:=x)]; tauto
-- multilinear expansion reusable
lemma blast {X Y I:Type} [NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y] [Fintype I]
    (v:Fin k→I→X)(q : ContinuousMultilinearMap ℝ (fun _ : Fin k=>X) Y): q (fun i=> ∑ j,v i j)=∑ p:Fin k→I,q fun i=> v i (p i):=by
  have he:= q.toMultilinearMap.map_sum (α:=fun _=> I) (g:=v)
  simpa using he -- check
lemma blared {F:trackG n}(x: Fin k→Cnr n): surge F x=∑ p:Fin k→Road n,(∏ i,x i (p i)) • Push.Uniform.entry F 0 p:=by
  unfold surge; nth_rw 1 [show x=(fun i=> ∑ j:Road n,x i j • Push.Uniform.bolt j) from funext fun i=> bolt_add _]
  rw [blast (X:=Cnr n)]; refine Finset.sum_congr rfl fun p _=>?_ ; exact (iteratedFDeriv ℝ k F 0).toMultilinearMap.map_smul_univ _ _
lemma openness (F:trackG n)(x:Fin k→Cnr n)(j : Site n): Run.cell (surge F x) (0:Site n) j=∑ p:Fin k→Road n,(∏ i,x i (p i)) • dotP F k (j,p):=by
  rw [blared]; ext a b; rw [Matrix.sum_apply]; unfold Run.cell; rw [Matrix.of_apply]; rw [Matrix.sum_apply]; exact Finset.sum_congr rfl fun i _=> rfl
lemma uphold_period {G : Window n N M} {d: Site N→ℂ} (h: Quaint G d)(x : Site N)(v: Cover): occ x v*d (x+wrap N v)=d x* occ (G.cut x) v:=by
  let Q:= route 0 v (1:Lattice.Order)
  have ht:= pours h x Q; rw [occ_rays,occ_rays,wrap_stop, show stop 0 Q=v from route_end ..] at ht; exact ht
lemma factor_period {G : Window n N M}{d:Site N→ℂ}(h: Quaint G d)(x y : Site N):
    d y= d x*occ (G.cut x) (lift (y-x))*occ x (lift (y-x)):=by
  let L:= lift (y-x); have ht:=uphold_period h x L; rw [show x+wrap N L=y from by unfold L; rw [wrap_lift]; abel] at ht
  rw [← ht,mul_right_comm,show occ x L*occ x L=1 from (realSeam ..).2,one_mul]
lemma calibrated (G: Window n N M)(d : Site N→ℂ)(h : Quaint G d) {F:trackG N} {x:Fin k→Cnr N} {Q:Sheet n} (he : surge F x*stream G d=stream G d*Q)(y : Site n) (hp:G.cut 0=0):
    Run.cell Q 0 y=∑ p:Plane N k, if G.cut p.1=y then (∏ i,x i (p.2 i)) • (occ (0:Site n) (lift p.1) • normedD F p) else 0:=by
  apply smul_right_injective Bundle (show d 0≠0 from by rcases h.sign 0 with h|h <;> simp [h]) -- inspect
  dsimp only; nth_rw 1 [← hp]; rw [velvet G d _ _ he (0:Site N), Finset.smul_sum,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _=> ?_
  dsimp only
  split <;> rename_i hi
  · rw [openness F, Finset.smul_sum]; apply sum_congr rfl; intro j _
    rw [normedD, smul_comm (d i), smul_comm (d 0) (Finset.prod _ _),factor_period h 0 i,hp,sub_zero]
    simp only [smul_smul, mul_assoc]
  simp [hi]
end YM.QCD.Sparks
