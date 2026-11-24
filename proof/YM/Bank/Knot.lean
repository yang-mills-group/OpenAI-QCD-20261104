import YM.Bank.Tel
/-! Calibrated gauges. Unscaled.Pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Knot
open Function Lattice Laurent Bloch Metric Exterior Precision Matrix
open YM.Next.Free Finset Filter RG AnalyticBridge.LocalGaussianLaws.Current
open YM.Bank.Learn
open QCD.Flume (twins tunes)
open scoped Matrix BigOperators Topology ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator
variable {c f:Side}{k j:ℕ} {n:Type}{m g: Type*} [DecidableEq n][Fintype n][Fintype m][Fintype g]
lemma refinements (r:Ratio c f)(hp:Odd r.count.val) {A: Matrix (Site f×n) (Site f×n) ℂ}{Q: Momentum → Matrix n n ℂ} (h: A*rotations f n = rotations f n * solo f Q):
     A*readings r n= readings r n * braceAll r Q := by
     ext ⟨x,y⟩ ⟨p,l,v⟩
     have hx := congr_fun (congr_fun h (x,y)) (twins r p l,v)
     rw [solo,rot_fiber] at hx
     rw [Matrix.mul_apply, Fintype.sum_prod_type]; simp_rw [twin_leaf _ hp]
     rw [Matrix.mul_apply,Fintype.sum_prod_type] at hx; rw [hx]; unfold braceAll
     rw [Matrix.mul_apply,Fintype.sum_prod_type, twin_mon _ hp]
     symm
     -- gone
     have hh := twin_mon r hp p l
     unfold cell; rw [twin_mon _ hp]; -- RHS sign
     -- sum
     simp only [Fintype.sum_prod_type, sample,fiber, Matrix.of_apply]; simp [ite_mul,mul_ite] -- edit
lemma shines (H:Bed)(r:Ratio c f)(hp: Odd r.count.val) : gaugeΞ H f * readings r (TypeFace 1) = readings r (TypeFace 1)*braceAll r (spaceK H.metric):= refinements r hp (moves H f)

def crow (j:ℕ)(r:Ratio c f)(B F:Bed)(p:Momentum)(l:Site r.count):=
     let k:= aliasAt p l
     starΔ F k * ((stageVolume r.count)⁻¹ • (((r.count.val:ℂ) • mask 1 (spindle j r.count k))ᴴ))*live B.metric p
lemma crowgate (r:Ratio c f)(F B:Bed)(p:Momentum) :
   fiber (fun l : Site r.count=>signal 1 1 (aliasAt p l))*fiber (fun l : Site r.count=>spaceK F.metric (aliasAt p l)) * ((stageVolume c/stageVolume f) • (warp j r p)ᴴ)* live B.metric p=
   downAlias (crow j r B F p):=by
   rw [fiber_mult, warp, alias_up, alias_pay, alias_after, alias_then]; rw [ratio_volume r, div_eq_mul_inv, _root_.mul_inv_rev, mul_left_comm,mul_inv_cancel₀ (stage_ne c),mul_one]; rfl
variable {r:Ratio c f}{B F:Bed}{Q J R}
lemma tech (h:TowerW j r F B J R Q){a b:ℝ}(hF:F.metric.safe) (hf:Numeric (F.metric.acts f) a b)(he:0<a)(hB:B.metric.safe):
     Runs (readings r (TypeFace 2)) (rotations c (TypeFace 1)) (J*d 1 c) (solo c (fun p=> downAlias (crow j r B F p))) :=by
     let D:=d 1 f; let M:=gaugeΞ F f
     let V:= Precision.K (F.metric.acts f); let U:=Precision.K (B.metric.acts c)
     have hs : approached (J*d 1 c)= approached D*M*approached Q.transpose*approached U:=by
        rw [h.binds,Bloch.prom_mul]; nth_rw 1 [← show approached D*M* approached V=approached D from stakes hF hf he]
        rw [Matrix.mul_assoc _ (approached V),← Bloch.prom_mul,show V*R=Q.transpose*U from h.station,Bloch.prom_mul,Matrix.mul_assoc _ (approached Q.transpose) ]
     let Ω:= readings r (TypeFace 1); let T:= readings r (TypeFace 2); let A:= rotations c (TypeFace 1)
     let Z:= solo c (live B.metric); let Y:= (stageVolume c/stageVolume f) • (solo c (warp j r))ᴴ
     have hp : approached U*A=A*Z:= live_c c hB
     have hy : approached Q.transpose*A=Ω * Y:= Runs.back h.smooth (rotations_crew ..) (readings_crew ..) -- projection
     have ht : approached D*Ω = T * braceAll r (signal 1 1):= (cobound_true 1).fine r h.odd
     change _*A=T*_
     rw [hs]; simp only [Matrix.mul_assoc]; rw [hp,← Matrix.mul_assoc _ A, hy, Matrix.mul_assoc Ω, ← Matrix.mul_assoc _ Ω, show M*Ω=_ from shines F r h.odd, Matrix.mul_assoc Ω,← Matrix.mul_assoc _ Ω,ht,Matrix.mul_assoc T]; congr 1
     unfold braceAll Z Y solo; rw [fiber_H,fiber_weight,fiber_mult,fiber_mult,fiber_mult]; simp_rw [← crowgate]; simp only [Matrix.mul_assoc]

end YM.Bank.Knot
#print axioms YM.Bank.Knot.tech
