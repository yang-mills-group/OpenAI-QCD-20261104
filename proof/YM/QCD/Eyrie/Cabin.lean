import YM.QCD.Eyrie.Cash

/-! # total holomorphic sums at uniform width; born cursor for repeatable step -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Rudder Revolve Metric Quarry Stationary
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {n : Side} {I X : Type} {k m : ℕ} {r a b c C B R A S u:ℝ}

def dust (P : I→Bloom k) (n:Side) (U:Grid n):Sheet n :=∑' i, (P i).tonic 0 U
lemma dusted {P:I→Bloom k} (hp : Fractal P a C) (V : Grid n)(i j: Row n): dust P n V i j=∑' k, (P k).tonic 0 V i j:=by
  let M : Sheet n →L[ℂ] ℂ:= LinearMap.toContinuousLinearMap {
    toFun A:= A i j,map_add' _ _:=rfl,map_smul' _ _:=rfl }
  exact M.map_tsum ((hp.tonics 0 V).of_norm) -- check
lemma register (f:I→ Cnr n→ℂ)(g:I→ Sails n →ℂ){a:I→ℝ} (hr : 0<R)
    (ha : Summable a)(H:∀ i, ContDiff ℂ ω (g i))(hG:∀ i x,x∈ball 0 R → ‖g i x‖ ≤ a i)
    (h : ∀ i,g i ∘ axisCL (Road n)=f i):
    ContDiffAt ℝ ω (fun x=>∑' i,f i x) 0 ∧ ∀ m:ℕ,∀ p: Fin m → Cnr n, HasSum (fun i=> iteratedFDeriv ℝ m (f i) 0 p) (iteratedFDeriv ℝ m (fun x=>∑' i,f i x) 0 p) :=by
  let G (x:Sails n):=∑' i, g i x
  let F (x:Cnr n):=∑' i, f i x
  have he : G ∘ axisCL (Road n)=F:=by funext x; exact tsum_congr fun i=>congr_fun (h i) x
  have hh:= Work.F02.analytic_series g hr (fun i=> (H i).differentiable (by simp)) ha hG
  refine ⟨visas he hh.contDiffAt, fun m p=> ?_⟩
  change HasSum _ (iteratedFDeriv ℝ m F _ _); rw [liftRates m he hh.contDiffAt]; simp_rw [liftRates m (h _) (H _|>.contDiffAt)]
  have ht:= circles (0:Sails n) hr g ha H hG m 0 (mem_ball_self (by positivity))
  exact (ContinuousMultilinearMap.apply ℂ _ _ (axisCL (Road n)∘p)).hasSum ht
lemma combine (f:I→ Cnr n→ℂ)(F:Cnr n→ℂ){a:I→ℝ}{x:Site n} (h:∀ i,Flock (traceG n) Push.Uniform.bolt (f i) x u (a i))
    (ht: 0<u)(hs:ContDiffAt ℝ ω F 0)(hp: ∀ m:ℕ,∀ p:Fin m → Cnr n,HasSum (fun i=> iteratedFDeriv ℝ m (f i) 0 p) (iteratedFDeriv ℝ m F 0 p))(hv: Summable a): Flock (traceG n) Push.Uniform.bolt F x u (∑' i,a i):= by
  refine ⟨ht,tsum_nonneg fun i=> (h i).fee,hs,?_,?_,?_⟩
  · have he:=hp 0 ![]; simp only [iteratedFDeriv_zero_apply] at he; rw [← he.tsum_eq]; have hg i: ‖f i 0‖≤a i:=(h i).born; have hh:=hv.of_nonneg_of_le (fun _=> norm_nonneg _) hg; exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum hg hv)
  · intro i; let p := Push.Uniform.bolt i
    have he:=hp 1 ![p]; simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at he
    let B:=Decay u x (traceG n i); have ht:=hv.mul_right B
    have hh j : ‖blade p (f j) 0‖≤a j*B:=(h j).walks i
    rw [← show (∑' j,blade p (f j) 0)=blade p F 0 from he.tsum_eq, ← tsum_mul_right]; exact (norm_tsum_le_tsum_norm (ht.of_nonneg_of_le (fun _=> norm_nonneg _) hh)).trans ((ht.of_nonneg_of_le (fun _=> norm_nonneg _) hh).tsum_le_tsum hh ht)
  intro i j
  rw [Jacobi.iter _ _ hs, ← (hp _ _).tsum_eq, ← tsum_mul_right]
  have he k : ‖iteratedFDeriv ℝ 2 (f k) 0 ![Push.Uniform.bolt i,Push.Uniform.bolt j]‖≤a k*(Decay u x (traceG n i)*Decay u x (traceG n j)):=by rw [← Jacobi.iter _ _ (h k).host]; exact (h k).wandered i j
  have hh:= (hv.mul_right (Decay _ x _*Decay _ x _)).of_nonneg_of_le (fun z=> norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum he (hv.mul_right _))

lemma attainable (k:ℕ) (ht:0<r) (u:ℝ) : ∃ w D':ℝ,0<w∧0 ≤ D' ∧ ∀ (I:Type)(P:I→Bloom k), Fractal P r u → ∀ n,
    glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (fun x=> dust P n (input su n x)) w (D'*u):= by
  let w:=r/6; have hw:0<w:=by unfold w; positivity
  obtain ⟨y,E,hy,hE,H⟩:= orient k hw
  let D:= E*(1+circleTax y 1+circleTax y 2)
  have hD:0≤D:=by unfold D; have := circleTax_pos hy 1; have := circleTax_pos hy 2; positivity
  refine ⟨w,D,hw,hD,fun I P hp n i j=> ?_⟩
  choose Q hq hQ he using fun k=>H n (P k) i j
  have hP k: Flock (traceG n) Push.Uniform.bolt (trailF (P k) i j) i.1 w (D*(P k).paid r* Decay w i.1 j.1):=by
    have ht:w+5*w≤r:=by unfold w; linarith
    apply (record (P k) i j hy hw ht hE (L:=Q k) (funext (he k)) (hq k) (hQ k)).patron (le_of_eq ?_); unfold ticket D; ring
  have hs : Summable (fun k=> E*(P k).paid w):= (hp.bills.mul_left E).of_nonneg_of_le (fun k=>mul_nonneg hE ((P k).price_nn.trans ((P k).paidUp hw.le))) (fun k=>mul_le_mul_of_nonneg_left (by
    unfold Bloom.paid; apply mul_le_mul_of_nonneg_right _ ((P k).price_nn); gcongr; dsimp only [w]; linarith) hE)
  let f k := trailF (P k) i j
  have hf := register f Q hy hs hq hQ (fun i=>funext (he i))
  simp_rw [dusted hp]
  apply (combine f _ hP hw hf.1 hf.2 ((hp.bills.mul_left _).mul_right _)).patron
  rw [tsum_mul_right,tsum_mul_left]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp.bill hD) (decay_pos ..).le
end YM.QCD.Eyrie
