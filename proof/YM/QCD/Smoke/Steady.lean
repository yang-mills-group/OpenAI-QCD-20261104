import YM.QCD.Smoke.Fire

/-! # lit cloud localized. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Finset Lat Cost Run Eyrie Metric Lattice Wilson Push.Uniform
open YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.L2Operator
variable {n:Side}{X V:Type} [NormedAddCommGroup X][NormedSpace ℝ X] {r D u:ℝ}{w v:ℕ→ℝ}
def fuseG (w v:ℕ→ℝ)(r D:ℝ) (q:ℕ) : ℕ→ℝ
  | 0=>0
  | n+1=>∑ p∈antidiagonal n,4*(4*w p.1*D*(q*countCost (4*r)))*v p.2*(q*countCost r)
-- drop C param
lemma fuseP (w v:ℕ→ℝ)(h:∀ i,0≤w i)(hw:∀ i,0≤v i)(q:ℕ)(ht:0≤D)(he:0<r)(i:ℕ):0≤ fuseG w v r D q i:=by
  cases i with
  | zero=> exact le_rfl
  | succ i=> rw [fuseG]; apply sum_nonneg; intro i _; have hp:=count_pos he; have hx:=count_pos (show 0<4*r by positivity); have hZ:=h i.1; have hU:=hw i.2; positivity
lemma fuses {q:ℕ}(h:Summable w)(hh:Summable v) : Summable (fuseG w v r D q):=by
  apply (summable_nat_add_iff 1).1
  have hc:= (summable_sum_mul_antidiagonal_of_summable_norm' h.norm h hh.norm hh).mul_right (4*4*D*(q*countCost (4*r))*(q*countCost r)) -- name
  apply hc.congr; intro i; unfold fuseG; rw [Finset.sum_mul]; apply sum_congr rfl; intros; ring
variable {l:V→ Site n}{k:V→X}{p:Row n→Site n}{A d:X→Sheet n}{B:ℕ→X→Sheet n}
lemma zeroG (h:0<r):glyph l k p p (0:X→Sheet n) r 0:=by intro i j; simpa using (Flock.hush (0:ℂ) (x:=p i) (l:=l) (d:=k) h)
lemma batch {I:Type}{T:I→ X→Sheet n}{u:I→ℝ}(s: Finset I)(h:∀ i,glyph l k p p (T i) r (u i))(hr:0<r): glyph l k p p (∑ i∈s,T i) r (∑ i∈s,u i):=by
  induction s using Finset.induction with
  | empty=> simp only [sum_empty]; exact zeroG hr
  | insert x s hx hh=> rw [sum_insert hx,sum_insert hx]; exact (h x).plus hh
lemma gusts (q:ℕ)(hq: Multiplicity p q)(hh:0<r)(hz:4*(4*r)≤u)(h:∀ i,0 ≤ w i)(he:∀ i,0≤v i)(hc:0≤D)
    (hA:∀ i,glyph l k p p (A^i) u (w i))(hF:glyph l k p p d (4*r) D)(hB:∀ i,glyph l k p p (B i) r (v i))(i):glyph l k p p (shove A d B i) r (fuseG w v r D q i):=by
  cases i with
  | zero=> intro a b; simp only [shove,fuseG,zero_mul,Pi.zero_apply,Matrix.zero_apply]; simpa using (Flock.hush (0:ℂ) (x:=p a) (l:=l) (d:=k) hh)
  | succ i=>
    have h (c:ℕ×ℕ): glyph l k p p (A^c.1*d*B c.2) r (4*(4*w c.1*D*(q*countCost (4*r)))*v c.2*(q*countCost r)) :=by
      have hx : 0<4*r:=by positivity
      exact ((hA c.1).comp hF hx hz hq (h c.1) hc).comp (hB c.2) hh le_rfl hq (by have := count_pos hx; have he:= h c.1; positivity) (he _)
    rw [shove,fuseG]; exact batch _ h hh

lemma bunch (F:X→Sheet n) (hX:‖F 0‖<1)(h:ContDiffAt ℝ ω F 0) (he : 0<r)(H:∀ i,glyph l k p p (fun x=> logchip (F x) i) r (w i)) (hv:Summable w):glyph l k p p (lap ∘ F) r (∑' i,w i):=by
  intro i j; obtain ⟨hx,hp⟩:= lapRates F h hX
  let D:=Decay r (p i) (p j); have hz:= decay_pos r (p i) (p j); let v (j:ℕ):= w j * D
  let Q:= lap ∘ F; have hi t : ContDiffAt ℝ ω ((fun X=>logchip X t) ∘ F) 0:= ((chip_omega t).contDiffAt.restrict_scalars ℝ).comp 0 h
  have hm : 0≤∑' i,w i:=tsum_nonneg (fun t=> nonneg_of_mul_nonneg_left (H t i j|>.fee) hz)
  rw [← tsum_mul_right]
  obtain ⟨L,hL⟩:= ink_touch (I:=Row n) (J:=Row n) i j
  have hh := hv.mul_right D
  refine ⟨he,tsum_nonneg (fun t=>(H t i j|>.fee)), smear hx i j,?_ ,fun u=>?_,fun u b=>?_⟩
  · have he' : HasSum (fun t=> logchip (F 0) t i j) (Q 0 i j):= by simp_rw [← hL]; exact L.hasSum (Run.log_series hX).hasSum
    change ‖Q 0 i j‖ ≤ _; rw [← he'.tsum_eq]; have hp' t : ‖logchip (F 0) t i j‖ ≤ v t:= (H t i j).born
    have hv' := hh.of_nonneg_of_le (fun t=>norm_nonneg _) hp'; exact (norm_tsum_le_tsum_norm hv').trans (hv'.tsum_le_tsum hp' hh)
  · have he (t:ℕ): ‖blade (k u) ((fun x=>logchip x t) ∘ F) 0 i j‖≤ v t * Decay r (p i) (l u):= by rw [detailed (hi t)]; exact (H t i j).walks u
    have ht : HasSum (fun t=>blade (k u) ((fun x=>logchip x t)∘F) 0 i j) (blade (k u) (lap ∘ F) 0 i j):= by simp_rw [← hL]; exact L.hasSum (hp _ (k u)).1
    have hD := hh.mul_right (Decay r (p i) (l u)); have hP:=hD.of_nonneg_of_le (fun _=>norm_nonneg _) he; rw [← detailed hx,← ht.tsum_eq,← tsum_mul_right]; exact (norm_tsum_le_tsum_norm hP).trans (hP.tsum_le_tsum he hD)
  let a:= k u; let c:=k b
  let Y:=Decay r (p i) (l u)*Decay r (p i) (l b)
  have he (t:ℕ): ‖Jacobi.mixed a c ((fun x=>logchip x t) ∘ F) 0 i j‖≤ v t * Y:= by rw [detail_sq (hi t)]; exact (H t i j).wandered u b
  have ht : HasSum (fun t=> Jacobi.mixed a c ((fun x=> logchip x t)∘ F) 0 i j) (Jacobi.mixed a c (lap ∘ F) 0 i j):= by simp_rw [← hL]; exact L.hasSum (hp a c).2
  have hD := hh.mul_right Y; have hP:= hD.of_nonneg_of_le (fun _=> norm_nonneg _) he; rw [← detail_sq hx,show k u=a from rfl,show k b=c from rfl, ← ht.tsum_eq, ← tsum_mul_right]; exact (norm_tsum_le_tsum_norm hP).trans (hP.tsum_le_tsum he hD)
end YM.QCD.Smoke
