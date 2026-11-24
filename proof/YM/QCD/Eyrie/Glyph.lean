import YM.QCD.Eyrie.Tag

/-! # Jet matrix multiplication. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {X Y R: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n : Side} {I J K M L: Type} [Fintype J] [Fintype K] [Fintype M] {ν : ℕ}
variable {l : I→Site n} {d : I→X} {j : J→Site n} {k : K→Site n} {m : M→Site n} {r a b c C D u : ℝ}

def glyph (l : I→Site n)(d:I→X)(j:J→Site n)(k:K→Site n)(F:X→Matrix J K ℂ)(r C:ℝ) :=
    ∀ i h,Flock l d (fun x=> F x i h) (j i) r (C*Decay r (j i) (k h))
namespace glyph
variable {F G : X→Matrix J K ℂ}
omit [Fintype J] [Fintype K] in
lemma reduces (h:glyph l d j k F r C)(hu:0<u)(he:u≤r)(hp:0≤C)(hC:C≤D): glyph l d j k F u D:=fun i b=> ((h i b).cliff hu he).patron (mul_le_mul hC (white he ..) (decay_pos ..).le (hp.trans hC))
omit [Fintype J] [Fintype K] in
lemma plus (h:glyph l d j k F r C)(he:glyph l d j k G r D): glyph l d j k (F+G) r (C+D) := by intro i b; rw [add_mul]; exact (h i b).plus (he i b)
omit [Fintype J] [Fintype K] in
lemma minus (h:glyph l d j k F r C): glyph l d j k (-F) r C := fun i b=> (h i b).nu
omit [Fintype J] [Fintype K] in
lemma tariff (h:glyph l d j k F r C)(c : ℂ):glyph l d j k (c • F) r (4*(‖c‖*C)):=by
  intro i b; rw [mul_assoc _,mul_assoc]; exact (Flock.hush c (h i b).fund).breakthrough (h i b)
omit [Fintype J] [Fintype K] in
lemma fleet {L : Type} [Fintype L] {P:L→ X→Matrix J K ℂ}{s: Finset L}{B:L→ℝ}(h : ∀ i∈s,glyph l d j k (P i) r (B i))(hr : 0<r):
    glyph l d j k (fun x=> ∑ i∈s,P i x) r (∑ i∈s,B i):=by intro i b; simp_rw [Matrix.sum_apply,sum_mul]; exact Flock.convoy hr (fun v hv=> h v hv ..)
omit [Fintype J] in
lemma uni [DecidableEq J] (hr : 0<r): glyph l d j j (fun _=>(1:Matrix J J ℂ)) r 1:=by
  intro i b; apply (Flock.hush _ hr).patron; simp only [Matrix.one_apply]; split
  next h=> rw [h]; simp [Decay]
  rw [norm_zero,one_mul]; exact (decay_pos ..).le

omit [Fintype J] [Fintype K] in
private lemma slide {v : ℝ} (hv : 0<v) (hr: 4*v ≤r) {h x y : Site n} : Decay r x h * (Decay v h y * (Decay v x h)⁻¹^2) ≤ Decay v x h * Decay v x y:=by
  let A:=Decay v x h; let B:=Decay v h y; have hp : 0<A:=decay_pos ..; have hB: 0<B:=decay_pos ..
  have he:= white (y:=h) (x:=x) hr
  have hq : A^(4:ℕ)=Decay (4*v) x h:=by unfold A Decay; rw [← Real.exp_nat_mul]; push_cast; ring_nf
  apply (mul_le_mul_of_nonneg_right he (show 0≤B*A⁻¹^2 from by positivity)).trans
  rw [← hq]; change A^4*(B*A⁻¹^2) ≤ A*_; rw [show A^4*(B*A⁻¹^2)=A*(A*B) by field_simp]; exact mul_le_mul_of_nonneg_left (decay_step hv.le ..) hp.le

omit [Fintype J] [Fintype M] in
lemma comp {G : X→Matrix K M ℂ}(h:glyph l d j k F r C)(he:glyph l d k m G u D)(hu : 0<u)(hr : 4*u≤r)(hK : Multiplicity k ν)(hC : 0≤ C)(hD:0≤D):
    glyph l d j m (fun x=> F x*G x) u (4*C*D*((ν:ℝ)*countCost u)) := by
  intro i b
  let A:= j i; let B:=m b; let S:=Decay (n:=n)
  have hh w:Flock l d (fun x=>F x i w*G x w b) (j i) u (4*C*D*(Decay u A (k w)*Decay u A B)):=by
    apply ((((h i w).cliff hu (by linarith)).breakthrough ((he w b).roster (j i))).patron)
    have ht : S r A (k w) * (S u (k w) B * (S u A (k w))⁻¹^2) ≤ S u A (k w)*S u A B:=slide hu hr
    change 4*((C*S r A (k w))*(D*S u (k w) B*(S u A (k w))⁻¹^2)) ≤ _; linarith only [mul_le_mul_of_nonneg_left ht (mul_nonneg hC hD)]
  simp only [Matrix.mul_apply]
  refine (Flock.convoy hu (fun w (_:w∈univ)=> hh w)).patron ?_
  simp_rw [← mul_assoc (4*C*D), ← sum_mul,← mul_sum]; apply mul_le_mul_of_nonneg_right _ (decay_pos ..).le
  rw [mul_assoc (4*C*D)]; exact mul_le_mul_of_nonneg_left (hK.count _ hu A) (by positivity)

omit [Fintype J] [Fintype K] in
lemma flip (h:glyph l d j k F r C)(hu: 0<u)(hr : 3*u≤r): glyph l d k j (fun x=>(F x)ᴴ) u C:=by
  intro i b
  let x:=j b; let y:= k i
  have hp := ((h b i).cliff hu (by linarith)).roster y
  let f (x:X):= F x b i; let L:= (starL ℝ : ℂ≃L[ℝ]ℂ).toContinuousLinearMap
  let a:=C*Decay r x y*(Decay u y x)⁻¹^2
  have ht : Flock l d (L ∘ f) y u a:=by
    have hP : Flock l d f y u a:=hp
    refine ⟨hu,hP.fee,L.contDiff.contDiffAt.comp _ hP.host,?_ ,fun w=>?_, fun w y=>?_⟩
    · rw [Function.comp_apply, show ‖L (f 0)‖=‖f 0‖ from norm_star ..]; exact hP.born
    · rw [retell _ _ hP.host, show ‖L _‖=_ from (norm_star (blade (d w) f 0))]; exact hP.walks w
    rw [retold _ _ _ hP.host, show ‖L _‖=_ from norm_star (Jacobi.mixed (d w) (d y) f 0)]; exact hP.wandered w y
  apply ht.patron
  have hC : 0≤C := nonneg_of_mul_nonneg_left (show 0≤ C*Decay r x y from (h b i).fee) (decay_pos ..)
  unfold a; rw [decay_comm r x, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC
  apply (mul_le_mul_of_nonneg_right (white hr y x) (by positivity : 0 ≤ (Decay u y x)⁻¹^2)).trans_eq
  rw [show Decay (3*u) y x= Decay u y x^3 from (by unfold Decay; rw [← Real.exp_nat_mul]; push_cast; ring_nf)]
  field_simp [(decay_pos u y x).ne']; rfl
end glyph
end YM.QCD.Eyrie
