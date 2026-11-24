import YM.QCD.Eyrie.Market

/-!
# finite jets at origin with area tag. n independent, placement on one
specified lattice. Counting norm from multiplicity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix ContDiff BigOperators Classical
variable {X Y Z R : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedRing R] [NormedAlgebra ℝ R]
variable {n : Side} {I J K M L: Type} [Fintype J] [Fintype K]
variable (l : I→Site n) (d : I→X) {r a b c C D u : ℝ}

structure Flock (l : I→Site n)(d : I→X) (f:X→Y)(x : Site n) (r C:ℝ): Prop where
 fund : 0 < r
 fee : 0 ≤ C
 host : ContDiffAt ℝ ω f 0
 born : ‖f 0‖ ≤ C
 walks (i:I) : ‖blade (d i) f 0‖ ≤ C * Decay r x (l i)
 wandered (i j:I) : ‖Jacobi.mixed (d i) (d j) f 0‖ ≤ C*(Decay r x (l i)*Decay r x (l j))
variable {l d}
lemma white {v w : ℝ} (he : v≤w) (x y : Site n): Decay w x y≤ Decay v x y:=by unfold Decay; gcongr
lemma snow (x y : Site n) (a:ℝ) : Decay (-a) x y=(Decay a x y)⁻¹:=by unfold Decay; simp [← Real.exp_neg]
lemma lend {r C:ℝ} {l:I→Site n}{x y:Site n} (hr:0≤r) : (Decay r x y)⁻¹ ≤ (Decay r x y)⁻¹^2 := by
  have hf := decay_le hr x y; have ht:=one_le_inv₀ (decay_pos ..) |>.2 hf; nlinarith
lemma foil {r:ℝ}(hr : 0≤r) (x y z: Site n): Decay r x z ≤ (Decay r y x)⁻¹*Decay r y z:= by rw [inv_mul_eq_div, le_div_iff₀ (decay_pos ..),mul_comm]; exact decay_step hr ..

namespace Flock
variable {f g:X→Y} {x : Site n}

lemma patron (h:Flock l d f x r C)(he : C≤D): Flock l d f x r D := { h with fee:=h.fee.trans he,born:=h.born.trans he,walks:=fun i=> (h.walks i).trans (mul_le_mul_of_nonneg_right he (decay_pos ..).le), wandered:=fun i j=>(h.wandered i j).trans (mul_le_mul_of_nonneg_right he (mul_nonneg (decay_pos ..).le (decay_pos ..).le)) }
lemma cliff (h : Flock l d f x r C) (ha : 0<a)(he:a≤r):Flock l d f x a C:= { h with fund:=ha,walks:=fun i=>(h.walks i).trans (mul_le_mul_of_nonneg_left (white he ..) h.fee), wandered:=fun i j=>(h.wandered i j).trans (mul_le_mul_of_nonneg_left (mul_le_mul (white he ..) (white he ..) (decay_pos ..).le (decay_pos ..).le) h.fee)}
lemma aliasG (h:Flock l d f x r C)(he:g=ᶠ[𝓝 0] f): Flock l d g x r C:= ⟨h.fund,h.fee,h.host.congr_of_eventuallyEq he,by rw [he.self_of_nhds]; exact h.born,fun i=>by rw [blade_same (d i) he]; exact h.walks i, fun i j=> by rw [repeated (d i) (d j) he]; exact h.wandered i j⟩
lemma plus (h : Flock l d f x r C)(k:Flock l d g x r D): Flock l d (fun x=> f x+g x) x r (C+D):=by
  refine ⟨h.fund,add_nonneg h.fee k.fee,h.host.add k.host,(norm_add_le ..).trans (add_le_add h.born k.born),fun i=>?_,fun i j=>?_⟩
  · rw [blade_plus (d i) h.host k.host]; exact (norm_add_le ..).trans ((add_le_add (h.walks i) (k.walks i)).trans_eq (add_mul ..).symm)
  have he : blade (d j) (fun y=> f y+g y)=ᶠ[𝓝 0] fun y=> blade (d j) f y+blade (d j) g y := ((h.host.eventually (by simp)).and (k.host.eventually (by simp))).mono fun _ he=> blade_plus _ he.1 he.2
  unfold Jacobi.mixed; rw [blade_same _ he,blade_plus _ (smooth _ h.host) (smooth _ k.host)]; exact (norm_add_le ..).trans ((add_le_add (h.wandered i j) (k.wandered i j)).trans_eq (add_mul ..).symm)
lemma hush (a : Y) (hc : 0<r):Flock l d (fun _=>a) x r ‖a‖:= ⟨hc,norm_nonneg _,contDiffAt_const,le_rfl,
    fun i => by simp only [blade_const,norm_zero]; exact mul_nonneg (norm_nonneg _) (decay_pos ..).le,
    fun i j => by unfold Jacobi.mixed; simp only [show (blade (d j) (fun x:X=>a))=(fun _=>0) from funext fun i=>blade_const _ _,blade_const,norm_zero]; exact mul_nonneg (norm_nonneg _) (mul_nonneg (decay_pos ..).le (decay_pos ..).le)⟩
lemma nu (h : Flock l d f x r C): Flock l d (fun x=> -f x) x r C:=by
  let L := - ContinuousLinearMap.id ℝ Y
  have he (v:Y): L v= -v:=rfl
  rw [show (fun x=> -f x)=L ∘ f from rfl]
  refine ⟨h.fund,h.fee,L.contDiff.contDiffAt.comp _ h.host,(by rw [Function.comp_apply, he,norm_neg]; exact h.born),fun i=>?_,fun i j=>?_⟩
  · rw [retell _ L h.host,he,norm_neg]; exact h.walks i
  rw [retold _ _ L h.host,he,norm_neg]; exact h.wandered i j
lemma roster (h : Flock l d f x r C) (y:Site n) : Flock l d f y r (C*((Decay r y x)⁻¹)^2):=by
  let A:= (Decay r y x)⁻¹; have hp := decay_pos r y x; have he : 1≤A:= (one_le_inv₀ hp).mpr (decay_le h.fund.le ..)
  have ht i : Decay r x (l i)≤ A*Decay r y (l i):= foil h.fund.le ..
  have he': A≤ A^2:=by nlinarith
  refine ⟨h.fund,mul_nonneg h.fee (sq_nonneg _),h.host,h.born.trans (le_mul_of_one_le_right h.fee (he.trans he')),fun i=> ?_,fun i j=>?_⟩
  · rw [mul_assoc]; exact (h.walks i).trans (mul_le_mul_of_nonneg_left ((ht i).trans (mul_le_mul_of_nonneg_right he' (decay_pos ..).le)) h.fee)
  rw [mul_assoc]; exact (h.wandered i j).trans (mul_le_mul_of_nonneg_left ((mul_le_mul (ht i) (ht j) (decay_pos ..).le (mul_nonneg (zero_le_one.trans he) (decay_pos ..).le)).trans_eq (by unfold A; ring)) h.fee)
lemma convoy {g : J→X→Y}{s : Finset J}{w:J→ℝ}(h:0<r)(hp : ∀ i∈s,Flock l d (g i) x r (w i)) : Flock l d (fun y=>∑ i∈s,g i y) x r (∑ i∈s,w i):=by
  induction s using Finset.induction_on with
  | empty=>simpa using! hush (x:=x) (l:=l) (d:=d) (0:Y) h
  | insert i s he H=> simp_rw [sum_insert he]; exact (hp i (mem_insert_self ..)).plus (H (fun j hj=> hp j (mem_insert_of_mem hj)))
lemma breakthrough {U V : X→R} (h:Flock l d U x r C)(p:Flock l d V x r D):Flock l d (fun i=> U i*V i) x r (4*(C*D)):=by
  let P:=Decay (n:=n) r; have hp i j : 0≤P i j:= (decay_pos ..).le; have hC:=h.fee; have hD:=p.fee
  refine ⟨h.fund,mul_nonneg (by norm_num) (mul_nonneg hC hD), h.host.mul p.host,?_ ,fun i=>?_ ,fun i j=>?_⟩
  · exact (norm_mul_le ..).trans ((mul_le_mul h.born p.born (norm_nonneg _) hC).trans (le_mul_of_one_le_left (mul_nonneg hC hD) (by norm_num)))
  · rw [made _ h.host p.host]
    have hu: 0≤ P x (l i):=hp ..
    refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul (h.walks i) p.born (norm_nonneg _) (mul_nonneg hC hu))) ((norm_mul_le ..).trans (mul_le_mul h.born (p.walks i) (norm_nonneg _) hC))).trans ?_)
    change C * P x (l i) * D+ C*(D*P x (l i))≤4*(C*D)*P x (l i); nlinarith only [mul_nonneg hC (mul_nonneg hD hu)]
  rw [rotate_area _ _ h.host p.host]
  have hu1:=hp x (l i); have hu2:=hp x (l j)
  exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (h.wandered i j) p.born (norm_nonneg _) (by apply mul_nonneg hC; exact mul_nonneg hu1 hu2))) ((norm_mul_le ..).trans (mul_le_mul (h.walks j) (p.walks i) (norm_nonneg _) (mul_nonneg hC hu2))))) ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (h.walks i) (p.walks j) (norm_nonneg _) (mul_nonneg hC hu1))) ((norm_mul_le ..).trans (mul_le_mul h.born (p.wandered i j) (norm_nonneg _) hC))))).trans_eq (by ring))
end Flock
end YM.QCD.Eyrie
