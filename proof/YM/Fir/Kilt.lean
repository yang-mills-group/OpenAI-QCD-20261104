import YM.Fir.Chest
/-! Exact quotients all conventions; Ranger caps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ}
open Finset
include hp hr
lemma ticking (M:ℕ)(c b:ℝ)(hc: 0 ≤ c)(h₁:0 ≤ b):∃ m:ℕ,∃ A:ℝ,0 ≤ A ∧ ∀ r:ℝ, 0<r → r ≤ 1 →∃ j≥M, C.S.spacing j<r∧ c*Real.exp (b*Hub.clock C.S j) ≤A * r⁻¹^m:=by
    obtain ⟨W,h⟩:=eventually_atTop.mp (hr.track 1 zero_lt_one); let N:= max M W
    obtain ⟨m,hm⟩:=exists_nat_gt (b*2); refine ⟨m,max c ((c*Real.exp (b*Hub.clock C.S N))), hc.trans (le_max_left ..),fun r hr hr' =>?_⟩
    let q:= Nat.find (shyness ‹C.Path β e› r hr N); have hN := Nat.find_spec (shyness ‹C.Path β e› r hr N);
    have hV:(c*Real.exp (b*Hub.clock C.S q)) ≤ max c ((c*Real.exp (b*Hub.clock C.S N)))*r⁻¹^m:=by
       have hψ : 1 ≤ r⁻¹^m:= one_le_pow₀ (one_le_inv₀ hr |>.mpr hr')
       by_cases he:q=N; rw [he]; exact (le_max_right ..).trans (le_mul_of_one_le_right (hc.trans (le_max_left ..)) hψ)
       let p:=q-1; have hp:N ≤ p:=by have h:N ≤ q:=hN.1; unfold p; omega
       have hh : q=p+1:=by unfold p; have h:N ≤ q:= hN.1; omega
       have ht : r ≤ C.S.spacing p:= le_of_not_gt fun h0=>by have hz:q ≤ p:= Nat.find_min' (shyness ‹C.Path β e› r hr N) ⟨hp,h0⟩; omega
       have hγ : Hub.clock C.S p ≤ Real.log r⁻¹:= Real.log_le_log (inv_pos.mpr (space0 C.S _)) (inv_le_inv₀ (space0 C.S _) hr |>.mpr ht) -- inverse_le_inv arg order
       apply (mul_le_mul_of_nonneg_left _ hc).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans hψ)); rw [← Real.exp_log (pow_pos (inv_pos.mpr hr) m), Real.log_pow]; apply Real.exp_monotone; change b*clock C.S q ≤ _; rw [hh]; refine le_trans (mul_le_mul_of_nonneg_left (h p ((le_max_right ..).trans hp)) h₁) ?_; have hp':(1+(1:ℝ))=2:=by norm_num
       rw [hp']; nlinarith only [mul_le_mul_of_nonneg_left hγ (mul_nonneg h₁ (by norm_num: (0:ℝ)≤2)),mul_le_mul_of_nonneg_right hm.le (Real.log_nonneg (one_le_inv₀ hr|>.mpr hr'))]
    exact ⟨q,(le_max_left ..).trans hN.1,hN.2,hV⟩
include G
variable (d:Fin n→ℕ)
lemma arctic (v:(i:Fin n)→Label (d i)):∃ m:ℕ,∃ A:ℝ,0 ≤ A ∧∀ r:ℝ,0<r → r ≤ 1 →∀ᶠ i in atTop,∀ f:Strings n,localSep C i f r→ ‖plain P d i f v‖ ≤ A*r⁻¹^m:=by
    let V(k:Fin n):= (G (d k)).rise; obtain ⟨M,hM⟩:=eventually_atTop.mp ((eventually_all.mpr fun i:Fin n=>(V i).nest).and (hr.high.eventually_gt_atTop (6*n)))
    let g(i:Fin n):= ‖v i‖*(V i).v; let c:= ∏ i,g i; let b:= budgetD 1 d; have hb:0 ≤ b:= Finset.sum_nonneg fun i _=> add_nonneg (by positivity) zero_le_one
    have he :0 ≤ c:=Finset.prod_nonneg fun i _=> mul_nonneg (norm_nonneg _) (V i).green; obtain ⟨m,A,hA,H⟩:= ticking hp hr M c b he hb
    refine ⟨m,A,hA,fun r hx hz=>?_⟩; obtain ⟨j,hj,hS,h⟩:= H r hx hz; filter_upwards [eventually_all.mpr (hM j hj).1,hp.uv.tendsto_atTop.eventually_ge_atTop (j+1)] with i hi ht f hf
    let V'(k:Fin n):= Hub.rayM C.S (d k) 1 (g k) j; refine le_trans (reapS i j (fun k=> stem P (d k) i (v k)) V' hp ?_ f (tide _ _ _ hf (le_trans (Nat.le_succ _) ht) hS) (hM _ hj).2 ht) ?_
    · intro k; have hu: V' k = ‖v k‖ * Hub.rayM C.S (d k) 1 (V k).v j:=by unfold V' Hub.rayM g; ring
      rw [hu]; exact hi _ _
    change (∏ k:Fin n,V' k)≤_; have hh:(∏ k:Fin n,V' k)= c*Real.exp (b*Hub.clock C.S j):=(Hub.invests ..).trans (Hub.priceTo ..)
    rwa [hh]
omit G hr
variable {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {x:Points n}
include hφ
lemma shipH {r:ℝ}(he:0<r)(h:spaced r x) :∀ᶠ p in Watch C φ x,localSep C (φ p.1) p.2 (r/2/2):=by
     let I:= {i:Fin n×Fin n// i.1≠i.2}; suffices ht:∀ᶠ y in Watch C φ x,∀ i:I,let k:= φ y.1; r/2/2≤ C.S.spacing (C.N k)*separation (wrap _ (y.2 i.val.1)) (wrap (C.S.side (C.R k) (C.N k)) (y.2 i.val.2)) by exact ht.mono fun y hy i j hij=> hy ⟨(i,j),hij⟩
     apply eventually_all.mpr; intro i; let f(y:Points n):= dist (y i.val.1) (y i.val.2); have hv:r/2<f x:=lt_of_lt_of_le (half_lt_self he) ((h i.val.1 i.val.2 i.property).trans ((dist_pi_le_iff dist_nonneg).mpr fun b:Axis=> PiLp.dist_apply_le (x i.val.1) (x i.val.2) b))
     have hX:Continuous f:=by unfold f; fun_prop
     have hx:= approach (v:=fun k=>pollF C n (φ k)) (x:=x); filter_upwards [((hφ.comp beyond).eventually (fullPrice hp (r/2) (f x+1))), ((hX.tendsto x).comp hx).eventually (Ioo_mem_nhds hv (lt_add_one _))] with y hy hh; exact hy _ _ hh.1.le hh.2.le
include hr G
variable {Z:SpaceZ}(H:Ability P φ Z)
include H
lemma expanse (v:(i:Fin n) → Label (d i)):∃ m:ℕ,∃ A:ℝ,0 ≤ A∧∀ r:ℝ,0 < r → r ≤ 1 → ∀ y:Points n,spaced r y →  ‖Z n d y v‖≤A*r⁻¹^m:=by
    obtain ⟨m,A,hA,h⟩:= arctic (G:=G) hp hr d v; refine ⟨m,A*4^m,by positivity,fun r he hL y hy=>?_ ⟩; let w:=r/2/2; have hv:0 < w:=half_pos (half_pos he); have ht:w ≤ 1:=by unfold w; linarith
    letI:=alive hp hφ y; have hx: w⁻¹= (4*r⁻¹):=by unfold w; field_simp <;> ring
    rw [mul_assoc,← mul_pow,←hx]; apply le_of_tendsto ((H.excels n d y (spaced_conf he hy) v).norm); filter_upwards [(hφ.comp beyond).eventually (h w hv ht), shipH hp hφ he hy] with k hh hk; exact hh _ hk
end YM.Massive.Fir
#print axioms YM.Massive.Fir.expanse
