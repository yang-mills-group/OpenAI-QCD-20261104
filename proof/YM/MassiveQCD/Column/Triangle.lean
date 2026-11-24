import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ray

/-! # Split gauge projection

Perturb the *true vacuum*. Weaken Ψ vanishing of the unmarked Hessian's scalar part
through weight three (only body), keeping the FULL local gauge orbit Ward identity
on each support and Woven smoothness. The distinction from `Heir.ray`, a weight-4 jet
contraction, is vital: we won't independently reset the gauge parameter on a perturbation.
This proves the homogeneous deterministic profile cost at that sharp weight, with no loss
in the chart constants over the usual unmarked taper. With the actual curved-sector Promises
in the Step payments, this is a tool toward a uniform estimate on every mass perturbation column. Uses the same PMOM interpolation/germ as in Ghost/Ray, but weaker ends.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson RG Labels Source Source.Drops Next.Foundations
  MultiNext.SignedSource MultiNext.SignedSource.Mom AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {k m : ℕ}
    {f : Config G n → ℝ}

structure PointedSeed (B : BudgetPoint) (o : Site n) (X : Support n) (f : Config G n → ℝ) : Prop where
  good : B.Regular X f
  site : o∈X
  value : f 1 = 0

section cancel
variable (g : G.Simple) (h : PointedSeed B o X f) (hX : Nonwrapping X o) (hn : 2 ≤ n.val)
include g h hn hX
set_option maxHeartbeats 1000000 in
lemma PointedSeed.three : Mediator.valence (fun i => (Mom.Maps o X i (G:=G): Set _)) 3 (f ∘ increment 1) := by
  let K (i) := (Mom.Sites o X i (G:=G) (d:=3): Set (Mom.Slate G n 3))
  let L (i) := (Mom.Maps o X i (G:=G) : Set (Directions G n))
  let q := optic X o (G:=G) (d:=3)
  let F := f ∘ increment (1:Config G n)
  have hn' : 2 ≤ n.val := hn
  have hf : ContDiffAt ℝ 3 F 0 := (h.good.smooth 1 (flat_ok B X)).of_le (Nat.cast_le (α:=ℕ∞ω) |>.mpr (le_trans (by decide : 3 ≤ 6) B.order_ge))
  have hg := flat_critical g h.good
  obtain ⟨hq,h₀⟩:=osmotic (d:=3) (G:=G) X o
  have hD : ContDiffAt ℝ 3 (F ∘ q) 0 := (h₀.symm ▸ hf).comp (f:=q) 0 (hq.of_le le_top)
  have hc : Mediator.curry K L 3 q := Mom.along o X hn' hX
  apply Mediator.attenuation K L q F (hq.of_le le_top) h₀ hf (fun i hi hd => Mom.covers o X hX hn' i hi hd) hc
  let H := hol G
  letI : NormedAddCommGroup (Mom.Slate G n 3) := inferInstanceAs (NormedAddCommGroup ((Site n → G.Color) × Snap G 3))
  letI : NormedSpace ℝ (Mom.Slate G n 3) := inferInstanceAs (NormedSpace ℝ ((Site n → G.Color) × Snap G 3))
  have ht : ((fun x => (f x:ℂ)) ∘ increment 1) ∘ q=ᶠ[𝓝 (0:Mom.Slate G n 3)]
      (fun v => (f (H.testLinks 3 o (expand 3 v.2) 1):ℂ)) := Mom.appears (fun u v hv => congrArg Complex.ofReal (h.good.sites u v hv))
        (fun s x => congrArg Complex.ofReal (h.good.symmetry s x)) H
  let π : Mom.Slate G n 3 →L[ℝ] Mom.Slate G n 3 := (ContinuousLinearMap.inr ..).comp (ContinuousLinearMap.snd ..)
  have hP : F ∘ q =ᶠ[𝓝 0] (F ∘ q) ∘ π := by
    filter_upwards [ht,ht.comp_tendsto (show Tendsto π (𝓝 0) (𝓝 0) from by simpa using π.continuous.tendsto 0)] with v hv hv'
    exact Complex.ofReal_inj.mp (hv.trans hv'.symm)
  intro m a v hA
  by_cases hV : ∃ i, a i ≤ 1
  · obtain ⟨i,hi⟩ := hV
    have hv : π (v i) = 0 := Prod.ext rfl (funext fun j => ((hA.1 i).2.2 j (by omega)))
    have hm : m ≤ 3 := le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun j _ => (hA.1 j).1)) hA.2
    rw [(hP.iteratedFDeriv (𝕜:=ℝ) m).eq_of_nhds,jets_linear π (hD.of_le (show (m:ℕ∞ω) ≤ 3 by exact_mod_cast hm)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact ContinuousMultilinearMap.map_coord_zero _ i hv
  have hv (i) : 2 ≤ a i := by have h := not_exists.mp hV i; omega
  have hm : m*2 ≤ 3 := le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 2) (fun j _ => hv j)) hA.2
  have hJ := Work.F03.hessian_comp h₀ (germ_diff h.good) (hq.of_le le_top) hg
  cases m
  · rw [iteratedFDeriv_zero_apply]; change F (q 0) = 0; rw [show q 0=0 from h₀]; exact (congrArg f (at_zero 1)).trans h.value
  · rename_i m
    by_cases he : m=0
    · subst m; rw [iteratedFDeriv_one_apply, show fderiv ℝ (F ∘ q) 0 = 0 from hJ.1]; rfl
    omega

lemma PointedSeed.disappear {a : Fin m → ℕ} (v : Fin m → Directions G n) (ha : ∀ i, 0 < a i) (he : ∑ i,a i ≤ 3)
    (hs : ∀ i, screen X (v i)∈Mom.Maps o X (a i)) : iteratedFDeriv ℝ m (f ∘ increment 1) 0 v = 0 := by
  let F := f ∘ increment (1:Config G n)
  have hQ : F = F ∘ screen (G:=G) X := funext fun u => h.good.sites _ _ fun i hi hh => by
    rw [increment,increment,Mom.screen_at,if_pos (show needed X i from ⟨hi,hh⟩)]
  have hm : m ≤ B.order := (le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun j _ => (show 1 ≤ a j from ha j))) he).trans
    (le_trans (by decide : 3 ≤ 6) B.order_ge)
  have hf := (h.good.smooth 1 (flat_ok B X)).of_le (Nat.cast_le (α:=ℕ∞ω) |>.mpr hm)
  change iteratedFDeriv ℝ m F 0 v=0
  rw [hQ, jets_linear _ (f:=F) hf]
  exact h.three g hX hn m a _ ⟨fun i => ⟨ha i, hs i⟩,he⟩
private lemma triangle (a : Fin m → ℕ) (v : Fin m → Directions G n)
    (he : ∑ i,a i ≤ 3) (hA : ∀ i, 1 ≤ a i) (hv : ∀ i, a i ≤ 2 → screen X (v i) ∈ Mom.Maps o X (a i)) :
    iteratedFDeriv ℝ m (f ∘ increment 1) 0 v = 0 := by
  by_cases hx : ∃ i, 2 < a i
  · obtain ⟨i,hi⟩ := hx
    have hm : (Finset.univ.erase i).card+1=m := (Finset.card_erase_add_one (Finset.mem_univ i)).trans (by simp)
    have hs := Finset.sum_le_sum (s:= Finset.univ.erase i) (f:=fun _ => 1) (fun i _ => hA i); rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at he
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
    change (Finset.univ.erase i).card ≤ ∑ j ∈ Finset.univ.erase i, a j at hs
    have hM : 0 < m := i.pos
    obtain rfl : m=1 :=by omega
    rw [iteratedFDeriv_one_apply, show fderiv ℝ (f ∘ increment 1) 0=0 from flat_critical g h.good]
    rfl
  exact h.disappear g hX hn v hA he (fun i => hv i (le_of_not_gt (fun h => hx ⟨i,h⟩)))


variable {C r τ : ℝ}
open MultiNext.SignedSource.Banjo
variable (hb : B.supBounds o X f τ) (hr : 0 ≤ r) (ht : r ≤ 1) (hc : 1 ≤ C) (Q : Rights G k) (hk : k ≤ B.order)

include hb hr ht hc hk

private lemma taper_triangle (hm : m ≤ k) (v : Fin m → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) :
    ‖iteratedFDeriv ℝ m (f ∘ increment 1) 0 v‖ ≤ ((3*C)^k*r^4) * Q.fee * τ := by
  choose w hw hW hP using hv
  let T := iteratedFDeriv ℝ m (f ∘ increment 1) 0; change ‖T v‖ ≤ _
  have h0 := Q.large; have hτ := hb.1
  rw [funext hw,T.map_sum (α:=fun _ => Fin 3)]
  apply (norm_sum_le ..).trans
  refine (Finset.sum_le_sum (g:=fun _ => (C^m*r^4)*Q.fee*τ) (fun j _ => ?_)).trans ?_
  · let a (i : Fin m) := (j i).val+1
    by_cases he : ∑ i,a i ≤ 3
    · rw [show T _ = 0 from triangle g h hX hn a _ he (fun _ => by unfold a; omega) (fun i hi => hP i _ (show (j i).val < 2 from Nat.lt_of_succ_le hi)),norm_zero]
      positivity
    apply (Q.born 1 _ (fun i => C*r^(a i)) hm (hm.trans hk) h.good hb (flat_ok B X) (fun i => hW i _)).trans
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht (by omega)) (by positivity)) (by positivity)) hτ
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have hi := pow_le_pow_right₀ (show 1 ≤ 3*C by linarith) hm
  calc
    _ = ((3*C)^m*r^4)*Q.fee*τ := by push_cast; rw [mul_pow]; ring
    _ ≤ _ := by gcongr

/-- Leading rescaled E deterministic pay at matching `u,v`.
Caller has to fit these actual chart conditions, see also `coaches`.
No PiVanish assumptions. -/
lemma PointedSeed.profile (u : Directions G n) (hu : Promise 2 C r B o X u) (he : ∀ e, needed X e → ‖u e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1)
    (hs : ∀ t ∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (t • u))) (hK : 4 ≤ k) (hm : m ≤ k) (v : Fin m → Directions G n)
    (hv : ∀ j, Promise 2 C r B o X (v j)) : ‖iteratedFDeriv ℝ m (f ∘ increment 1) u v‖ ≤ (k+1:ℝ)*((3*C)^k*r^4) * Q.fee * τ := by
  let F := f ∘ increment (1:Config G n); let z := ((3*C)^k*r^4)*Q.fee*τ
  have h0 := Q.large; have hτ := hb.1
  have H (j) (hj : j ≤ k) (v : Fin j → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) (s : ℝ) (ht' : s ∈ Set.Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ j F (s • u) v‖ ≤ ((k+1-j:ℕ):ℝ)*z := by
    have Hs t i (h : t ∈ Set.Icc (0:ℝ) 1) (hi : i ≤ k) : ContDiffAt ℝ (i:ℕ∞ω) F (t • u) := (along ‹PointedSeed ..›.good (hs t h)).of_le (Nat.cast_le.mpr (hi.trans hk))
    induction hj using Nat.decreasingInduction generalizing s with
    | self =>
      rw [show k+1-k=1 by omega,Nat.cast_one,one_mul]
      apply (Q.moves 1 _ v (fun _ => 3*C*r) le_rfl hk ‹PointedSeed ..›.good hb (hs _ ht') ?_ ?_).trans
      · simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]; unfold z; rw [mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht hK) (by positivity)) (by positivity)) hτ
      · intro i hi; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg ht'.1]; exact ⟨mul_le_one₀ ht'.2 (norm_nonneg _) (he i hi).1,(he i hi).2⟩
      intro i; convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num
    | of_succ j hj ih =>
      have ha : ∀ i : Fin (j+1), Promise 2 C r B o X ((Fin.cons u v : Fin (j+1) → Directions G n) i) := Fin.cases (by simpa using hu) (fun i => by simpa using hv i)
      have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t : ℝ => iteratedFDeriv ℝ j F (t • u) v) (fun x hx => (along_deriv u v x (Hs x (j+1) hx hj)).hasDerivWithinAt)
        (fun x hx => ih (Fin.cons u v) ha x hx) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) ht'
      rw [zero_smul,sub_zero, Real.norm_of_nonneg ht'.1] at H
      have hp := H.trans (mul_le_of_le_one_right (by unfold z; positivity) ht'.2)
      have he : ‖iteratedFDeriv ℝ j F 0 v‖ ≤ z := taper_triangle g ‹PointedSeed ..› hX hn hb hr ht hc Q hk (Nat.le_of_lt hj) v hv
      refine (norm_le_of_pair hp he).trans_eq ?_
      rw [show k+1-j=k+1-(j+1)+1 by omega, Nat.cast_add_one, add_mul,one_mul]
  have hx := H m hm v hv 1 (by simp); rw [one_smul] at hx
  refine hx.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by unfold z; positivity)).trans_eq ?_); unfold z; push_cast; ring
where norm_le_of_pair {x y a b : ℝ} (h : ‖x-y‖ ≤ a) (he : ‖y‖ ≤ b) : ‖x‖ ≤ a+b :=
  (by simpa using (norm_add_le (x-y) y).trans (add_le_add h he))
end cancel

end YM.PhysicalNext.JointLoad.Heir
