import YM.QCD.Dust.Pages
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Hera
open MultiNext.SignedSource.Ease
open Function Filter Lattice Wilson RG Next.Foundations
    AnalyticBridge.VerifiedReset MultiNext.SignedSource MultiNext.SignedSource.Mom MultiNext.SignedSource.Banjo
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {m k : ℕ} {C r τ : ℝ}
    {f : Config G n → ℝ}


variable (h : Charm B X f)(hr: 0≤r)(ht:r≤1)(hc:1≤C)(Q:Rights G k)(hk:k ≤ B.order)(hw:0≤ τ)(hb: B.supBounds o X f (τ*r^3))
variable (h₀:‖f 1‖ ≤ τ*r^5)(h₁:∀ v t,Lyre.Sized t v B o→ Mom.screen X v∈Mom.Maps o X 1 → ‖fderiv ℝ (f ∘ increment 1) 0 v‖ ≤ (t*Q.fee)*τ*r^4)
include h hr ht hc hk hw hb h₀ h₁
private lemma mica (m:ℕ)(hm : m ≤ k) (v : Fin m→ Directions G n)(hv : ∀ i, Promise 2 C r B o X (v i)):
    ‖iteratedFDeriv ℝ m (f ∘ increment 1) 0 v‖≤ ((3*((3*C)^k*r^5))*Q.fee)*τ :=by
    have hh : 1 ≤3*C:=by linarith
    have he : 1 ≤ (3*C)^k := one_le_pow₀ hh; have hx:= Q.large
    by_cases hs:m=0
    · subst m; rw [iteratedFDeriv_zero_apply, Function.comp_apply,YM.Work.G07.at_zero_increment]; apply h₀.trans; rw [mul_comm τ]; let b:=(3*C)^k; have hA:1≤3*b*Q.fee:=by unfold b; nlinarith only [he,hx]
      refine mul_le_mul_of_nonneg_right ?_ hw; exact (le_mul_of_one_le_left (pow_nonneg hr _) hA).trans_eq (by unfold b; ring)
    by_cases he:m=1
    · subst m; obtain ⟨z,hZ,hB,h⟩:=hv 0; rw [iteratedFDeriv_one_apply,hZ,map_sum]; apply (norm_sum_le ..).trans
      let p:= (3*C)^k*r^5*Q.fee*τ
      have hu(j:Fin 3):‖fderiv ℝ (f ∘ increment 1) 0 (z j)‖ ≤ p:=by
         have hm:C ≤ (3*C)^k:=le_trans (by linarith) ((le_self_pow₀ hh (by omega : k≠0)))
         rcases eq_or_ne j.val 0 with hj|hj
         · have hf:= h₁ _ _ (hB j) (by simpa only [hj,Nat.zero_add] using h j (by omega)); rw [hj,Nat.zero_add, pow_one] at hf; apply hf.trans; exact (show _= C*r^5*Q.fee*τ by ring).le.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity)) (by positivity))
         let s:= fun _ : Fin 1=> z j; have h':= Q.born _ s _ (show 1≤ k by omega) (by omega :1 ≤ B.order) (by assumption : Charm B X f) hb (flat_ok ..) (fun i=> hB j)
         rw [Fintype.prod_unique,iteratedFDeriv_one_apply] at h'; apply h'.trans
         refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht (by omega : 2≤j.val+1)) (by positivity : 0 ≤ C)) (show 0≤Q.fee by positivity)) (show 0≤τ*r^3 by positivity)).trans ?_
         exact (show C*r^2*Q.fee*(τ*r^3)=C*r^5*Q.fee*τ by ring).le.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity)) (by positivity))
      apply (Finset.sum_le_sum (s:=Finset.univ) fun j _=> hu j).trans_eq; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; unfold p; norm_cast; ring -- inspect
    have h:= Q.born 1 v (fun _=>3*C*r) hm (hm.trans hk) h hb (flat_ok ..) (fun i=>by convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num)
    apply h.trans; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rw [mul_pow]; let s:=3*C; have hx':(3*C)^m*r^m ≤ (3*C)^k*r^2:=mul_le_mul (pow_le_pow_right₀ hh hm) (pow_le_pow_of_le_one hr ht (by omega)) (pow_nonneg hr _) (by positivity); refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (show 0 ≤Q.fee by positivity)) (show 0 ≤ τ*r^3 by positivity)).trans ?_
    calc
      _=(3*C)^k*r^5*Q.fee*τ:=by ring
      _ ≤ _:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num)) (zero_le_one.trans hx)) hw)
lemma crystal (u : Directions G n) (hu : Promise 2 C r B o X u) (he : ∀ e, needed X e → ‖u e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1)
    (hs : ∀ t ∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (t • u))) (hK : 2 ≤ k) (hm : m ≤ k) (v : Fin m → Directions G n)
    (hv : ∀ j, Promise 2 C r B o X (v j)) : ‖iteratedFDeriv ℝ m (f ∘ increment 1) u v‖ ≤ (k+1:ℝ)*(3*((3*C)^k*r^5)) * Q.fee * τ := by
  let F := f ∘ increment (1:Config G n); let z := (3*((3*C)^k*r^5))*Q.fee*τ
  have h0 := Q.large; have hτ := hw
  have H (j) (hj : j ≤ k) (v : Fin j → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) (s : ℝ) (ht' : s ∈ Set.Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ j F (s • u) v‖ ≤ ((k+1-j:ℕ):ℝ)*z := by
    have Hs t i (ht₀ : t ∈ Set.Icc (0:ℝ) 1) (hi : i ≤ k) : ContDiffAt ℝ (i:ℕ∞ω) F (t • u) := (Hera.along h (hs t ht₀)).of_le (Nat.cast_le.mpr (hi.trans hk))
    induction hj using Nat.decreasingInduction generalizing s with
    | self =>
      rw [show k+1-k=1 by omega,Nat.cast_one,one_mul]
      apply (Q.moves 1 _ v (fun _ => 3*C*r) le_rfl hk h hb (hs _ ht') ?_ ?_).trans
      · simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]
        have hh:= mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht hK) (show 0≤ (3:ℝ)^k*C^k from by positivity)
        change _*Q.fee*(τ*r^3) ≤ z
        refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (show 0≤τ*r^3 by positivity)).trans ?_
        unfold z; simp only [mul_pow]; calc
           _ = ((3:ℝ)^k*C^k*r^5)*Q.fee*τ:=by ring
           _ ≤ _:=by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num)) (zero_le_one.trans h0)) hτ
      · intro i hi; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg ht'.1]; exact ⟨mul_le_one₀ ht'.2 (norm_nonneg _) (he i hi).1,(he i hi).2⟩
      intro i; convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num
    | of_succ j hj ih =>
      have ha : ∀ i : Fin (j+1), Promise 2 C r B o X ((Fin.cons u v : Fin (j+1) → Directions G n) i) := Fin.cases (by simpa using hu) (fun i => by simpa using hv i)
      have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t : ℝ => iteratedFDeriv ℝ j F (t • u) v) (fun x hx => (Heir.along_deriv u v x (Hs x (j+1) hx hj)).hasDerivWithinAt)
        (fun x hx => ih (Fin.cons u v) ha x hx) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) ht'
      rw [zero_smul,sub_zero, Real.norm_of_nonneg ht'.1] at H
      have hp := H.trans (mul_le_of_le_one_right (by unfold z; positivity) ht'.2)
      have he : ‖iteratedFDeriv ℝ j F 0 v‖ ≤ z := mica h hr ht hc Q hk hw hb h₀ h₁ j (Nat.le_of_lt hj) v hv
      refine (norm_le_of_pair hp he).trans_eq ?_
      rw [show k+1-j=k+1-(j+1)+1 by omega, Nat.cast_add_one, add_mul,one_mul]
  have hx := H m hm v hv 1 (by simp); rw [one_smul] at hx
  refine hx.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by unfold z; positivity)).trans_eq ?_); unfold z; push_cast; ring
where norm_le_of_pair {x y a b : ℝ} (h : ‖x-y‖ ≤ a) (he : ‖y‖ ≤ b) : ‖x‖ ≤ a+b :=
  (by simpa using (norm_add_le (x-y) y).trans (add_le_add h he))
end YM.PhysicalNext.JointLoad.Hera
