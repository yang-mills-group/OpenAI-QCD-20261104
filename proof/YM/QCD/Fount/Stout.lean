import YM.QCD.Fount.Datum
/-! # Scale calculus auxiliary all witness. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lattice MeasureTheory Wilson Function Finset Filter Set Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open PhysicalNext.Repeat Lapis ConnectedActivityE6 Push Push.Uniform Blaze Brush Poll Coat
open Cove Reggae
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]{u v b A w C:ℝ}{f:X→Y}{n k:ℕ}
-- Pools weighted. Caller constant fetched at any mask. Weighted norms on all estimates.
lemma pond (ha:0<u) (h:k≤n) (hq:0 ≤ C) (hb : 0 ≤ b) (hp: ∀ y∈ ball 0 u,ContDiffAt ℝ n f y)
    (hg : ∀ i, k ≤ i → i≤n →∀ y∈ball 0 u,normJ i f y * u^i ≤ C) (h₀: ∀ i:ℕ,i<k→ normJ i f 0*u^i ≤ b) :
    ∀ y∈ball 0 u,Brush n (C+(k:ℝ)*b) u⁻¹ f y:= by
  have ht : ∀ i:ℕ, ∀ (hi:i ≤ k), ∀ y∈ball 0 u,normJ i f y * u^i ≤ C + ((k-i:ℕ):ℝ)*b:= by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self=> intro y hy; rw [Nat.sub_self, Nat.cast_zero,zero_mul,add_zero]; exact hg k le_rfl h _ hy
    | of_succ i hi ih=>
      intro x hx
      let w:= iteratedFDeriv ℝ i f
      let m:=C+ ((k-(i+1):ℕ):ℝ)*b
      have hm : 0 ≤ m:=by unfold m; positivity
      have hV : ‖w x-w 0‖ ≤ m/u^(i+1)*u:= by
        have ht:= (convex_ball (0:X) u).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (C:=m/u^(i+1))
          (f:=w) (fun y hy=>((hp y hy).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (hi.trans_le h)))) (fun y hy=>?_) (mem_ball_self ha) hx
        · rw [sub_zero] at ht; exact ht.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (by positivity))
        rw [show ‖fderiv ℝ w y‖=_ from norm_fderiv_iteratedFDeriv]; exact (le_div_iff₀ (by positivity)).mpr (ih _ hy)
      have hv : k-i=k-(i+1)+1:=by omega
      change ‖w x‖ * u^i ≤ _
      calc _ ≤ (‖w x-w 0‖+ ‖w 0‖) * u^i := mul_le_mul_of_nonneg_right (by rw [add_comm]; exact norm_le_insert' _ _) (by positivity) -- scope
           _ ≤ _ := by rw [add_mul,hv]; push_cast; apply le_trans (add_le_add (mul_le_mul_of_nonneg_right hV (by positivity)) (h₀ i hi)); apply le_of_eq; field_simp; unfold m; ring
  intro y hy; refine ⟨hp y hy,(inv_pos.mpr ha).le,fun i hi=>?_⟩
  rw [inv_pow,← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos ha i)).mpr
  rcases le_total i k with he'|he'
  · refine (ht i he' y hy).trans ?_; gcongr; exact Nat.sub_le ..
  exact (hg i he' hi y hy).trans (le_add_of_nonneg_right (by positivity))
lemma reborn (hu:0 < u)(h:3≤n)(he: ∀ y∈ball (0:X) u,ContDiffAt ℝ n f y)(hc:∀ i:ℕ, 3 ≤ i → i≤ n → ∀ y∈ball (0:X) u,normJ i f y*u^i ≤ C) (hb:normJ 2 f 0 *u^2≤ b)(hz:fderiv ℝ f 0=0):∀ y∈ball 0 u,Brush n (C+3*b) u⁻¹ (Shellac.off f) y:=by
    let F:=Shellac.off f; let S:=ball (0:X) u; have hh:(0:X)∈S:= mem_ball_self hu
    have hb': 0 ≤ b:= (by apply le_trans _ hb; unfold normJ; positivity)
    have hk (i:ℕ)(hi: i≠0)(hj: i≤n)(x:X)(hx:x∈S): normJ i F x=normJ i f x:=by
       obtain ⟨i,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hi; unfold F Shellac.off normJ; rw [iteratedFDeriv_sub_apply ((he _ hx).of_le (Nat.cast_le.mpr hj)) contDiffAt_const, iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
    have hp:0 ≤ C:=(by apply le_trans _ (hc 3 le_rfl h _ hh); unfold normJ; positivity)
    have hh':=pond hu (f:=F) h hp hb' (fun x hx=>(he _ hx).sub contDiffAt_const) (fun i hi hv x hx=>by rw [hk i (by omega) hv _ hx]; exact hc i hi hv _ hx) (fun i hi=>?_)
    · norm_num at hh'⊢; exact hh'
    interval_cases i
    · simpa [F,Shellac.off,normJ] using hb'
    · simpa only [hk _ one_ne_zero (by omega) _ hh,normJ,norm_iteratedFDeriv_one,hz,norm_zero,zero_mul] using hb'
    rw [hk 2 (by omega) (by omega) _ hh]; exact hb
end YM.QCD.Fount
