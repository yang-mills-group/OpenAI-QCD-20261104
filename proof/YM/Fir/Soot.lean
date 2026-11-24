import YM.Fir.Shine
/-! Recovery of genuine all-axis derivatives on the separated set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Fir.Mesh
open Asymptotics NoteF Set Function Filter Metric
open scoped Topology ContDiff
variable {I X: Type*}[Fintype I] [DecidableEq I] [NormedAddCommGroup X][NormedSpace ℝ X]
noncomputable def wing (x:I→X): (I→ℝ)→L[ℝ] X:= ∑ i,(ContinuousLinearMap.proj (R:=ℝ) i).smulRight (x i)
lemma pin (x:I→X)(z:I→ℝ): wing x z=∑ i,z i • x i:= by unfold wing; simp
lemma thornF (x:I→X)(b:I): wing x (Pi.single b 1)= x b:=by rw [pin]; simp [Pi.single_apply]
variable {f:ℕ→(I→ℤ)→X}{x:I→ℝ}{F:(I→ℝ)→X}{D:I→X}
variable {a:ℕ→ℝ} (ha:∀ i,0<a i)(hT:Tendsto a atTop (𝓝 0))
noncomputable abbrev pursuit (a:ℕ→ℝ) (f:ℕ→ (I→ℤ) → X)(i:ℕ)(b:I)(p:I→ℤ): X:= (a i)⁻¹ • (f i (advanceF b p)-f i p)
lemma poll (q:I→ℤ)(b:I)(a:ℝ): imageF a (advanceF b q)-imageF a q= a • Pi.single b 1:=by
   funext i; by_cases h:i=b; · subst i; simp [Pi.single_apply,advanceF,imageF]; ring
   simp [h,Pi.single_apply,advanceF,imageF]
include ha hT
set_option maxHeartbeats 340000 in
lemma appeared (hv:∀ᶠ y in 𝓝 x, seesF (fun i=>imageF (a i)) f y (F y)) (hd:∀ b:I,seesF (fun i=>imageF (a i)) (fun i=> pursuit a f i b) x (D b)): HasFDerivAt F (wing D) x:=by
   apply HasFDerivAt.of_isLittleO; rw [isLittleO_iff]; intro ε he
   let N:ℝ:= ↑(Fintype.card I); have hN:0 ≤ N:= Nat.cast_nonneg _; let k:= ε/(N+1); have hk:0 < k:= div_pos he (by linarith); have hz:N*k ≤ ε:= (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hk.le).trans_eq (by unfold k; field_simp)
   let X' (i):=imageF (I:=I) (a i); let W:=noteF X' x
   have H:∀ᶠ p in W,∀ b:I, pursuit a f p.1 b p.2∈ball (D b) k:= eventually_all.mpr fun b=> (hd b).eventually (ball_mem_nhds _ hk)
   obtain ⟨r,hr,H⟩:= circles H
   let G(i:ℕ)(q:I→ℤ):= f i q-(wing D) (imageF (a i) q); let F1(z:I→ℝ):= F z-(wing D) z
   have hu:∀ᶠ i in atTop, ∀ p,imageF (a i) p∈ball x r→∀ q,imageF (a i) q∈ball x r→ dist (G i p) (G i q)≤ N*k * dist (imageF (a i) p) (imageF (a i) q):= H.mono (fun i hi p hp q hq=> by
        rw [mul_assoc]; apply snake _ hr (ha i) hk.le _ _ _ hp hq; intro u hu b he
        let w:= advanceF b u; have hh:G i w-G i u= a i• (pursuit a f i b u-D b):=by unfold G pursuit; rw[smul_sub,smul_inv_smul₀ (ha i).ne',sub_sub_sub_comm,←map_sub,poll, map_smul,thornF]
        change dist (G i w) (G i u)≤_; rw [dist_eq_norm,hh,norm_smul,Real.norm_of_nonneg (ha i).le,←dist_eq_norm,mul_comm]; exact mul_le_mul_of_nonneg_right (Metric.mem_ball.mp (hi u hu b)).le (ha i).le)
   let V(z:I→ℝ)(i):=imageF (a i) (markF (a i) z)
   have hG(z:I→ℝ)(hp:seesF X' f z (F z)): Tendsto (fun i=> G i (markF (a i) z)) atTop (𝓝 (F1 z)):= (track ha hT hp).sub (((wing D).continuous.tendsto _).comp (visible z ha hT))
   filter_upwards [ball_mem_nhds _ hr,hv] with y hy hp
   have hh: dist (F1 y) (F1 x) ≤ N*k*dist y x := le_of_tendsto_of_tendsto ((hG y hp).dist (hG x (mem_of_mem_nhds hv))) (((visible y ha hT).dist (visible x ha hT)).const_mul _) (by filter_upwards [hu,(visible y ha hT).eventually (isOpen_ball.mem_nhds hy),(visible x ha hT).eventually (ball_mem_nhds _ hr)] with i hi hv hw; exact hi _ hv _ hw)
   rw [dist_eq_norm,dist_eq_norm] at hh; unfold F1 at hh; rw [sub_sub_sub_comm,←map_sub] at hh; exact hh.trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
end YM.Fir.Mesh
#print axioms YM.Fir.Mesh.appeared
