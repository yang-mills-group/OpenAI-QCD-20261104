import YM.Push.GRID_APPROXIMATION.KernelLocal
import YM.Branch.Covariant
import YM.QCD.Tide.Seize
import YM.QCD.Tide.Gleam
/-! # linear backward use BOREL. inherit baseline conditional cone, no independent tags assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology ComplexOrder
variable {A:Type*}[Fintype A] {n c f : Side} {F : ℕ} {β:ℝ}{S:StepData c f}
noncomputable def brook (S:StepData c f) (β:ℝ)(P: Grid c→Alg A) (U:Grid f) := ∫ V,S.density β U V • P V ∂prior su c
variable (hB:S.patch.Branches S.kernel su)(X Y:Set (Site c))(P Q: Grid c→Alg A) (hP:Stays P)(hQ:Stays Q)
include hP hB
lemma delta (β:ℝ):Stays (fun u:Grid f×Grid c=> S.density β u.1 u.2 • P u.2):=by
    obtain ⟨a,b⟩:=den_env (S.isKernel hB β); exact Stays.acts (p:=fun u:Grid f×Grid c=>S.density β u.1 u.2) ⟨a,b⟩ (f:=fun u=>P u.2) (hP.travel measurable_snd)
lemma deltaPay (U:Grid f):Integrable (fun V=>S.density β U V • P V) (prior su c):=((delta hB P hP β).travel (p:=fun V=> (U,V)) (measurable_const.prodMk measurable_id)).intg _
lemma brain (β:ℝ):Stays (brook S β P):=by
     obtain ⟨a,C,hC⟩:=delta hB P hP β; exact ⟨a.stronglyMeasurable.integral_prod_right'.measurable,C,fun U=> by simpa [Measure.real,brook] using norm_integral_le_of_norm_le_const (μ:=prior su c) (f:=fun V=> S.density β U V • P V) (ae_of_all _ fun V=> hC (U,V))⟩ -- check sig
lemma dink (U:Grid f)(i:Finset A): coef i (brook S β P U)= Push.GridApprox.back S β (fun V=>coef i (P V)) U :=by
     let Q:= ((coef i).toContinuousLinearMap).restrictScalars ℝ; unfold brook; change Q _= _ ; rw [← Q.integral_comp_comm (deltaPay hB P hP U)]; unfold Push.GridApprox.back; apply integral_congr_ae; refine ae_of_all _ fun V=>?_ ; dsimp only; rw [map_smul]; change (S.density β U V) • ((coef i) (P V)) = _; rw [Complex.real_smul]
lemma mentor (i:Finset A): Envelope (fun V=>coef i (P V)):= by obtain ⟨a,b⟩:= hP.flows (continuous_coef i); exact ⟨a,b⟩ -- hB unused
lemma deltaL (H:LocalOn X P)(Y:Set (Site f))(hY:∀ x∈ X,window (S.ratio.embed x) (reach S.patch) ⊆ Y):LocalOn Y (brook S β P):=by
    intro U V h; nth_rw 1 [← write (brook S β P U)]; nth_rw 1 [← write (brook S β P V)]; apply sum_congr rfl; intro i _; rw [dink hB P hP,dink hB P hP,back_local hB (mentor hB P hP i) (show LocalOn X _ from fun A B e=>congr_arg (coef i) (H A B e)) β Y hY U V h]
include hQ
lemma urban (H:LocalOn X P)(W:LocalOn Y Q)(hw: Disjoint X Y)(U:Grid f): brook S β (P*Q) U= brook S β P U * brook S β Q U:=by
   let Z:=fun i j: Finset A=>mono i * mono j
   let p (i:Finset A)(V:Grid c):= coef i (P V); let q (i:Finset A)(V:Grid c):= coef i (Q V)
   have hx i j: Push.GridApprox.back S β (p i*q j) U= coef i (brook S β P U)*coef j (brook S β Q U):=by
       rw [dink hB P hP,dink hB Q hQ]; exact congr_fun (back_factors hB (mentor hB P hP i) (mentor hB Q hQ j) (hp:=fun A B e=>congr_arg (coef i) (H A B e)) (ht:= fun A B e=>congr_arg (coef j) (W A B e)) hw β) U
   let L (i j: Finset A)(V:Grid c): ℂ:= S.density β U V * (p i V*q j V)
   have he(V:Grid c): S.density β U V • (P*Q) V=∑ i:Finset A,∑ j:Finset A, L i j V • Z i j:=by
       conv_lhs=> rw [Pi.mul_apply,← write (P V), ← write (Q V),sum_mul]
       simp_rw [mul_sum,smul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [smul_mul_assoc,mul_smul_comm,smul_smul]; unfold L; rw [mul_smul (S.density β U V:ℂ)]; rfl
   have hp i j:Integrable (L i j) (prior su c):=(back_slice (S.isKernel hB β) ((mentor hB P hP i).mulC (mentor hB Q hQ j)) U).integrableC _ -- edit
   unfold brook; change (∫ V, _ ∂prior su c)=brook S β P U * brook S β Q U
   simp_rw [he]; rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> (hp i j).smul_const _))]; simp_rw [integral_finsetSum _ (fun j _ => (hp _ j).smul_const _),integral_smul_const];
   conv_rhs=> rw [← write (brook S β P U),← write (brook S β Q U),sum_mul]
   simp_rw [mul_sum]
   apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [smul_mul_assoc,mul_smul_comm,smul_smul]; exact congr_arg (· • Z i j) (hx i j)
omit hQ
end YM.QCD.Tide
