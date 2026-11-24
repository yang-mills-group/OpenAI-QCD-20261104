import YM.Tawny.Vista
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Perla
variable {n:ℕ}
noncomputable def plain (d:ℕ):GPol →ₗ[ℂ] Pol d:= LinearMap.flip (TensorProduct.mk ℂ _ _) (1:SpinPol d)
variable (x:GPol)
local notation "P"=> plain d
lemma plainP:P x=x⊗ₜ[ℂ](1:SpinPol d):=rfl
lemma plain_cap (h:x ∈ Labels.limited su (d/2)):P x ∈ UV.cap d:=by
    rw [Labels.limited,MvPolynomial.restrictSupport_eq_span] at h
    induction h using Submodule.span_induction with
    | mem x h=> rcases h with ⟨i,hi,rfl⟩; change Labels.height i≤d/2 at hi; have he : weight (d:=d) (i,∅) ≤ d:=by simp only [UV.weight,sum_empty,add_zero]; omega
                rw [show P (MvPolynomial.monomial i 1)= UV.gen (d:=d) (i,∅) from by rw[plainP]; unfold UV.gen; simp]; exact Submodule.subset_span ⟨_,he,rfl⟩
    | zero=> rw [map_zero]; exact Submodule.zero_mem _
    | smul a b _ h=> rw[map_smul]; exact Submodule.smul_mem _ _ h
    | add a b _ _ h k=> rw[map_add]; exact Submodule.add_mem _ h k
lemma plainT (s:Signed)(w:EuPin)(hw:w.Lifts s): pinAct w (P x)= P (Labels.rotated s.ortho x):=by rw[plainP,pinAct,TensorProduct.map_tmul]; simp only [AlgHom.toLinearMap_apply, show w.coord=_ from hw,map_one]; rfl
abbrev changeL := Labels.changed (G:=su) (fun _=>UV.recolor)
lemma plainX : chargeAct (P x)= P (changeL x):=by rw[plainP,chargeAct,TensorProduct.map_tmul]; simp only [AlgHom.toLinearMap_apply,map_one]; rfl
lemma earnedT (h:x∈ Labels.localFields su (d/2)):P x∈ labels d:=by
    rw [label_law]; refine ⟨plain_cap x h.1,fun u=>?_⟩; rw[plainP,colorAct,TensorProduct.map_tmul]; simp_rw [AlgHom.toLinearMap_apply,map_one]; congr 1; apply Labels.eval_ext; intro A; exact (Labels.eval_changed ..).trans (h.2 A u)
noncomputable def dowry (x:Labels.Label su (d/2)):Label d:= ⟨P x.val,earnedT x.val x.property⟩
lemma plainQ: Quiet (P x):=by refine ⟨?_,fun s=>?_⟩
                              · rw [plainP,parityAct,TensorProduct.map_tmul]; simp
                              rw [plainP,flavorAct,TensorProduct.map_tmul]; simp
open scoped InnerProductSpace
-- changeC preserves metric in our frame. prove via trace not topology.S.
lemma crowns (a b:su.Color): inner ℝ (reflectColor a) (reflectColor b)= inner ℝ a b:=by
    apply mul_left_cancel₀ (show (su.repDim:ℝ)≠0 from (by exact_mod_cast su.dimPos.ne')); rw [← su.trace_color,← su.trace_color,reflMat,reflMat]
    let X:Mat:=su.colorMat a; let Y:Mat:=su.colorMat b
    change -(Matrix.trace (which true X*which true Y)).re= - (Matrix.trace (X*Y)).re; rw [← which_mul, QCD.bar_trace]; rfl
open StressFlux (pair pairDeriv productPol curl0 curl1 curled)
private lemma lint (v:Axis)(i j:Axis)(X:Labels.Taylor su d): StressFlux.curled d (basis v) i j (UV.recolor X)=reflectColor (StressFlux.curled d (basis v) i j X):=by
   let τ:=LinearMap.toContinuousLinearMap UV.reflectColor; rw [StressFlux.curled_deriv,StressFlux.curled_deriv,map_sub]; have he (i j:Axis) := Maxwell.grad_linear τ (x:=basis v) ((Tensor.diag_smooth (X.val j) ∞).contDiffAt) i; exact congr_arg₂ (·-·) (he i j) (he j i)
variable (i j k l u v:Axis)
abbrev Curl (i j:Axis):= curl0 (G:=su) i j
lemma curl_change(X:Labels.Taylor su 0): Curl i j (UV.recolor X)=reflectColor (Curl i j X):=by
      rw [StressFlux.curl0_value,StressFlux.curl0_value,map_sub]; rfl
lemma mirrorE : changeL (pair su i j k l).val=(pair su i j k l).val:=by
      apply Labels.eval_ext; intro A; rw [changeL,Labels.eval_changed,StressFlux.pair_value,StressFlux.pair_value]; change (↑(inner ℝ (Curl i j (UV.recolor (A 0))) (Curl k l (UV.recolor (A 0)))):ℂ)=_; rw[curl_change,curl_change,crowns]
lemma mirrorD : changeL (pairDeriv su i j k l v).val= (pairDeriv su i j k l v).val:=by
      apply Labels.eval_ext; intro A; rw [changeL,Labels.eval_changed,StressFlux.pairDeriv_value,StressFlux.pairDeriv_value]; change (↑(inner ℝ (Curl i j (UV.recolor (A 0))) (curl1 k l v (UV.recolor (A 1)))):ℂ)=_; rw[curl_change,lint k l v,crowns] -- order
noncomputable def GG (i j k l:Axis):Label 8:= dowry (pair su i j k l)
noncomputable def GE (i j k l v:Axis):Label 10:= dowry (pairDeriv su i j k l v)
lemma grit : fog (GG i j k l).val = (pair su i j k l).val:=unit_fog _
lemma frost : fog (GE i j k l v).val= (pairDeriv su i j k l v).val:=unit_fog _
lemma fullD : (GG i j k l).val= UV.dotF i j k l:=rfl -- check
lemma colorC : chargeAct (GG i j k l).val= (GG i j k l).val:=by change chargeAct (plain _ _)= _; rw [plainX,mirrorE]; rfl
lemma colourE : chargeAct (GE i j k l v).val=(GE i j k l v).val:=by change chargeAct (plain _ _)=_; rw [plainX,mirrorD]; rfl
variable (s:Signed)(w:EuPin)(hw:w.Lifts s)
local notation "σ" i:arg=> (signT s i:ℂ)
include hw
lemma payG : pinAct w (GG i j k l).val=(σ i* σ j*(σ k* σ l)) • (GG (s.perm i) (s.perm j) (s.perm k) (s.perm l)).val:=by
     change pinAct w (plain _ _)= _ • plain _ _; rw[plainT _ s w hw]; have he:= StressFlux.pair_turn (G:=su) s i j k l; let α:ℝ:= ((signT s i* signT s j)*(signT s k*signT s l)); have hP : Labels.rotated s.ortho _ = (↑α:ℂ) • (pair su (s.perm i) (s.perm j) (s.perm k) (s.perm l)).val:= congr_arg Subtype.val he; rw [hP,map_smul]; simp only [α,Complex.ofReal_mul]
lemma payE : pinAct w (GE i j k l v).val= (σ i* σ j*(σ k*(σ l* σ v))) • (GE (s.perm i) (s.perm j) (s.perm k) (s.perm l) (s.perm v)).val:=by
    change pinAct w (plain _ _)=_ • plain _ _; rw[plainT _ s w hw]; have he:= StressFlux.pairDeriv_turn (G:=su) s i j k l v; let α:ℝ:= signT s i* signT s j*(signT s k*(signT s l* signT s v)); have hP : Labels.rotated s.ortho _ = (↑α:ℂ) • (pairDeriv su (s.perm i) (s.perm j) (s.perm k) (s.perm l) (s.perm v)).val:= congr_arg Subtype.val he; rw [hP,map_smul]; simp only [α,Complex.ofReal_mul]
end Perla
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Perla.fullD
#print axioms YM.Massive.Tawny.Cast.Perla.payG
#print axioms YM.Massive.Tawny.Cast.Perla.mirrorD
