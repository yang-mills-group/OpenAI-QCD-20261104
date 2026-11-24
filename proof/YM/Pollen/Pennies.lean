import YM.Pollen.Bean
import YM.Further.DENSE_MIXED_KERNELS.Pitch
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek Loom Finset NormedSpace
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola Further.DenseMixedKernels
variable {C t A D B M:ℝ}{I:Type}[Fintype I]
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "q"=> traceI I
local notation "τ"=> Stitch.Tablet.credits
variable (t)
structure Phy (v:Grid c→Patio (Keys c N ⊕ Spine I)) (U:Grid c)(D:Directions su c → Prop) (n:ℕ) (x a:ℝ) : Prop where
   smooth : Push.Local.Chart n v U
   paid : ∀ l:List _,l.length ≤ n → (∀ i∈l,D i)→Stitch.Tablet.credits t (leftDerivs v l U)≤ x * a^l.length
variable {t} {u v:Grid c→Patio (Keys c N ⊕ Spine I)}{U:Grid c}{Q: Directions su c → Prop}
namespace Phy
-- Use token norm.Eq evenA measure.
variable (h: Phy t v U Q n B A)(ht:0<t)
lemma costX (x y:P): τ t (x+y) ≤ τ t x+τ t y:=by unfold Stitch.Tablet.credits; rw [map_add]; unfold load wscale; rw [map_add]; exact norm_add_le ..
lemma spiceX (a:ℂ)(x:P): τ t (a • x)=‖a‖*τ t x:=by unfold Stitch.Tablet.credits; rw [map_smul,load_scale]
include h
local notation "O"=> (fun (_:I)=> (0:Site c))
set_option maxHeartbeats 760000 in
lemma prod {p:Grid c→ℂ}(hf:Pitch p U Q n C D): Phy t (fun i=> p i • v i) U Q n (C*B) (D+A):=by
     let f0:(Keys c N ⊕ Spine I)→ ℝ:=Stitch.Tablet.chip t _ _; let F':= ((changeVars (Matrix.diagonal fun a=> (f0 a:ℂ))).comp (light _)).toLinearMap.toContinuousLinearMap; have hy (x:P):‖F' x‖=τ t x:= (show Norm.norm (changeVars (Matrix.diagonal (fun a=>(f0 a:ℂ))) (light _ x))=Stitch.Tablet.credits t x from (by unfold Stitch.Tablet.credits QCD.Creek.load wscale f0; congr!)); let Z:= fun i=> F' (v i); have hZ: Pitch Z U Q n B A:=by
           refine ⟨(F'.restrictScalars ℝ).contDiff.contDiffAt.comp _ h.smooth,fun l hl hA=> ?_⟩
           unfold Z; rw [show leftDerivs (fun i=> F' (v i)) l U=F' _ from clm_left (F'.restrictScalars ℝ) h.smooth l hl]; exact (hy _).trans_le (h.paid l hl hA)
     let x:= fun i=> p i • v i; have hp: Rests x n U:=ContDiffAt.smul hf.smooth h.smooth
     refine ⟨hp,fun l hl he=>?_⟩
     have hw: Pitch (fun i=> F' (x i)) U Q n (C*B) (D+A):=by
               simp only [x, map_smul]; have hh:= Pitch.bilinear (ContinuousLinearMap.lsmul (E:=_) ℝ _) hf hZ (C:=1) (by intro x y; simp [norm_smul]) zero_le_one; simpa [Z] using hh
     have hk:= hw.bounds l hl he; rw [show leftDerivs (fun i=> F' (x i)) l U= F' _ from clm_left (F'.restrictScalars ℝ) hp l hl] at hk; exact (hy _).symm.trans_le hk
lemma linear (f:P→L[ℂ]P) (hb:∀ x:P,τ t (f x)≤ C*τ t x)(hc:0 ≤ C): Phy t (f ∘ v) U Q n (C*B) A:=by
    refine ⟨(f.restrictScalars ℝ).contDiff.contDiffAt.comp _ h.smooth,fun l hl he=>?_⟩; rw [show leftDerivs (f ∘ v) l U= f _ from Push.Local.left_linear (f.restrictScalars ℝ) l h.smooth hl]; exact (hb _).trans ((mul_le_mul_of_nonneg_left (h.paid _ hl he) hc).trans_eq (mul_assoc ..|>.symm)) -- inspect
lemma nn : 0 ≤ B:=by have hh:= h.paid [] (Nat.zero_le n) (by simp); rw[List.length_nil,pow_zero,mul_one] at hh; exact (load_nn ..).trans hh
lemma more (hv:B ≤ M)(h0:0 ≤ A)(hp:A ≤ C): Phy t v U Q n M C:= ⟨h.smooth,fun l hv' he=> (h.paid l hv' he).trans (mul_le_mul hv (pow_le_pow_left₀ h0 hp _) (pow_nonneg h0 _) (h.nn.trans hv))⟩
lemma plus (hp: Phy t u U Q n C A): Phy t (v+u) U Q n (B+C) A:=by
    refine ⟨ContDiffAt.add h.smooth hp.smooth,fun l hl hv=>?_⟩; change τ _ (leftDerivs (fun i=> v i+u i) l U)≤_; rw [plus_left h.smooth hp.smooth l hl,add_mul]; exact (costX ..).trans (add_le_add (h.paid _ hl hv) (hp.paid _ hl hv)) -- t implicit might implicit not rec
omit h
lemma fixedX (x:P){A:ℝ}(hA:0≤ A): Phy t (fun _=> x) U Q n (τ t x) A:=by
   refine ⟨contDiffAt_const,fun l hl he=>?_⟩
   rw [Work.G07.left_const]; split; next h=> rw [h,List.length_nil,pow_zero,mul_one]
   unfold Stitch.Tablet.credits; rw [map_zero, QCD.Cove.load_zero]; exact mul_nonneg (load_nn ..) (pow_nonneg hA _)
lemma ton {Y:Type} [Fintype Y] (r:Finset Y)(f:Y→ Grid c→ P)(b:Y→ℝ) (hA:0 ≤A)(hp:∀ i∈r,Phy t (f i) U Q n (b i) A) : Phy t (∑ i∈r,f i) U Q n (∑ i∈r,b i) A:=by
    induction r using Finset.induction_on with
    | empty=> simpa only [sum_empty, Stitch.Tablet.credits,map_zero,QCD.Cove.load_zero] using! (fixedX (U:=U) (n:=n) (t:=t) (Q:=Q) (0:P) hA)
    | insert i r hi ih=> rw [sum_insert hi,sum_insert hi]; exact (hp _ (mem_insert_self ..)).plus (ih fun i hi=>hp _ (mem_insert_of_mem hi))
end Phy
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Phy.prod
#print axioms YM.Massive.PCAC.Phy.ton
