import YM.Tawny.Hone
import YM.Push.STRESS_FLUX.Jets
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Pane
namespace KeysP
variable (x:Label d)(h:Quiet x.val)(hd:d≤10)
local notation "Gc"=>su.Color
local notation "g"=>su.colorMat
variable (e:Gc)(he:‖e‖=1)
noncomputable def slot (i j:Pinor):Bundle→ₗ[ℂ] Mat:=
 { toFun:=fun B x y=> B (i,x) (j,y),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
variable (p q:Multi d)(u v:Axis)
local notation "μ"=> gravel a b p q
local notation "A"=> Labels.Taylor su 0
local notation "Ψ"=> glow x h hd
local notation "hL"=> StressFlux.leg0 (G:=su) u v
open scoped Kronecker InnerProductSpace
include h hd he
lemma rayP : ∃ c:Spike,∀ k:su.Color, μ (Ψ (hL k)) = c ⊗ₖ g k:=by
    have hp(i j:Pinor): let L:= ((slot i j).restrictScalars ℝ) ∘ₗ ((μ).restrictScalars ℝ) ∘ₗ Ψ ∘ₗ hL; ∃ z:ℂ,∀ k:su.Color,L k=z • g k:=by
        intro L
        refine HintR.prismC L (fun t k=>?_) e he; ext c f; have ht:= ray_color a b p q x h hd t (hL k); rw [StressFlux.paint_leg0] at ht; have he:=congr_fun (congr_fun ht (i,c)) (j,f); change ((slot i j) (μ (Ψ (hL _))) * _ ) c f= ( _ * (slot i j) (μ (Ψ (hL _)))) c f
        simpa [Matrix.mul_apply, Fintype.sum_prod_type, touch, slot, Matrix.one_apply,ite_mul,mul_ite] using he
    choose Z hZ using hp; refine ⟨Matrix.of Z,fun k=>?_⟩; ext ⟨i,c⟩ ⟨j,f⟩; exact congr_fun (congr_fun (hZ i j k) c) f
omit h hd he
lemma braidR (M N: Spike)(X:Mat)(h:X≠0)(he:M ⊗ₖ X= N ⊗ₖ X):M=N:=by
    obtain ⟨i,j,hx⟩:∃ i j:Hue,X i j≠0:=by contrapose! h; ext i j; exact h i j
    ext s t; apply mul_right_cancel₀ hx; exact congr_fun (congr_fun he (s,i)) (t,j)
include he
lemma gem : g e≠0:=by intro hz; have hp: e=0:=su.colorMat_injective (hz.trans (map_zero _).symm); rw [hp,norm_zero] at he; norm_num at he
omit he
lemma ruby_pick : ∃ e:su.Color,‖e‖=1:=by haveI:= Gauge.Simple.nontrivial_color QCD.simple; obtain ⟨y,h⟩:=exists_ne (0:su.Color); refine ⟨‖y‖⁻¹ • y,?_⟩; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
lemma mix_blank (M N:Spike)(h:wave M=wave N): M=N:=by nth_rw 1[← Stew.leafy M,← Stew.leafy N]; rw[h]
include h hd
noncomputable def twin : Spike:=(rayP a b x h hd ruby_pick.choose ruby_pick.choose_spec p q u v).choose
local notation "c"=> twin a b x h hd p q u v
lemma pare (k:Gc): μ (ray (hL k) x.val)= c ⊗ₖ g k:=by rw [glean x h hd]; exact (rayP a b x h hd ruby_pick.choose ruby_pick.choose_spec p q u v).choose_spec k
end KeysP
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.KeysP.pare
