import YM.Heron.Beryl
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad away)
open Finset
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(u v e:Flavor 6)(y:E4) (Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(p q:Multi d)(i j:Pinor)(a b: Hue)(t t':Bool)
local notation "P"=> steps p
local notation "Q"=> steps q
local notation "x₀"=> x (0:Fin 2)
local notation "x₁"=> x (1:Fin 2)
local notation "κ"=> code t p i a u
local notation "Uk"=> piD (1:Fin 2) (!t) q j a u
local notation "K"=> pose (formT (!t)) (deck j) Q x₁
local notation "R"=> fromCenter Δ.val x₀
local notation "Y°"=> twistS (formT t) R K
include hΓ hx
lemma fineK : dawd x Uk (sonic u Γ κ)= -dotL (deck i) (deriveL P (twistS (formT t) (fromCenter Δ.val (x 0)) K) x₀):=by
    let W:= (dawd x Uk).toContinuousLinearMap.restrictScalars ℝ; have hh : Way (FlipT (formT (!t))) ({x₁}ᶜ) K:= care _ _ (actual (!t)) _ Q; have ht:= revival (U:=({x₁}ᶜ)) Δ Γ hΓ p (x 0) _ t isOpen_compl_singleton (show x₀≠ x₁ from (show Injective x.ofLp from hx).ne (by decide : (0:Fin 2)≠ 1)) (fun x hx=> hh.live x hx); apply (W.hasFDerivAt.comp_hasDerivAt (0:ℝ) (suitable Δ Γ hΓ u κ)).unique; refine ((dotL (deck i)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ht).neg |>.congr_of_eventuallyEq ?_; exact Eventually.of_forall fun t'=>F_line x hx u Γ Δ hΓ p q i j a t t'
omit hΓ
variable (χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)
include hχ
lemma lode : χ=ᶠ[𝓝 x₀] fun _=>1:= hχ.2.2.1
lemma cutView : x₁∉ tsupport χ:= hχ.2.2.2 (0:Fin 1)
lemma cult : tsupport χ ⊆ {x₁}ᶜ:=fun z hz h=> cutView x hx χ hχ ((show z=x₁ from h) ▸ hz)
lemma palmG (hy:y∈ tsupport (fderiv ℝ χ)): ∀ i:Fin 2, x i ≠ y:=by
   have hz(y:E4)(hy:y∈tsupport (fderiv ℝ χ)):y≠x 1:= cult x hx χ hχ (tsupport_fderiv_subset ℝ hy); intro i; fin_cases i; exact fun ht=> Maxwell.Free.collar (lode x hx χ hχ) (ht.symm ▸ hy); exact Ne.symm (hz y hy)
lemma torchD (hy:y∈ tsupport (fderiv ℝ χ)):Points.cons y x∈conf 3:=by
  have he(i):y≠x i:=Ne.symm (palmG x hx y χ hχ hy i)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j
    simp [Points.cons,he]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Points.cons,Ne.symm (he i)]
  simp only [Points.cons, points_apply, Fin.cons_succ]
  exact fun hi => congr_arg Fin.succ ((show Injective x.ofLp from hx) hi)

noncomputable def windD (x:Points 2)(Γ:Ortho.Skew)(u:Flavor 6)(i j: Dot d)(a:Axis)(y:E4):ℂ:= ∑ b:Axis, fromCenter Γ.val (x 0) b y • beeD u a b x y i j
local notation "T"=> windD x Δ
noncomputable def combD (x:Points 2)(Γ:Ortho.Skew)(u:Flavor 6)(i j:Dot d)(χ:E4→ℝ):ℂ:= Maxwell.Free.exportFlux (windD x Γ u i j) χ
local notation "E"=> combD x Δ
omit hx hχ
variable (m n:Fin 2)
set_option quotPrecheck false
local notation "cG" m:arg t:arg=> piD m t p i a u
local notation "sG" n:arg t:arg=>piD n t q j b v
lemma dark (h:¬ (t=false ∧ t'=true ∧ a=b∧ u=e∧ v=e)): windD x Δ e (cG m t) (sG n t') =0:=by unfold windD; simp_rw [fun k l y=> aus x y p q i j a b u v e m n t t' k l h,smul_zero,Finset.sum_const_zero]; rfl
lemma voidP (h:¬ (t=false∧ t'=true∧ a=b∧u=e∧v=e)): combD x Δ e (cG m t) (sG n t') χ=0:=by unfold combD; rw [dark x u v e Δ p q i j a b t t' m n h]; simp [Maxwell.Free.exportFlux]
local notation "X"=>pose gamma (deck i) P (x m)
local notation "S"=>pose (FlipT gamma) (deck j) Q (x n)
include hx hχ
lemma cruise(y:E4)(hy:y ∈ tsupport (fderiv ℝ χ))(k:Axis): windD x Δ u (piD m false p i a u) (piD n true q j a u) k y=brook gamma X S R k y :=by -- fix
     unfold windD brook; simp_rw [fun i'=>roads x y p q i j a u m n k i' (palmG x hx y χ hχ hy m) (palmG x hx y χ hχ hy n)]
lemma bible : combD x Δ u (piD m false p i a u) (piD n true q j a u) χ= Maxwell.Free.exportFlux (brook gamma X S R) χ :=by
     unfold combD Maxwell.Free.exportFlux; congr 1; apply sum_congr rfl; intro k _; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ ; dsimp only; by_cases he:y∈tsupport (grad k χ); · rw [cruise x hx u Δ p q i j a χ hχ m n y (Maxwell.Free.gradient_part χ k he)]
     rw [image_eq_zero_of_notMem_tsupport he,zero_smul,zero_smul]
end YM.Heron
#print axioms YM.Heron.fineK
#print axioms YM.Heron.bible
