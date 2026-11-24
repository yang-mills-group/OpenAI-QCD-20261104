import YM.Heron.Stull
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad)
open Finset
variable {d:ℕ} (s:Ortho.Skew)(Γ:ℝ→EuPin)(hΓ: EuPin.Path s Γ)(x:ℝ) (p q:Multi d)(z:E4)(W:Spins)(t:Bool)(a:Axis)
local notation "ω"=> formT t
local notation "R"=> fromCenter s.val z
local notation "T"=> twistS ω R W
local notation "D"=> deriveL
private lemma acts0 : ∀ A:EuPin,changeP A (walk (0:Multi d))=walk (0:Multi d):=by intro A; rw[walking]; simp [show ∀ i:Axis,power (0:Multi d) i=0 from fun _=>rfl]
lemma snaps : steps (0:Multi d)=[]:=by unfold steps; simp [show ∀ i:Axis,power (0:Multi d) i=0 from fun _=>rfl]
include hΓ
lemma theta0 : tent z t p W (Γ 0)= deriveL (steps p) W z:=by unfold tent; rw[uno _ _ hΓ, hΓ.1,spin_coord_id]; exact burst ..
lemma spirit_b : HasDerivAt (fun x=>tent z t (0:Multi d) W (Γ x)) (deriveL (steps (0:Multi d)) (twistS ω R W) z) 0:=by
     simp only[tent,acts0, burst, snaps]; change HasDerivAt (fun x=> turnG _ t (W z)) (twistS _ _ W z) 0; rw [goes, show (∑ i:Axis, (fromCenter s.val z i z) • grad i W z)=0 from ?_,zero_add]; · exact actO s Γ hΓ t _
     simp [fromCenter,M4.at_coord]
variable {U:Set E4}(hU:IsOpen U)(hz:z∈U)(hw:∀ y∈U, ContDiffAt ℝ ∞ W y)
include hU hz hw
lemma tide (h:AtNext a p q):tent z t q W (Γ x) = ∑ i:Axis, ((Γ x).coord.val i a:ℝ) • tent z t p (grad i W) (Γ x):=by
     unfold tent; rw[breeze (Γ x) p q z W a hU hz hw h,map_sum]; apply sum_congr rfl; intro i _; rw [_root_.map_smul,collect,map_sum]; simp only[_root_.map_smul,_root_.map_sum,burst]; rfl
omit hΓ
private lemma spring (L:List Axis) (i:Axis) : D L (grad i (twistS (formT t) (fromCenter s.val z) W)) z= D L (twistS (formT t) (fromCenter s.val z) (grad i W)) z+ ∑ j:Axis, s.val j i • D L (grad j W) z:=by
    let Q:= fromCenter s.val z; let A:=formT t; let F:=twistS A Q W; let S:=twistS A Q (grad i W); let α(j:Axis):ℝ:= s.val j i
    have hh(i):∀ x∈U, ContDiffAt ℝ ∞ (grad i W) x:= fun x hx=> Maxwell.grad_smooth i (hw x hx) (by simp)
    have hp:∀ x∈U,ContDiffAt ℝ ∞ S x:= fun x hx=>life s A (grad i W) x z (hh i x hx)
    have hf(L:List Axis)(x:E4)(hx:x∈U): D L (grad i F) x= D L S x+∑ j:Axis, α j • D L (grad j W) x:=by
         induction L generalizing x with
         | nil=> exact shifts s A i W x z (hw x hx)
         | cons a L ih=>
               have ht := (balla L S U hU hp x hx).differentiableAt (by simp); have hy(j:Axis):= (balla L (grad j W) U hU (hh j) x hx).differentiableAt (by simp); have hQ(j): DifferentiableAt ℝ (fun x=> α j • D L (grad j W) x) x:= (hy j).const_smul (α j); rw [show deriveL (a::L) (grad i F) x= Analysis.D (basis a) (fun y=>deriveL L S y + ∑ j:Axis,α j • deriveL L (grad j W) y) x from GermD _ ((show ∀ᶠ y in 𝓝 x,y∈U from hU.mem_nhds hx).mono ih), Analysis.D, fderiv_fun_add ht (DifferentiableAt.fun_sum fun j _=>hQ j), fderiv_fun_sum (fun j _=>hQ j)]; simp_rw [fderiv_fun_const_smul (hy _)]; simp only [ContinuousLinearMap.add_apply,_root_.sum_apply]; rfl
    exact hf L z hz
include hΓ
lemma revival : HasDerivAt (fun x=> tent z t p W (Γ x)) (deriveL (steps p) T z) 0 :=by
   induction h:UV.order (power p) using Nat.strong_induction_on generalizing p W with
   | h k ih=>
       subst k; by_cases he:p=0; subst p; exact spirit_b _ _ hΓ .. 
       obtain ⟨a,q,hq⟩:= prey p he; let X:=fromCenter s.val z; let F:= twistS ω X W
       have ht: UV.order (power q)<UV.order (power p):=by rw [Arise.omegaLen hq]; omega
       have hY(i):∀ x∈ U,ContDiffAt ℝ ∞ (grad i W) x:=fun x hx=>Maxwell.grad_smooth _ (hw x hx) (by simp)
       let B(i:Axis):= deriveL (steps q) (twistS ω X (grad i W)) z; let D'(i):=tent z t q (grad i W) (Γ 0); let M(i:Axis):=(Γ 0).coord.val i a
       have hx(i:Axis) : HasDerivAt (fun x:ℝ=> (Γ x).coord.val i a • tent z t q (grad i W) (Γ x)) (M i • B i+s.val i a • D' i) 0:=by
              have y : HasDerivAt (fun x=> tent z t q (grad i W) (Γ x)) (B i) 0 := by apply ih (UV.order (power q)) ht q (grad i W) (hY i) rfl
              exact (cSpan s Γ hΓ i a).smul y
       simp_rw [fun x=>tide s Γ hΓ x q p z W t a hU hz hw hq]; apply HasDerivAt.congr_deriv (HasDerivAt.fun_sum fun i _=>hx i); unfold D'; rw [sum_add_distrib, show (∑ i:Axis, M i • B i)=B a from (?_), stock q p z _ a hU hz (?_) hq, spring s z W t hU hz hw]; simp only [theta0 _ _ hΓ]; rfl
       · exact fun y hy=>life _ _ _ _ _ (hw y hy)
       unfold M; rw[hΓ.1]; simp [show (1:EuPin).coord.val=1 from rfl,Matrix.one_apply,ite_smul]
end YM.Heron
#print axioms YM.Heron.tide
#print axioms YM.Heron.revival
