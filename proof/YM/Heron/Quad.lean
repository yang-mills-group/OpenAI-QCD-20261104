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
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(p q:GPol)(u:Flavor 6)(R:List (letters d))(S:Dot d)(L:List (Dot d))(α:letters d)
local notation "P"=> Hail.tagD R
local notation "D"=> east d
local notation "Ω"=> chime (oakT d) x
noncomputable def fuel (x:Points 2)(L:List (Dot d)): SpinPol d →ₗ[ℂ] ℂ:= (lease (chime (oakT d) x)) ∘ₗ LinearMap.mulRight ℂ (pwn (L.map (east d))) ∘ₗ (twig (oakT d) 0).toLinearMap
lemma forbs : fuel x L (atom α) = slips L fun s u=> dawd x s (atom α) * fiesta x u :=by
     unfold fuel; change lease Ω (twig (oakT d) _ (atom α)*_)=_; rw [tuck, slipH,slips_map]; unfold slips; simp only[mask,smul_eq_mul]; rfl
noncomputable def sunSlip (x:Points 2)(L:List (Dot d)) :SpinPol d→ₗ[ℂ] ℂ :=
   let f(i:Dot d)(r:List (Dot d)):= fiesta x r • dawd x i; slips L f
lemma B_sun (w:SpinPol d):sunSlip x L w = slips L (fun s u=> dawd x s w * fiesta x u):=by
    unfold sunSlip slips; simp only [LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul]; apply sum_congr rfl; intro i _; rw [mul_comm (fiesta ..)]
lemma awash : fuel x L (atom α) = sunSlip x L (atom α):=by rw [forbs,B_sun]
variable (A:Ortho.Skew)(Γ:ℝ→EuPin)(h:EuPin.Path A Γ)
include h
lemma berry : fuel x L (sonic u Γ α)= slips L (fun s w=>dawd x s (sonic u Γ α) * fiesta x w):=by
     let F:= fun t=>spiritX u Γ t d (atom α); let X:SpinPol d →L[ℝ]ℂ:=(fuel x L).toContinuousLinearMap.restrictScalars ℝ; let K:SpinPol d →L[ℝ]ℂ:=(sunSlip x L).toContinuousLinearMap.restrictScalars ℝ; have hv:= suitable A Γ h u α
     rw [← B_sun]; apply (X.hasFDerivAt.comp_hasDerivAt (0:ℝ) hv).unique; apply (K.hasFDerivAt.comp_hasDerivAt (0:ℝ) hv).congr_of_eventuallyEq; obtain ⟨t,p,i,a,u',hX⟩:= voicing α; refine Eventually.of_forall fun z=>?_ ; subst α; change fuel x L (spun _ _ _) = sunSlip x L (spun _ _ _); change fuel x L (spun _ _ (atom (code t p i a u')))=sunSlip x L (spun _ _ (atom (code t p i a u'))); rw [rolls]; simp only [map_sum,map_smul,awash]
omit h
noncomputable def tally (x:Points 2)(v:Pol d) : Pol d →ₗ[ℂ] ℂ:= (moment (oakT d) x).toLinearMap (![0,v]) (0:Fin 2)
lemma t_eye (v w:Pol d): tally x v w= ear x w v:=by change moment (oakT d) x (update _ (0:Fin 2) _ ) = moment (oakT d) x _; apply congr_arg; funext i; fin_cases i<;>simp
variable (y:E4)(hy:Points.cons y x∈conf 3)(v:List (letters d))
local notation "V"=> Hail.tagD v
local notation "W"=> ester x p q
include hy hx
set_option maxHeartbeats 500000 in
lemma evo (w: SpinPol d): tally x (q⊗ₜ[ℂ] V) (p ⊗ₜ[ℂ] (w*P)) = W* fuel x (tot R v) w:=by
     let G:Fin 2→GPol:=![p,q]; let T:= ![w*P,V]; have hs:ear x (p⊗ₜ[ℂ](w*P)) (q⊗ₜ[ℂ] V)= moment (oakT d) x (fun i=>G i⊗ₜ[ℂ]T i):=by unfold ear; apply congr_arg; funext i; fin_cases i<;>rfl
     rw [t_eye,hs]; rw [stroll x hx G T]; refine congr_arg₂ (·*·) ?_ ?_; · change _= Maxwell.Wick.moment su x _; apply congr_arg; funext i; fin_cases i<;>rfl
     rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_singleton]; let B(i:Fin 2):= twig (oakT d) i
     change lease Ω (B 0 (w*P)* B 1 V) = lease Ω ((B 0 w) * pwn ((tot R v).map (east d)))
     rw [show B 0 (w*P)=B 0 w* B 0 P from map_mul (B 0) _ _, mul_assoc,show B 0 P= _ from tonic x y hx hy R 0, show B 1 V= _ from tonic x y hx hy v (1:Fin 2)]
     congr 2; simp [tot,pwn]

include h
lemma spawnX :
    let w:List (Dot d):= tot R v
    HasDerivAt (fun t=> ear x (p⊗ₜ[ℂ] spiritX u Γ t d P) (q⊗ₜ[ℂ] V))
      (slips R (fun b r=>slips (tot r v) (fun j w' => charm x Γ u (0,b) j * (ester x p q*fiesta x w')))) 0 :=by
    intro w
    let F:=tally x (q⊗ₜ[ℂ] V); let L:SpinPol d→ₗ[ℂ]ℂ:= F ∘ₗ TensorProduct.mk ℂ _ _ p; simp_rw [show ∀ s:ℝ, ear x (p⊗ₜ[ℂ] spiritX u Γ s d P) (q⊗ₜ[ℂ]V)= L (spiritX u Γ s d P) from fun s=> (t_eye x _ _).symm |> fun h=>h] -- rw function? use simp
    apply HasDerivAt.congr_deriv ((L.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0:ℝ) (jolt A Γ h u R)); change L _ = _; rw[from_slip]; unfold slips; apply sum_congr rfl; intro i _; dsimp only; change _ • tally x (q⊗ₜ[ℂ]V) (p⊗ₜ[ℂ](sonic _ _ _ * Hail.tagD _))=_; rw [evo x hx p q (R.eraseIdx i.val) y hy, berry x u _ _ A Γ h]; unfold slips; rw[Finset.mul_sum]; apply congr_arg; apply sum_congr rfl; intro k _; dsimp only; unfold charm; rw [if_pos rfl]; simp only[smul_eq_mul]; ring
end YM.Heron
#print axioms YM.Heron.spawnX
