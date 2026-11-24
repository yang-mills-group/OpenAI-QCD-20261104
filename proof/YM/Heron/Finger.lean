import YM.Heron.Boggle
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Finset LinearMap
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(h:EuPin.Path Δ Γ)(χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)
local notation "F"=> Pol d
local notation "R"=> Axis×Axis→ Label 8
local notation "H"=> fromCenter Δ.val (x 0)
variable (v w:Pol d)(i j:Axis × Axis→Label 8)
noncomputable def wedge(v w:Pol d)(σ:Label 8)(x:Points 2)(y:E4):ℂ:= triangle y x σ.val (![v,w])
lemma bMap(z:Label 8)(y:E4) : ∃ L: Pol d →ₗ[ℂ] Pol d→ₗ[ℂ] ℂ,∀ v w: F,trioL y x (![v,w]) z.val=L v w:=by
     let Q:= UV.Free.moment (hill d) (Points.cons y x); let g: MultilinearMap ℂ (fun _:Fin 2=> Pol d) ℂ:= Q.curryLeft z.val
     let J(v:F):= (![v,0]); let X(v:F):=g.toLinearMap (J v) 1; have hv(v w:F): X v w= g (![v,w]):=by
         change g _=g _; apply congr_arg; funext i; fin_cases i<;> simp [X,J,MultilinearMap.toLinearMap_apply]
     let W(w:F):=g.toLinearMap (![0,w]) 0; have H'(v w:F):X v w=W w v:=by rw[hv]; change g _=g _; apply congr_arg; funext i; fin_cases i<;> simp [W,MultilinearMap.toLinearMap_apply]
     let B: Pol d →ₗ[ℂ] Pol d →ₗ[ℂ] ℂ:= {toFun:=X,map_add':=fun v w=>by apply LinearMap.ext; intro t; change X (v+w) t=X v t+X w t; rw[H',H',H',_root_.map_add], map_smul':=fun c v=>by apply LinearMap.ext; intro t; change X (c • v) t=c • X v t; rw [H',H', _root_.map_smul] }
     refine ⟨B, fun v w=>?_⟩; change _=X v w; rw[hv]; change Q (update (Fin.cons (α:=fun i:Fin 3=>Pol (hill d i)) 0 (![v,w])) 0 z.val)= Q (Fin.cons (α:=fun i:Fin 3=>Pol (hill d i)) z.val (![v,w])); exact congr_arg (fun f:(i:Fin 3)→ Pol (hill d i)=> Q f) (Fin.update_cons_zero ..)
include hx hχ
lemma wearθ : Realm χ (actS x Δ (![v,w]) i):=by
    intro a; apply Maxwell.Free.shell_cost hχ.1 hχ.2.1; intro y hy
    let u:Fin 3→ℕ:= hill d; have ht:= torchD x hx y χ hχ hy; have hg: Continuous (fun y:E4=>Points.cons y x):=by unfold Points.cons points; fun_prop
    have H'(i:Label 8): ContinuousAt (fun y:E4=> trioL y x (![v,w]) i.val) y:=by
         unfold trioL; let f:= update (Fin.cons (α:=fun i:Fin 3=>Pol (hill d i)) (0:Pol 8) (![v,w])) 0 i.val; change ContinuousAt (fun y=>UV.Free.moment u (Points.cons y x) f) y; exact (UV.Free.Sip.smoothC ht u f).continuousAt.comp (x:=y) (f:=fun y=>Points.cons y x) hg.continuousAt
    unfold actS; exact tendsto_finsetSum _ fun i' _=> (((helm Δ (x 0)).smooth i').continuous.continuousAt (x:=y)).smul (H' (i (a,i')))
end YM.Heron
#print axioms YM.Heron.bMap
#print axioms YM.Heron.wearθ
