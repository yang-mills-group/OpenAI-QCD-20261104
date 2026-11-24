import YM.Lyre.Mirror
/-! Matrix/W.Pol universal rows -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free.Lyre
open Function Filter MeasureTheory Lattice Wilson QCD QCD.Lat TensorProduct QCD.Grass Analysis YM.Arise.Range YM.Arise.Count Matrix Finset
open scoped Topology BigOperators ContDiff TensorProduct Matrix Matrix.Norms.L2Operator Kronecker Classical
variable {d e n m:ℕ}(a:Axis)(x:E4)
variable (p:Fin n→ E4)(w:Fin n→ℕ)
local notation "Q"=> crossV a x p
local notation "Rv"=> (Fin.rev : Fin n→Fin n)
open MultilinearMap
variable (P:(i:Fin n)→ UV.Pol (w i)) (hp:Injective p)
include hp
lemma panel : moment (w ∘ Rv) (points (Q ∘ Rv)) (fun i=> UV.adj a (P (Rv i))) = star (moment w (points p) P) :=by
    let V := fun i => UV.Pol (w i)
    let Z: Equiv.Perm (Fin n):= Fin.revPerm; let Z₂:=Q ∘Z
    let L: MultilinearMap ℂ (fun i=>V (Z.symm i)) ℂ:= moment (w ∘ Rv) (points (Q ∘ Rv)); let H:MultilinearMap ℂ V ℂ:= (MultilinearMap.domDomCongrLinearEquiv' (R:=ℂ) (S:=ℂ) (M₁:=V) ℂ Z).symm L
    let g(U:(i:Fin n)→V i)(i):= UV.adj a (U i)
    have Hz(U:(i:Fin n)→V i):H (g U)=moment (w ∘ Rv) (points (Q ∘ Rv)) (fun i=> UV.adj a (U (Rv i))):=rfl -- transport Equiv
    have hx [DecidableEq (Fin n)] (i:Fin n)(U:(i:Fin n)→V i) (v:V i): g (update U i v)= update (g U) i (UV.adj a v):=by
       funext j; by_cases h:j=i
       · subst j; simp [g]
       simp [g,h]
    let D: MultilinearMap ℂ V ℂ:= {
       toFun:= fun v=> star (H (g v))
       map_update_add':= fun v i a b=>by rw [hx,hx,hx,map_add,H.map_update_add,star_add]
       map_update_smul':= fun v i a b=>by rw [hx,hx,map_smulₛₗ,H.map_update_smul]; simp }
    have hu:D=moment w (points p):=by
         refine Module.Basis.ext_multilinear (fun i=>basisU (w i)) ?_
         intro k; let K i:= basisU (w i) (k i); change star (H (g K)) = _; rw [Hz]
         let U i:= (MvPolynomial.basisMonomials (Labels.Key su) ℂ) (k i).1; let W(i):=(Grass.blades (Pairs (SpinMode (w i)))) (k i).2; change _=moment w _ K
         rw [show K=(fun i=> U i ⊗ₜ[ℂ] W i) from funext fun i=> Module.Basis.tensorProduct_apply' ..]; erw [paired a x p w hp U W]; rw [star_star]
    rw [← Hz]; apply star_injective; rw [star_star]; exact DFunLike.congr_fun hu P
end YM.Massive.UV.Free.Lyre
#print axioms YM.Massive.UV.Free.Lyre.panel
