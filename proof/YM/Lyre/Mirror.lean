import YM.Lyre.Knit
import YM.Next.MAXWELL.Covariance
/-! # reflected Wick-data projections with active FULL taps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free.Lyre
open Function Filter MeasureTheory Lattice Wilson QCD QCD.Lat TensorProduct QCD.Grass Analysis YM.Arise.Range YM.Arise.Count Matrix Finset
open scoped Topology BigOperators ContDiff TensorProduct Matrix Matrix.Norms.L2Operator Kronecker Classical
variable {d e n m:ℕ}(a:Axis) (x:E4)
noncomputable def mot (a:Axis):GPol→ₛₗ[starRingEnd ℂ] GPol:= (Labels.rotated (Signed.reflect a)).toLinearMap.comp conjGPol
variable (p: Fin n→E4)(hp:Injective p)
local notation "G"=> Maxwell.Wick.moment su
local notation "Q" => crossV a x p
local notation "Rv"=> (Fin.rev : Fin n→Fin n)
local notation "Tv"=> (Fin.revPerm : Equiv.Perm (Fin n)) -- name
open Maxwell.Free
lemma gauge_rev (S:Equiv.Perm (Fin n))(f:Fin n→ Maxwell.WickPol su)(hp:Injective p): G (points (p ∘ S)) (f ∘ S)=G (points p) f:=by
    let L:=(G (points (p ∘ S))).domDomCongr S
    have h: points (p ∘ S)∈ conf n:= hp.comp S.injective
    have hs: L=G (points p):=by
       apply Module.Basis.ext_multilinear (fun _=>Maxwell.Wick.monBasis su) -- name
       intro v
       obtain ⟨l,hL⟩:=power_bag v
       rw [← hL]; change G _ ( (bag Prod.fst Prod.snd _) ∘ S)= _
       let w(i:Fin n×Factor su):= S.symm i.1
       have he(l:List (Fin n×Factor su)):bag Prod.fst Prod.snd l ∘ S=bag w Prod.snd l:=by
           funext x; induction l with|nil=>rfl|cons i l ih=> simp only [Function.comp_apply,bag_cons] at ih ⊢; rw [ih]; simp [w, Equiv.eq_symm_apply]
       rw [he,bag_rec w Prod.snd l h,bag_rec Prod.fst Prod.snd l (show points p∈conf n from hp)]; simp [w,Function.comp_def]
    exact DFunLike.congr_fun hs f
noncomputable def posV(a:Axis)(p: E4)(X:Points n) := Points.across p (Points.move (Signed.reflect a) X)
lemma pos_at (i:Fin n) : Q i= posV a x (points p) i:=by simp [posV,crossV,add_comm]
lemma pos_list:points Q= posV a x (points p):=PiLp.ext fun i=>pos_at ..
lemma illuminated (hp:Injective p):Injective Q:=fun i j he=> hp ((Ortho.motion _).injective (add_left_cancel he))
lemma changedL(y:GPol): Maxwell.reduceEq (mot a y) = mirrorBar (Signed.reflect a) (Maxwell.reduceEq y):=by
    let P:= Signed.reflect a; apply Maxwell.equalPol; intro V
    rw [Maxwell.jet_value]; change Labels.read _ (Labels.rotated P (conjGPol y))= Maxwell.probe _ (reflectPol _ (realForm _)); rw [reflects_eval,real_eval, Maxwell.jet_value]; unfold Labels.rotated; rw [Labels.eval_changed,UV.conj_values]; congr 2; apply congr_arg; funext i; exact gauge_orient P⁻¹ (V i) -- lookup
lemma gaugeP (hp:Injective p)(U:Fin n→UV.GPol)(W:Equiv.Perm (Fin n)) :
    G (points (Q ∘ W)) (fun i=> Maxwell.reduceEq (mot a (U (W i))))=star (G (points p) (fun i=>Maxwell.reduceEq (U i))):=by
    simp_rw [changedL]; let Z:= (fun i=> Maxwell.reduceEq (U i)); let f:= mirrorBar (Signed.reflect a) ∘ Z; change G _ (f ∘ W)= _; rw [gauge_rev _ W _ (illuminated a x p hp), pos_list, posV,moment_across, show G _ f= G _ (fun i=>realForm (Z i)) from moment_rotation (points p) (show points p∈conf n from hp) (fun i=>realForm (Z i)) (Signed.reflect a)]; exact moment_real _ (show points p∈conf n from hp) _
lemma reversesV {A :Type*} (x : Fin n→ A): List.ofFn (x ∘ Rv)=(List.ofFn x).reverse:=by
    apply List.ext_getElem; · simp
    intro i hi hi'; simp only [List.getElem_ofFn,List.getElem_reverse,List.length_ofFn,List.getElem_ofFn]; unfold Function.comp; apply congr_arg; apply Fin.ext; rw [Fin.rev]; dsimp only; have h:i<n:= (by simpa using hi)
    omega
variable {U:Type}[Fintype U](w: Fin n→ℕ)
lemma spinV (X:(i: Fin n)→ SpinPol (w i)) : erg (Fin n) (U:=U) Q w (List.ofFn (fun i=> ham (Fin n) (Rv i) w (aSpin _ a (X (Rv i))))).prod= dagger (erg (Fin n) p w (List.ofFn fun i=> ham (Fin n) i w (X i)).prod):=by
    let z(i : Fin n) := ham (Fin n) i w (X i); let g:= DawnH a w; let J:=fun i=>changeVars g (dagger (z i))
    have h(l:List (Fin n)) : (l.reverse.map J).prod=changeVars g (dagger (l.map z).prod):=by
         induction l with| nil=> simp [dagger_one]|cons a l ih=> rw [List.reverse_cons,List.map_append,List.prod_append,ih]; simp only [List.map_cons,List.prod_cons,List.map_nil, List.prod_nil,mul_one, dagger_mul,map_mul]; rfl
    simp_rw [hamR]; change erg _ _ w (List.ofFn (J ∘Rv)).prod = _; rw [reversesV, ← show List.map J (List.finRange n)=List.ofFn J from (by rw [List.finRange,List.map_ofFn]; rfl), ← List.map_reverse,h,downL]; simp only [List.finRange,List.map_ofFn]; rfl
lemma paired (hp:Injective p)(P:Fin n→GPol)(W:(i:Fin n)→SpinPol (w i)) : UV.Free.moment (w ∘ Rv) (points (Q ∘ Rv)) (fun i=> UV.adj a (P (Rv i)⊗ₜ[ℂ] W (Rv i))) = star (UV.Free.moment w (points p) (fun i=>P i⊗ₜ[ℂ] W i)) :=by
     let X : Fin n → E4:= crossV a x p
     let Y i:=mot a (P (Rv i)); let M(i:Fin n):= aSpin _ a (W (Rv i));
     let Z:=fun i=> Y i⊗ₜ[ℂ]M i; let b:= UV.Free.moment (w ∘ Rv) (points (X ∘ Rv)) Z; let c:= UV.Free.moment w (points p) (fun i=>P i⊗ₜ[ℂ] W i)
     erw [show (fun i: Fin n=> UV.adj a (P (Rv i)⊗ₜ[ℂ] W (Rv i)))=Z from funext fun i=> TensorProduct.map_tmul ..]; change b=star c
     have hv:=gammaCost (U:=Unit) (Fin n) Rv w X (show points (X ∘ Rv)∈conf n from (illuminated a x p hp).comp Fin.rev_injective) Y M
     let G₁:=G (points p) (fun i=> Maxwell.reduceEq (P i)); let G₂:= Arise.Count.erg (U:=Unit) (Fin n) p w (List.ofFn fun i=> ham _ i w (W i)).prod
     have he:G₁ • G₂ = c • 1:=gammaCost (U:=Unit) (Fin n) id w p hp P W
     have hZ:b • (1:Alg Unit)= star c • 1:=by
        let Q₁:= G (points (X ∘ Rv)) (fun i=> Maxwell.reduceEq (Y i)); let Q₂:= Arise.Count.erg (U:=Unit) (Fin n) X w (List.ofFn fun i: Fin n=> ham (Fin n) (Rv i) w (M i)).prod
        have hx:Q₁ • Q₂=b • 1:=hv; rw [← hx, show Q₁=star G₁ from gaugeP a x p hp P (Fin.revPerm), show Q₂=dagger G₂ from spinV a x p w W]; change starRingEnd ℂ _ • dagger _=_; rw [← map_smulₛₗ, he,map_smulₛₗ, dagger_one]; rfl
     exact smul_left_injective ℂ (one_ne_zero (α:=Alg Unit)) hZ
end YM.Massive.UV.Free.Lyre
#print axioms YM.Massive.UV.Free.Lyre.spinV
#print axioms YM.Massive.UV.Free.Lyre.gaugeP

#print axioms YM.Massive.UV.Free.Lyre.paired
