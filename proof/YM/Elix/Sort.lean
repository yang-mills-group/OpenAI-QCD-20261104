import YM.MassiveMasses.OrderedWick
import YM.Maxwell.Reorder

set_option autoImplicit false
noncomputable section

namespace YM.MassiveMasses.FreePair
open Lattice QCD QCD.Lat QCD.Grass Massive Massive.UV TensorProduct
open scoped BigOperators TensorProduct
local notation "Letter" d => Pairs (SpinMode d)

/-- Both the basis evaluator and the exterior product choose this very same
ordering. Keeping the sign avoids assuming an order on the numerical indices. -/
private lemma orient {T : Type*} [Fintype T] [DecidableEq T] {p q : T} (h : p ≠ q) :
    (Free.atomList {p,q} = [p,q] ∧ atom p * atom q = mono {p,q}) ∨
    (Free.atomList {p,q} = [q,p] ∧ atom p * atom q = -mono {p,q}) := by
  let s : Finset T := {p,q}
  have expr := (Grass.expression s).choose_spec
  have hm : mono s = ((Free.atomList s).map atom).prod := by
    simpa only [Free.atomList,List.map_ofFn] using expr.2.2
  have mem (u : T) : u ∈ Free.atomList s ↔ u ∈ s := by
    simp only [Free.atomList,List.mem_ofFn]
    exact (expr.2.1 u).symm
  have hlen : (Free.atomList s).length = 2 := by simp [Free.atomList,s,h]
  obtain ⟨v,w,e⟩ := List.length_eq_two.mp hlen
  have h₁ := (mem p).mpr (show p ∈ s by simp [s])
  have h₂ := (mem q).mpr (show q ∈ s by simp [s])
  simp only [e,List.mem_cons,List.not_mem_nil,or_false] at h₁ h₂
  have orders : Free.atomList s = [p,q] ∨ Free.atomList s = [q,p] := by
    rcases h₁ with f|f <;> rcases h₂ with g|g
    · exact (h (f.trans g.symm)).elim
    · exact Or.inl (by simpa only [← f,← g] using e)
    · exact Or.inr (by simpa only [← g,← f] using e)
    · exact (h (f.trans g.symm)).elim
  rcases orders with ord|ord
  · exact Or.inl ⟨ord,by simpa [ord] using hm.symm⟩
  · refine Or.inr ⟨ord,?_⟩
    rw [atom_flip p q]
    congr 1
    simpa [ord] using hm.symm

private def bond (d : ℕ) (x : Points 2) : Pol d →ₗ[ℂ] Pol d →ₗ[ℂ] ℂ where
  toFun p := ((Free.moment (fun _ : Fin 2 => d) x).curryLeft p).toLinearMap (fun _ => 0) 0
  map_add' p q := by apply LinearMap.ext; intro z; simp
  map_smul' p q := by apply LinearMap.ext; intro z; simp

private lemma bondEval (d : ℕ) (x : Points 2) (p q : Pol d) :
    bond d x p q = Free.moment (fun _ : Fin 2 => d) x ![p,q] := by
  unfold bond
  simp only [LinearMap.coe_mk,AddHom.coe_mk,MultilinearMap.toLinearMap_apply,MultilinearMap.curryLeft_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

private def spinIn (d : ℕ) : SpinPol d →ₗ[ℂ] Pol d := TensorProduct.mk ℂ _ _ 1

private def listValue {d : ℕ} (x : Points 2) (l r : List (Letter d)) : ℂ :=
  let all := l.map (fun t => (⟨0,t⟩ : Free.Occ (fun _ : Fin 2 => d))) ++ r.map (fun t => ⟨1,t⟩)
  Free.pf (Free.pair x) all.length all

private lemma basisValue (d : ℕ) (x : Points 2) (s t : Finset (Letter d)) :
    bond d x (spinIn d (mono s)) (spinIn d (mono t)) =
      listValue x (Free.atomList s) (Free.atomList t) := by
  classical
  let power : Fin 2 → PowerPair d := ![(0,s),(0,t)]
  have basisSpin (U : Finset (Letter d)) : Free.basisU d (0,U) = spinIn d (mono U) := by
    change (MvPolynomial.basisMonomials (Labels.Key su) ℂ).tensorProduct (Grass.blades (Letter d)) (0,U) = _
    simp [Module.Basis.tensorProduct_apply,spinIn,mono]
  rw [bondEval]
  rw [show ![spinIn d (mono s),spinIn d (mono t)] = (fun i => Free.basisU d (power i)) by
    funext i; fin_cases i <;> simp [power,basisSpin]]
  rw [Free.moment,Multilabel.applyBasis]
  unfold Free.monomialValue
  have constants : (fun i => Maxwell.reduceEq (MvPolynomial.monomial (power i).1 1)) =
      (fun _ : Fin 2 => (1 : Maxwell.WickPol su)) := by
    funext i
    fin_cases i <;> simp [power]
  rw [constants,Maxwell.Wick.constants,one_mul]
  have order : (List.finRange 2) = [0,1] := rfl
  simp only [order,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

private lemma valFour (d : ℕ) (x : Points 2) (p q r s : Letter d) :
    listValue x [p,q] [r,s] =
      -Free.pair (u:=fun _=>d) x ⟨0,p⟩ ⟨1,r⟩ * Free.pair (u:=fun _=>d) x ⟨0,q⟩ ⟨1,s⟩ +
       Free.pair (u:=fun _=>d) x ⟨0,p⟩ ⟨1,s⟩ * Free.pair (u:=fun _=>d) x ⟨0,q⟩ ⟨1,r⟩ := by
  change Free.pf _ 4 [_,_,_,_] = _
  rw [fourLetters]
  have hzero : Free.pair (u:=fun _=>d) x ⟨0,p⟩ ⟨0,q⟩ = 0 := by simp [Free.pair]
  rw [hzero,zero_mul,zero_sub,neg_mul]

private lemma arbitraryOrder (d : ℕ) (x : Points 2) {p q r s : Letter d} (hp : p ≠ q) (hr : r ≠ s) :
    bond d x (spinIn d (atom p*atom q)) (spinIn d (atom r*atom s)) = listValue x [p,q] [r,s] := by
  classical
  rcases orient hp with ⟨ho,hprod⟩|⟨ho,hprod⟩ <;>
    rcases orient hr with ⟨ho',hprod'⟩|⟨ho',hprod'⟩ <;>
    rw [hprod,hprod'] <;>
    simp only [map_neg,LinearMap.neg_apply,neg_neg,basisValue,ho,ho',valFour] <;> ring

theorem arts (d : ℕ) (x : Points 2) {p q r s : Pairs (SpinMode d)} (hp:p≠q)(hq:r≠s) :
   Free.moment (fun _ : Fin 2=>d) x ![(1:UV.GPol) ⊗ₜ[ℂ] (atom p * atom q), (1:UV.GPol) ⊗ₜ[ℂ] (atom r*atom s)] =
     Free.pf (Free.pair x) 4 [(⟨0,p⟩:Free.Occ (fun _ : Fin 2=>d)), ⟨0,q⟩,⟨1,r⟩,⟨1,s⟩] :=by
    rw[← bondEval]; exact arbitraryOrder _ _ hp hq
set_option maxHeartbeats 850000 in
private lemma massLegs (d:ℕ) (x:Points 2) (a b:Fin 6) (i j k l:Fiber) :
    bond d x (spinIn d (bar ((0,i),a)*psi ((0,j),a))) (spinIn d (bar ((0,k),b)*psi ((0,l),b))) = if a=b then orderedFour d a a x i j k l else 0:=by
     by_cases h:a=b
     · subst b; rw [if_pos rfl]; apply arbitraryOrder (p:=.inr ((0,i),a)) (q:=.inl ((0,j),a))
         (r:=.inr ((0,k),a)) (s:=.inl ((0,l),a)) <;> simp
     let A : SpinMode d:= ((0,i),a); let B: SpinMode d:=((0,j),a); let C: SpinMode d:=((0,k),b); let D: SpinMode d:=((0,l),b)
     rw [if_neg h]; refine (arbitraryOrder d x (p:=.inr A) (q:=.inl B) (r:=.inr C) (s:=.inl D) (by simp) (by simp)).trans ?_; rw [valFour]; simp [Free.pair,Free.leg,h,Ne.symm h,A,B,C,D]
noncomputable def joined (v w: Bundle) (x: E4) :ℂ:= - Matrix.trace (v * prop x*w* prop (-x))
theorem rows (d:ℕ)(a:Fin 6){x: Points 2}(h:x 0 ≠ x 1)(P Q: Spike) : expand P (fun i j=> expand Q (orderedFour d a a x i j))= joined (wave P) (wave Q) (x 0-x 1):=by
     have rev: -(x 0 - x 1)= x 1-x 0:= neg_sub ..
     simp only [expand,orderedFour_value d a a h,joined,rev,mul_assoc,
         Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.mul_sum,← Finset.sum_neg_distrib]
     apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
theorem tango (d:ℕ)(a b:Fin 6){x:Points 2}(h:x 0≠ x 1)(P Q: Spike) : Free.moment (fun _ : Fin 2=>d) x ![UV.bilinear a a P 0 0,UV.bilinear b b Q 0 0]=
      if a=b then joined (wave P) (wave Q) (x 0-x 1) else 0:=by
     rw [← bondEval]; have terms (v:Fin 6)(P:Spike) : UV.bilinear v v P (0:Multi d) 0 = ∑ i:Pinor,∑ j:Pinor, ∑ r:Hue,P i j • spinIn d (bar ((0,i,r),v)*psi ((0,j,r),v)):=by
          change spinIn d _ =_; simp only[map_sum,map_smul]; -- debug
     rw [terms a P]; simp only [map_sum,map_smul,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul]; rw [terms b Q]; simp only[map_sum,map_smul,smul_eq_mul,massLegs]
     by_cases ht:a=b
     · rw [if_pos ht]; simp only[ht,if_true]; rw[← rows d b h]; simp only [expandBilinear]
     simp [ht]
end YM.MassiveMasses.FreePair
#print axioms YM.MassiveMasses.FreePair.tango
