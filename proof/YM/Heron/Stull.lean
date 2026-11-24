import YM.Heron.Palm
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (fromCenter)
open Maxwell (grad)
open MvPolynomial hiding eval
open Finset
variable {d:ℕ}(A:EuPin)(p q r: Multi d)(z:E4)(W:Spins)(a:Axis)
local notation "X"=> MvPolynomial.X (R:=ℂ)
noncomputable def holder(d:ℕ)(x:E4)(W:Spins): MvPolynomial Axis ℂ →ₗ[ℂ] Faces:= ∑ p:Multi d, LinearMap.smulRight (MvPolynomial.lcoeff ℂ (token p)) (deriveL (steps p) W x) -- check lcoeff
lemma burst : holder d z W (UV.walk p)= deriveL (steps p) W z:=by
    unfold holder; rw [LinearMap.sum_apply]; change ∑ q: Multi d, MvPolynomial.coeff (token q) (UV.walk p) • deriveL (steps q) W z=_; simp only [walk,coeff_monomial,token_eq,ite_smul,one_smul,zero_smul, sum_ite_eq,mem_univ,↓reduceIte] -- smul_left orientation
lemma sprouted (h:AtNext a p q): walk q=X a * walk p:=by
     have he : token q= token p+ Finsupp.single a 1:=by
         ext j; rw [Finsupp.add_apply,token_act,token_act, show power q= _ from h]; by_cases hj:a=j; · subst j; simp;
         simp [hj,Ne.symm hj]
     unfold walk; rw [he,MvPolynomial.X]; rw[MvPolynomial.monomial_mul,one_mul,add_comm]
lemma prey : p ≠0 → ∃ i q, AtNext i q p:=by
    intro hp; have he:= not_congr (Massive.Oriole.ground_iff p); obtain ⟨i,hi⟩:∃ i:Axis,0 < power p i:=by
        by_contra! h; have h0(i):power p i=0:=Nat.eq_zero_of_le_zero (h i); exact he.mpr hp (by simp [order,h0])
    exact ⟨i,(Elm.Pulses.nextFound p i).mpr hi⟩
variable {U:Set E4}(hU:IsOpen U)(hz:z∈ U)(H:∀ x∈U,ContDiffAt ℝ ∞ W x)
include hU hz H
lemma stock (h:AtNext a p q) : deriveL (steps q) W z= deriveL (steps p) (grad a W) z:=by
    exact (commute_a hU W H _ _ ((DawnS.permutation h).trans (show List.Perm _ (steps p ++ [a]) from List.perm_append_comm (l₁:=[a]) (l₂:=steps p))) z hz).trans (congr_fun (lyras (steps p) [a] _) z)
lemma town (h:AtNext a p q): changeP A (walk q) = (∑ i:Axis,(A.coord.val i a:ℂ) • (X i))* (∑ r:Multi d,multiMove A p r • walk r):=by
    rw [sprouted _ _ _ h,map_mul,collect (x:=p),changeP,aeval_X]; unfold stencilFrame; congr 1; apply Finset.sum_congr rfl; intro i _; exact MvPolynomial.C_mul' ..
-- could avoid prophecy nonunit estimates
lemma breeze (h:AtNext a p q):
    holder d z W (changeP A (walk q)) = ∑ i:Axis,(A.coord.val i a:ℂ) • (∑ r:Multi d, multiMove A p r • deriveL (steps r) (grad i W) z):=by
    rw [town A p q z W a hU hz H h,Finset.sum_mul,_root_.map_sum]; apply sum_congr rfl; intro i _; simp_rw[Finset.mul_sum,map_sum,Finset.smul_sum]; apply sum_congr rfl; intro r _; rw [_root_.smul_mul_assoc, _root_.mul_smul_comm, _root_.map_smul,_root_.map_smul]; by_cases he: multiMove A p r=0; · rw[he,zero_smul,zero_smul]
    have hp:= UV.invariant_level _ _ _ he; obtain ⟨y,hy⟩:= (afterP r i).mpr (by rw[hp]; exact (afterP p a).mp ⟨q,h⟩); rw[← sprouted r y i hy,burst, stock r y z W i hU hz H hy] -- signatures
noncomputable def tent (z:E4)(t:Bool)(p:Multi d)(W:Spins)(A:EuPin) : Faces:= turnG A t (holder d z W (changeP A (walk p))) -- includes params from include syntax
lemma poseP(t:Bool): tent z t p W A = ∑ q: Multi d,multiMove A p q • turnG A t (deriveL (steps q) W z):=by unfold tent; rw [collect]; simp only[_root_.map_sum,_root_.map_smul,burst]
end YM.Heron
#print axioms YM.Heron.prey
#print axioms YM.Heron.breeze
#print axioms YM.Heron.poseP
