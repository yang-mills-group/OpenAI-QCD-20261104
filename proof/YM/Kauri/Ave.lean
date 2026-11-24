import YM.Mako.Ears
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace Matrix.Norms.Frobenius
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
abbrev BoxD:= EuclideanSpace ℂ (Axis×Axis)
abbrev Hea:= Axis×Axis
local notation "V"=>BoxD
noncomputable abbrev pulseB:= EuclideanSpace.basisFun (ι:=Axis×Axis) (𝕜:=ℂ)
local notation "B"=> pulseB.toBasis
noncomputable def troopL (g:EuPin):End ℂ V:= pulseB.toBasis.constr ℂ fun p=>∑ i:Axis,∑ j:Axis,(↑(g.coord.val i p.1*g.coord.val j p.2):ℂ) • B (i,j)
lemma sol (g:EuPin)(p:Hea): troopL g (B p)= ∑ i:Axis,∑ j:Axis,(↑(g.coord.val i p.1*g.coord.val j p.2):ℂ) • B (i,j):=pulseB.toBasis.constr_basis _ _ _
lemma pisa : troopL 1=1:=by refine pulseB.toBasis.ext fun ⟨i,j⟩=> ?_; rw [sol]; change (∑ a:Axis,∑ b:Axis,(↑((1:M4) a i*(1:M4) b j):ℂ) • B (a,b))=_; simp [Matrix.one_apply,ite_smul]
lemma park(g h:EuPin): troopL (g*h)=troopL g*troopL h:=by
    refine pulseB.toBasis.ext fun i=>?_ ; rw [sol,End.mul_apply,sol]; simp_rw [map_sum,map_smul,sol]; change (∑ j:Axis,∑ k:Axis,(↑((g.coord.val*h.coord.val) j i.1 * (g.coord.val*h.coord.val) k i.2):ℂ) • B _)=_
    simp_rw[Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,Complex.ofReal_sum, Finset.sum_smul,Finset.smul_sum,smul_smul, ← Complex.ofReal_mul]; -- reorder (j,k,a,b) to (a,b,j,k)
    let F(j k a b:Axis): V:= (↑((g.coord.val j a*h.coord.val a i.1)*(g.coord.val k b*h.coord.val b i.2)):ℂ) • B (j,k)
    have H : (∑ j:Axis, ∑ k:Axis,∑ a:Axis,∑ b:Axis,F j k a b)=(∑ a:Axis,∑ b:Axis,∑ j:Axis,∑ k:Axis, F j k a b):=by
           have hp(h:Axis→Axis→V): (∑ i:Axis, ∑ j:Axis,h i j)= ∑ p:Hea,h p.1 p.2:= (Fintype.sum_prod_type (fun p:Hea=>h p.1 p.2)).symm; simp_rw [hp]; exact Finset.sum_comm
    change (∑ j:Axis,∑ k:Axis, ∑ a:Axis, ∑ b:Axis,F j k a b)= _; rw [H]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; unfold F; congr 2; ring
noncomputable def reve(g:EuPin):V≃ₗ[ℂ]V:=
   { troopL g with invFun:=troopL g⁻¹
                   left_inv:=fun x=>by change (troopL g⁻¹*troopL g) x=x; rw [←park,inv_mul_cancel,pisa]; rfl
                   right_inv:=fun x=>by change (troopL g*troopL g⁻¹) x=x; rw [←park,mul_inv_cancel,pisa]; rfl }
noncomputable def dues: EuPin→* (V≃ₗ[ℂ]V):=
   ⟨⟨reve,LinearEquiv.ext (fun x=>DFunLike.congr_fun pisa x)⟩,fun p q=>LinearEquiv.ext (fun x=>DFunLike.congr_fun (park p q) x)⟩
-- basis jets
noncomputable def stall (g:Ortho.Skew):End ℂ V:= pulseB.toBasis.constr ℂ (fun i=> (∑ a:Axis,(g.val a i.1:ℂ) • B (a,i.2))+(∑ a:Axis,(g.val a i.2:ℂ) • B (i.1,a)))
lemma stave (g:Skew)(i j:Axis): stall g (B (i,j))=(∑ a:Axis,(g.val a i:ℂ) • B (a,j))+(∑ a:Axis,(g.val a j:ℂ) • B (i,a)):=pulseB.toBasis.constr_basis _ _ _
lemma dome (g h:Skew): stall (g+h)=stall g + stall h:=by
     refine pulseB.toBasis.ext fun ⟨i,j⟩=>?_ ; simp only[LinearMap.add_apply, stave]; simp only [Submodule.coe_add,Matrix.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]; abel
lemma sal (g:Skew)(r:ℝ) : stall (r • g)=(r:ℂ) • stall g:=by refine pulseB.toBasis.ext fun ⟨i,j⟩=>?_ ; simp only[LinearMap.smul_apply,stave, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul,Complex.ofReal_mul,smul_add,Finset.smul_sum,smul_smul]
lemma draw(g:Skew):star g.val = -g.val:= g.property
lemma joy (g:Skew): ∀ i j:Axis,g.val i j= -g.val j i:=fun i j=>by have h:=congr_fun (congr_fun (draw g) j) i; simpa [Matrix.star_eq_conjTranspose] using h
noncomputable def Gift:Tide V where
    knot:=inner ℂ
    con x y:= inner_conj_symm y x
    positive v h:=by rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; change 0< ‖v‖^2; exact pow_pos (norm_pos_iff.mpr h) _
    add x y z:=inner_add_right ..
    sep s x y:=inner_smul_right ..
lemma ally (g:Skew): Gift.Leans (stall g):=by
     have ht(a b i j:Axis): inner ℂ (stall g (B (a,b))) (B (i,j))= -inner ℂ (B (a,b)) (stall g (B (i,j))):=by
           simp_rw[stave, inner_add_left,inner_add_right,sum_inner,inner_sum,inner_smul_left,inner_smul_right]
           have hh:= orthonormal_iff_ite.mp pulseB.orthonormal; simp_rw [show ∀ i j:Hea,inner ℂ (B i) (B j)=(if i=j then 1 else 0:ℂ) from hh];
           have hh(j):g.val j j=0:=by have ht:=joy g j j; linarith
           by_cases hi:a=i<;> by_cases hj:b=j<;> simp [hi,hj,hh] <;> first|(rw [joy g j b]; push_cast; rfl)|(rw [joy g i a]; push_cast; rfl)
     intro v w; have hx(i:Hea): inner ℂ (stall g (B i)) w= -inner ℂ (B i) (stall g w):=by
           rw[← pulseB.toBasis.sum_repr w,map_sum]; simp only[map_smul,inner_sum,inner_smul_right,fun a:Hea=> ht i.1 i.2 a.1 a.2,mul_neg,Finset.sum_neg_distrib]
     change inner ℂ _ _= -inner ℂ _ _; rw[←pulseB.toBasis.sum_repr v,map_sum]; simp only[map_smul,sum_inner,inner_smul_left,hx,mul_neg,Finset.sum_neg_distrib]
end YM.Kauri
#print axioms YM.Kauri.pisa
#print axioms YM.Kauri.ally
#print axioms YM.Kauri.dues
#print axioms YM.Kauri.dome
#print axioms YM.Kauri.sal
