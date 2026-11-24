import YM.Massive.Hawser.Cogs
/-!
Scalar/axial etc. weight `ℓ=6` realizes all flavors in the RawSym
label space. Exterior epsilons give actual weight `9` elements,
even before passage to quotient(s). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Lattice Wilson RG Source Function QCD Lat Massive Lining Papyrus Filter Work.G05 Finset Matrix Grass TensorProduct
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
variable (d:ℕ)(a b:Flavor 6)(S:Spike)(i j k:Pinor)
local notation "P" => Equiv.Perm Hue
def sPair (d:ℕ):SpinPol d:=∑ u:Pinor,∑ v:Pinor,∑ z:Hue, S u v • (other 0 a u z*male 0 b v z)
lemma weight_m : sPair a b S d∈weightS 6:=by -- implicit param order
   refine Submodule.sum_mem _ (fun x _=> Submodule.sum_mem _ (fun y _=> Submodule.sum_mem _ (fun z _=> ?_))); apply Submodule.smul_mem; have hh: other (0:Multi d) a x z*male 0 b y z∈weightS (spinWeight (0:Multi d)+spinWeight (0:Multi d)):= Rim.payroll letterWeight (q_other (0:Multi d) a x z) (q_male (0:Multi d) b y z); rw [cost_root] at hh; exact hh
variable (u:su.El)
private lemma singletPlan (i j:Hue) : ∑ k, (star (colour u k i))* (colour u k j)=if i=j then 1 else 0:=by
    let V:=colour u; change _=if _ then _ else _; rw [← Matrix.one_apply (α:=ℂ)]; exact congr_arg (fun x:Mat=> x i j) (Papyrus.Boat.starcolour u)
private lemma element (Z:ℂ): dyeS d u (∑ z:Hue, Z • (other 0 a i z*male 0 b j z))=∑ z:Hue,Z • (other 0 a i z*male 0 b j z):=by
   rw [← smul_sum,map_smul]; apply congr_arg (fun x:SpinPol d=> Z • x); simp_rw [map_sum,map_mul,drizzle_rev,drizzle,Finset.sum_mul, Finset.mul_sum, _root_.smul_mul_assoc,_root_.mul_smul_comm,smul_smul];
   rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]; simp_rw [←Finset.sum_smul, singletPlan]; simp [ite_smul] -- order
lemma color_pair : dyeS _ u (sPair a b S d) = sPair a b S d:=by unfold sPair; rw [map_sum]; exact sum_congr rfl (fun i _=> by rw [map_sum]; exact sum_congr rfl fun j _=> element d a b i j u _)
lemma parity_pair : grade (sPair a b S d)= sPair a b S d:= by simp_rw [sPair,map_sum,map_smul,map_mul,male,other,psi,bar,grade_atom,neg_mul_neg]
variable (p:FlavorTorus)
abbrev paidM : ℂ:= star (p a).val*(p b).val
lemma flavor_cover : pigment d p (sPair a b S d)= paidM a b p • sPair a b S d:=by unfold sPair; simp_rw [smul_sum,map_sum,map_smul,map_mul,pig_b,pig_p,_root_.smul_mul_assoc,_root_.mul_smul_comm,smul_comm (paidM a b p) (S _ _ : ℂ), paidM, mul_smul]; -- rfl
lemma meson_label (h:6≤d) : bilinear (d:=d) a b S 0 0∈labels d:=by
    rw [label_law]; refine ⟨ivory _ 6 h (weight_m d a b S),fun g=> ?_⟩ -- no '.. after args' syntax
    change colorAct g ((1:GPol) ⊗ₜ[ℂ] sPair a b S d)=_; rw [paint_weight,color_pair]; rfl
noncomputable def mesonCode (h:6≤d): Label d:=⟨_,meson_label d a b S h⟩
lemma meson_weight (h:6≤d)(w:RawSym) : w.flavor d p (mesonCode d a b S h)= paidM a b p • mesonCode d a b S h:=by
   apply Subtype.ext; rw [w.flavorActs]; change flavorAct p ((1:GPol) ⊗ₜ[ℂ] sPair a b S d)=paidM a b p • _; rw [pig_weight,flavor_cover,tmul_smul]; rfl
noncomputable def Mass : MassFields where
    mesonThree a b M:= mesonCode 6 a b M le_rfl
    mesonFour a b M := mesonCode 8 a b M (by norm_num)
    fixedThree _ _ _:=rfl
    fixedFour _ _ _:=rfl
end YM.Massive.UV
#print axioms YM.Massive.UV.Mass
