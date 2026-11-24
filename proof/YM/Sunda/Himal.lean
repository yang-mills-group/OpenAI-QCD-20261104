import YM.Sunda.Stalk
import Mathlib.LinearAlgebra.Matrix.Permutation
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
variable (a b:Hue)(u:su.El)
local notation "P"=>Equiv.Perm Hue
local notation "M"=> Module.End ℂ (Pol 9)
def bitZ(a b: Hue):ℂ:= if a=b then 1 else -1
def chipZ(a:Hue):Mat:= Matrix.diagonal (bitZ a)
lemma shareZ: ∃ z:su.El, colour z=chipZ a:=by
    apply colorsU; · have hs:star (chipZ a)=chipZ a:=by
                           ext i j; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,chipZ,Matrix.diagonal_apply]; split <;> rename_i h; · subst j; simp [bitZ]; split <;> simp
                           rw [if_neg (Ne.symm h)]; simp
                     have ht:∀ i,bitZ a i*bitZ a i=1:=fun i=> by unfold bitZ; split <;> ring
                     constructor <;> rw [hs,chipZ,Matrix.diagonal_mul_diagonal]; all_goals (ext i j; rw[Matrix.diagonal_apply, Matrix.one_apply]; split <;> first|exact ht _|rfl)
    unfold chipZ; rw [Matrix.det_diagonal]; fin_cases a <;> norm_num [bitZ,Hue, Fin.prod_univ_succ] <;> decide
noncomputable def bankZ(a: Hue):su.El:=(shareZ a).choose
noncomputable abbrev rimP(a:Hue): M := colorAct (bankZ a)+1
noncomputable def keels : M:= rimP 0*(rimP 1*rimP 2)
variable(i j k:Pinor) (f g:P)
local notation "E"=> Pearl.rowW i j k
noncomputable def capZ (i j k:Pinor)(z:Pearl.Triple):Pol 9 := (1:GPol)⊗ₜ[ℂ] Pearl.rowW i j k z
abbrev rateZ(a:Hue)(z:Pearl.Triple):=bitZ a z.1*bitZ a z.2.1*bitZ a z.2.2
private lemma hasZ(p:Multi 9)(q:Flavor 6)(i:Pinor)(h:Hue): dyeS 9 (bankZ a) (male p q i h)= bitZ a h • male p q i h:=by rw[drizzle,show colour (bankZ a)=_ from (shareZ a).choose_spec]; simp [chipZ, Matrix.diagonal_apply,ite_smul]
variable (z:Pearl.Triple)
lemma sight : rimP a (capZ i j k z)= (rateZ a z+1) • capZ i j k z:=by
      let G:= bankZ a; change colorAct G _+capZ i j k z=_; have ht:colorAct G (capZ i j k z)= rateZ a z • capZ i j k z:=by
              unfold capZ; rw [paint_weight,← tmul_smul]; apply congr_arg; unfold Pearl.rowW; rw[map_mul,map_mul]; unfold Pearl.isk Pearl.esk Pearl.ots; rw[hasZ,hasZ,hasZ,_root_.smul_mul_smul_comm, _root_.smul_mul_smul_comm]
      rw [ht]; exact (one_smul ℂ (capZ i j k z) ▸ (_root_.add_smul (rateZ a z) (1:ℂ) (capZ i j k z))).symm
lemma scales : keels (capZ i j k z) = ((rateZ 2 z+1)*(rateZ 1 z+1)*(rateZ 0 z+1)) • capZ i j k z:=by
      unfold keels; simp only[End.mul_apply,sight,map_smul, smul_smul]
lemma ferry(h:((rateZ 2 z+1)*(rateZ 1 z+1)*(rateZ 0 z+1))≠0):∃ f:P,z=Pearl.α f:=by
      obtain ⟨x,y,w⟩:=z; let r: Hue → Hue:= ![x,y,w]; have he:x≠y∧ x≠w∧y≠w:=by fin_cases x<;> fin_cases y <;> fin_cases w<;> first|decide|(exfalso; apply h; unfold rateZ bitZ; norm_num +decide)
      have hv: Function.Injective r:=by intro i j; fin_cases i<;> fin_cases j <;> simp [r,he.1,he.2.1,he.2.2,Ne.symm he.1,Ne.symm he.2.1,Ne.symm he.2.2]
      exact ⟨Equiv.ofBijective r ((Finite.injective_iff_bijective ..).1 hv),rfl⟩
lemma epics (f:P):Pearl.ε f *Pearl.ε f=1∧star (Pearl.ε f)=Pearl.ε f:=by
      rcases Int.units_eq_one_or (Equiv.Perm.sign f) with h|h <;>simp[Pearl.ε,h]
noncomputable def heartZ(f:P):Mat:= Pearl.ε f • f.permMatrix ℂ
lemma ceilf(f:P):∃ z:su.El,colour z=heartZ f:=by
       apply colorsU; · let m:= f.permMatrix ℂ; let p:ℂ:= Pearl.ε f; have hp1: star m*m=1:=by rw [Matrix.star_eq_conjTranspose]; simp only [m,Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul]; simp
                        have hp2:m*star m=1:=by rw [Matrix.star_eq_conjTranspose]; simp only [m,Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul]; simp
                        constructor <;> (change _=1; unfold heartZ; rw[star_smul, (epics f).2, smul_mul_smul_comm,(epics f).1,one_smul]); exact hp1; exact hp2
       unfold heartZ; rw [Matrix.det_smul,Fintype.card_fin,Matrix.det_permutation]; change Pearl.ε f^3*Pearl.ε f=1; rw [pow_succ,pow_two,(epics f).1,one_mul,(epics f).1]
noncomputable def shrine(f:P):su.El:=(ceilf f).choose
noncomputable def shoal :M:= ∑ f:P,colorAct (shrine f)
private lemma plasma (p:Multi 9)(q:Flavor 6): dyeS 9 (shrine f) (male p q i a)= Pearl.ε f • male p q i (f a):=by
        rw[drizzle,show colour (shrine f)= _ from (ceilf f).choose_spec]; unfold heartZ; simp only[Matrix.smul_apply]; rw [sum_eq_single (f a)]; · rw [show f.permMatrix ℂ a (f a)=1 from (by simp),smul_eq_mul,mul_one]
        · intro x _ hx; rw [show f.permMatrix ℂ a x=0 from by simp[hx,hx.symm],smul_zero,zero_smul]
        simp
lemma skiff : colorAct (shrine f) (capZ i j k (Pearl.α g))= Pearl.ε f • capZ i j k (Pearl.α (f*g)):=by
        unfold capZ; rw[paint_weight,←tmul_smul]; apply congr_arg; unfold Pearl.rowW; rw[map_mul,map_mul]; unfold Pearl.isk Pearl.esk Pearl.ots; rw [plasma,plasma,plasma,smul_mul_smul_comm,smul_mul_smul_comm,(epics f).1,one_mul]; rfl
lemma plows : shoal (capZ i j k (Pearl.α g))= Pearl.ε g • UV.baryon i j k:=by
      rw[Pearl.τ,shoal]; simp_rw[LinearMap.sum_apply,skiff]; rw [Pearl.lighthouse, tmul_sum, Finset.smul_sum]
      rw[← Equiv.sum_comp (Equiv.mulRight g) (fun f:P=> Pearl.ε g • ((1:GPol)⊗ₜ[ℂ](Pearl.ε f • E (Pearl.α f))))]; apply sum_congr rfl; intro f _; rw[tmul_smul,smul_smul, show Pearl.ε (Equiv.mulRight g f)=Pearl.ε f * Pearl.ε g from (by simp[Pearl.ε])]; rw [show Pearl.ε g*(Pearl.ε f*Pearl.ε g)=Pearl.ε f from by rw [mul_left_comm,(epics g).1,mul_one]]; rfl
set_option quotPrecheck false
local notation "F"=> Submodule.span ℂ (Set.range fun q:Pinor × Pinor × Pinor=>UV.baryon q.1 q.2.1 q.2.2)
noncomputable def heapZ : Submodule ℂ (Pol 9):= F
lemma quotes : Peak≤ heapZ.comap (shoal*keels):=by
       apply Submodule.span_le.mpr; rintro x ⟨⟨i,j,k,z⟩,rfl⟩; change shoal (keels (capZ i j k z))∈ heapZ; rw[scales,map_smul]; by_cases h:(rateZ 2 z+1)*(rateZ 1 z+1)*(rateZ 0 z+1)=0; · rw[h,zero_smul]; exact heapZ.zero_mem
       apply Submodule.smul_mem; obtain ⟨f,rfl⟩:= ferry z h; rw [plows]; apply Submodule.smul_mem; exact Submodule.subset_span (show UV.baryon i j k∈ Set.range (fun q:Pinor × Pinor × Pinor=> UV.baryon q.1 q.2.1 q.2.2) from ⟨(i,j,k),rfl⟩)
end YM.Sunda
#print axioms YM.Sunda.quotes
#print axioms YM.Sunda.plows
