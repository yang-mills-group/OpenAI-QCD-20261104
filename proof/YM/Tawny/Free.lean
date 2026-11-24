import YM.Tawny.Drill
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Drill
open Matrix Perla Zinc Rays TableT Complex
open scoped Kronecker
local notation "V"=>Pinor→ℂ
variable (f:Pinor→ℂ)
noncomputable def axis : Axis →ℂ := ![1,0,0,Complex.I]
local notation "S"=> sectionV axis
lemma like : S = gamma 0 + Complex.I • gamma 3:=by simp [sectionV,axis,Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one]
lemma nitro:S*S=0:=by have he := Lat.clifford (by decide : (3:Axis) ≠ 0); rw [like]; calc
                           _= (gamma 0*gamma 0)+ I • (gamma 0*gamma 3+gamma 3*gamma 0)+(I*I) • (gamma 3*gamma 3):=by simp only [add_mul,mul_add, Matrix.smul_mul, Matrix.mul_smul,smul_smul,smul_add]; abel
                           _=_:=by rw [he,add_neg_cancel,smul_zero,Lat.gamma_sq,Lat.gamma_sq,I_mul_I,neg_one_smul]; abel
lemma oxy: S≠0:=by
     intro h; have he:= congr_arg (star) h; rw [like] at h he; rw[star_add, star_smul] at he; simp only [gamma_star,star_zero, Complex.star_def] at he; simp at he; -- possible he shows self
     have hv:gamma (0:Axis)+gamma 0=0:= calc
          _= (gamma 0+ I • gamma 3)+(gamma 0+ -(I • gamma 3)):=by abel
          _= _:=by rw [h,he,zero_add]
     have ht: -(gamma (0:Axis))=gamma 0:= (add_eq_zero_iff_eq_neg.mp hv).symm
     have hj:= negS _ ht; have u:= Lat.gamma_sq (0:Axis); rw [hj,zero_mul] at u; exact zero_ne_one u
lemma freedom :∃ f:Pinor→ℂ, SlashV axis f ∧ f≠0:=by
     obtain ⟨i,j,h⟩:∃ i j:Pinor,S i j≠0:=by by_contra! h; apply oxy; ext i j; exact h _ _
     refine ⟨fun i=>S i j,?_,fun h₀=>h (congr_fun h₀ i)⟩; intro k; change (S*S) k j=0; rw[nitro]; rfl
lemma vacancy : SlashV (0:Axis→ℂ) f:=by intro x; simp [sectionV]
lemma radial(v:Axis→ℂ)(e:ℂ)(h:SlashV v f) :SlashV (e • v) f:=by
     have he : sectionV (e • v)=e • sectionV v:=by simp only[sectionV, Pi.smul_apply, smul_sum,smul_smul, smul_eq_mul]
     intro i; simp_rw [he, Matrix.smul_apply,smul_eq_mul,mul_assoc, ← Finset.mul_sum, h i, mul_zero] -- error H lhs fold
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.freedom
