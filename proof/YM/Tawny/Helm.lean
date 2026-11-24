import YM.Tawny.Drill
import YM.Tawny.Shade
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
open Matrix TableT Carnal Rays Perla Zinc
open scoped Kronecker
variable (v:Axis→ℂ)(b c: Hue)(M:Spike)(f g: Pinor →ℂ)
variable (h:SlashV v f) (X:Maxwell.TaylorTower su)
local notation "L"=> throne a v b c f g (d:=d)
local notation "H"=> hear a v b c f g h X
local notation "u" => Unit.unit
noncomputable def coinU : Dirac Unit →ₗ[ℂ] ℂ:= { toFun:=fun X=> uncoat X u u, map_add':=fun x y=>by rw[map_add]; rfl, map_smul':=fun c x=>by rw [map_smul]; rfl }
private lemma feast_unit : coinU 1=0:=by change - -coef ∅ (vary (Sum.inl ()) (vary _ _))=0; simp [vary_one]
private lemma praise : coinU (bar u*psi u)=1:=by
    have h: Oriole.coat ((1:Matrix Unit Unit ℂ))=bar u*psi u:=by change -(form (1:Matrix Unit Unit ℂ))= _; simp [form,bar,psi]; rw [atom_flip,neg_neg]; -- inspect
    rw [← h]; change uncoat _ u u=1; rw [coat_known]; rfl
noncomputable def vitality (E:ℕ): Pol E→ₗ[ℂ]ℂ := coinU.comp ((hear a v b c f g h X).comp reduceEq)
noncomputable def goldF (E:ℕ):Pol E→ₗ[ℂ]ℂ:= (coef ∅).comp ((hear a v b c f g h X).comp reduceEq)
variable (u':Flavor 6)(p q:Multi d) (k: SpinMode d)
local notation "Ψ"=> vitality a v b c f g h X
local notation "ζ"=>goldF a v b c f g h X
include h
lemma dustU (k: SpinMode d): ExteriorAlgebra.map (L) (psi k)= dcol v a b f k • psi u ∧ ExteriorAlgebra.map (L) (bar k)= drow a c g k • bar u:=by unfold psi bar atom; simp_rw [ExteriorAlgebra.map_apply_ι, C_th, B_th]; constructor <;> exact map_smul (ExteriorAlgebra.ι ℂ) _ _
lemma visaU (Z:GPol): Ψ d (plain d Z)=0:=by unfold vitality; rw [LinearMap.comp_apply,LinearMap.comp_apply,plainP,hears,map_smul,map_one,feast_unit,smul_zero]
lemma axisU (Z:GPol): ζ d (plain d Z)=Labels.read (Perla.Fore.lexY X) Z:=by unfold goldF; rw[LinearMap.comp_apply,LinearMap.comp_apply,plainP,hears,map_one,map_smul,← mono_empty,Grass.read,smul_eq_mul,mul_one]
omit h
lemma ζ_empty : coef ∅ (bar u*psi u)=0:=by
    unfold psi bar; rcases bladeX (Sum.inr u) (Sum.inl u) (by intro h; cases h) with he|he
    · rw[he,Grass.read_other]; exact Ne.symm (insert_ne_empty _ _)
    rw [he,map_neg,Grass.read_other,neg_zero]; exact Ne.symm (insert_ne_empty _ _)
include h
lemma axis_b(G:GPol)(i j:SpinMode d) : ζ d (G ⊗ₜ[ℂ] (bar i*psi j))=0:=by unfold goldF; rw[LinearMap.comp_apply,LinearMap.comp_apply,hears,map_mul,(dustU a v b c f g h i).2,(dustU a v b c f g h j).1,smul_mul_assoc,mul_smul_comm,_root_.map_smul,_root_.map_smul,_root_.map_smul,ζ_empty]; simp
lemma p_hue : ζ d (bilinear u' u' M p q)=0:=by unfold bilinear; simp_rw [TensorProduct.tmul_sum,TensorProduct.tmul_smul,_root_.map_sum,_root_.map_smul,axis_b,smul_zero,sum_const_zero]
lemma t_b(G:GPol)(i j:SpinMode d) : Ψ d (G⊗ₜ[ℂ] (bar i*psi j)) = Labels.read (Perla.Fore.lexY X) G *(drow a c g i* dcol v a b f j):=by
     unfold vitality; rw [LinearMap.comp_apply,LinearMap.comp_apply,hears,map_mul,(dustU a v b c f g h i).2,(dustU a v b c f g h j).1,_root_.smul_mul_assoc,_root_.mul_smul_comm,map_smul,map_smul,map_smul,praise]; simp
omit h
noncomputable def rowC (g f:Pinor→ℂ)(S:Spike):ℂ := ∑ i:Pinor,∑ j:Pinor,g i* S i j*f j
include h
set_option maxHeartbeats 860000 in
lemma epig : Ψ d (bilinear u' u' M p q)=if u'=a∧b=c∧p=0 then pay q v* rowC g f M else 0:=by
    unfold bilinear; simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,map_sum,map_smul,t_b,map_one,one_mul,drow,dcol]; by_cases he:u'=a∧b=c∧p=0; · rw [if_pos he]; obtain ⟨hu,hb,hp⟩:=he; subst u' b p; simp only[true_and,and_true]; unfold rowC; rw [Finset.mul_sum]; apply sum_congr rfl; intro i h; rw[Finset.mul_sum]; apply sum_congr rfl; intro j _; rw [sum_eq_single c]; simp only[↓reduceIte,smul_eq_mul]; ring; intro x _ ht; simp [ht]; simp
    rw [if_neg he]; refine sum_eq_zero (fun i _=> sum_eq_zero fun j _=> sum_eq_zero fun k _=>?_); by_cases hv:k=b∧u'=a; · obtain ⟨hk,rfl⟩:=hv; rw [if_neg (by grind), zero_mul,smul_zero]
    by_cases hx:k=c∧ u'=a ∧ p=0; · obtain ⟨hk,rfl,hp⟩:=hx; rw [if_pos (by simp [hk,hp]),if_neg (by tauto),mul_zero,smul_zero]
    rw [if_neg (by tauto),zero_mul,smul_zero]
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.t_b
