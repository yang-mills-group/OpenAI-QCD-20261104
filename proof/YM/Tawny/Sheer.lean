import YM.Tawny.Helm
import YM.Tawny.Free
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
open TableT Carnal Rays Perla Zinc
open scoped Kronecker
variable (v:Axis→ℂ)(b c: Hue)(i j k:Axis)(M:Spike)(f g: Pinor →ℂ)(B:Bundle)
variable (h:SlashV v f) (X:Maxwell.TaylorTower su) (u':Flavor 6)
local notation "H"=> hear a v b c f g h X
local notation "u" => Unit.unit
local notation "L"=> throne a v b c f g (d:=10)
local notation "J"=>Perla.Fore.lexY X
local notation "Ψ"=> vitality a v b c f g h X 10
local notation "ζ"=>goldF a v b c f g h X 10
lemma singleM (x y:SpinMode d)(z:ℂ): coat (Matrix.single x y z)=z • (bar x*psi y):=by
    have ht:=congr_arg (ready d 0) (j_single x y z); change ready _ _ (1⊗ₜ[ℂ]coat _)=_ at ht; rw [ready_t,ready_t,map_one,one_smul,one_smul] at ht; exact ht
include h
lemma fog_star : ζ (youthL u' i j M)=0:=by
    unfold youthL; rw [map_sum]; apply sum_eq_zero; intro n _; unfold weave; rw [show ∀ V,yard u' V= fieldB u' u' (0:Multi 10) 0 V from (fun _=>rfl), fieldB]; simp_rw[map_sum,TensorProduct.tmul_sum,singleM,TensorProduct.tmul_smul,map_sum,map_smul,axis_b,smul_zero,sum_const_zero]
lemma drillM(i j:Fiber)(z:ℂ) : let t: Fiber→SpinMode 10:=fun i=> ((0,i),u'); let E:= coat (Matrix.single (t i) (t j) z); coinU (ExteriorAlgebra.map L E)=z*(drow a c g (t i)*dcol v a b f (t j)):=by
    intro t E; let e:SpinMode 10:= t i; let w:SpinMode 10:=t j; have he:= t_b (d:=10) a v b c f g h (0:Maxwell.TaylorTower su) (1:GPol) e w
    unfold vitality at he; rw [LinearMap.comp_apply,LinearMap.comp_apply,hears,map_one,one_smul,one_mul] at he
    unfold E; rw [singleM,map_smul,map_smul]; exact congr_arg (z * ·) he
lemma mixedY : Ψ (youthL u' i j M)=(if u'=a then (BendR.ore (StressFlux.curl0 i j (J 0))) c b *rowC g f M else 0):=by
    let G':SpinPol 10→ₗ[ℂ]ℂ:= coinU.comp (ExteriorAlgebra.map L).toLinearMap
    have he(p:Pol 10): Ψ p=G' (ready 10 J p):=by
         induction p using TensorProduct.induction_on with
         | zero=> simp
         | add x y hx hy=> simp_rw [map_add,hx,hy]
         | tmul x y=>rw [vitality,LinearMap.comp_apply,LinearMap.comp_apply,hears,map_smul,ready_t,map_smul]; rfl
    let Xc:Mat:= BendR.ore (StressFlux.curl0 i j (J 0)); let B := whirl (StressFlux.curl0 i j (J 0)) M; rw [he,yMobi]; unfold weave
    change G' (coat (fieldB _ _ _ _ _))=if u'=a then Xc c b*_ else _; unfold fieldB; simp only[map_sum];
    let t:Fiber→SpinMode 10:=fun i=> ((0,i),u'); change ∑ i:Fiber,∑ j:Fiber,G' (coat (Matrix.single (t i) (t j) (B i j)))=_
    have hz (i j:Fiber): G' (coat (Matrix.single (t i) (t j) (B i j)))= B i j* (drow a c g (t i)*dcol v a b f (t j)):= drillM a v b c f g h u' i j _
    simp only [hz]; by_cases ht:u'=a
    · simp only [drow,dcol,t,ht,true_and,and_true, ↓reduceIte,base_price,one_mul]; rw [rowC,Finset.mul_sum,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw[sum_eq_single c]; simp only [↓reduceIte]; rw [Finset.mul_sum,Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [sum_eq_single b]; simp only [↓reduceIte]; change (M i j * Xc c b) * _= _; ring
      · intro x _ hx; rw [if_neg hx]; simp
      · simp
      · intro x _ hx; simp [hx]
      simp
    simp only [t,drow,dcol,ht,false_and,if_false,zero_mul,mul_zero,sum_const_zero]
lemma auditor (p:Pol d)(h0:reduceEq p=0): vitality a v b c f g h X d p=0 ∧ goldF a v b c f g h X d p=0:=by
    unfold vitality goldF; simp only [LinearMap.comp_apply,h0,map_zero]; exact ⟨trivial,trivial⟩
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.mixedY
