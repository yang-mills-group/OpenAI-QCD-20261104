import YM.Oriole.Soot
import YM.Oriole.Eider
import YM.Massive.Glint.Air
/-! fourth-order kinetic momentum at birth.Pry. Flavor-off/i. charge orientation scalars not threshold-dependent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "T"=> Lat.Fiber
local notation "G"=> pulp g
local notation "A"=> wave (claw g 0)
local notation "C"=> wave (pulp g)
local notation "V"=> wave (gamma 0)
open QCD.Entr.Goals
local notation "I"=> (0: Multi 8)
local notation "L"=> UV.first 0
lemma prismL (X Y: CensusA 8)(z:ℂ)(i j: Multi 8): Oriole.prism a b i j (X+z • Y)=Oriole.prism a b i j X+ z • Oriole.prism a b i j Y:=rfl
noncomputable def qp (a b:Flavor 6)(i j:Multi d) : CensusA d→ₗ[ℂ]Bundle:={toFun:=Oriole.prism a b i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
lemma pod(t s:Bool): qp a b (one_jet t 0) (one_jet (!t) 0) (juncoat (arbor a b g s).val)=if t=s then wave (claw g 0) else 0:=by
    rw [arbola a b g s]; simp_rw[← j_stard, map_sum,j_coat]; ext i j; rw [Matrix.sum_apply]; cases s <;> cases t
    all_goals first| (solve| simp [one_jet,qp,Oriole.prism,fieldK, Matrix.of_apply,first_eq,(highV 0),Ne.symm (highV 0)]) -- check
lemma Casing (p q r:ℂ)(t:Bool): qp a b (one_jet t 0) (one_jet (!t) 0) (juncoat (p • (flame a b g 8 (by decide)).val+q • (arbor a b g true).val+r • (arbor a b g false).val))=(if t then q else r) • A:=by
     simp_rw [map_add,map_smul,pod]; rw [show qp a b _ _ (juncoat ((flame a b g 8 (by decide)).val))=0 from ?_,smul_zero]; cases t <;> simp
     change qp _ _ _ _ (juncoat (UV.bilinear _ _ _ _ _))=_; rw [← j_stard,j_coat]; ext i j; simp only [qp,LinearMap.coe_mk,AddHom.coe_mk,Oriole.prism,Matrix.of_apply,fieldK]; cases t <;> simp [one_jet, highV]
variable (P Y: Density c 6)
local notation "Bu"=> Stiffness.body P 1
open TorusPCAC.Ward QCD.Grass.Ward
open QCD.Cove
noncomputable def rayC (P:Density c 6)(a:Flavor 6): Sheet c:= (Stiffness.body P 1)⁻¹ • piece a a (traceP (P 1))
lemma lightR (x: Grid c→EvenA c 6): rayC (Cove.light _ ∘ x) a= QCD.High.PrismT.fumes a (x 1):=by
     ext i j; simp only [rayC,Matrix.smul_apply]; let p:= (Cove.light _ ∘ x); rw [← Massive.Reading.quadr]; change (Stiffness.body p 1)⁻¹* _= _ / _; rw[div_eq_mul_inv,mul_comm]; rfl
lemma ζz (x:ℂ)(hx:x≠0): rayC (x • P) a= rayC P a:=by
     have hf:Stiffness.body (x • P) 1=x*Stiffness.body P 1:= map_smul (coef ∅) _ _
     have h:traceP ((x • P) 1)= x • traceP (P 1):=by ext i j; simp [traceP]
     unfold rayC; rw[h,hf,show piece a a (x • traceP (P 1))= x • piece a a (traceP (P 1)) from rfl,smul_smul,mul_inv_rev,mul_assoc,inv_mul_cancel₀ hx,mul_one]
lemma hewn (hp:Plus (P 1))(hz:IsUnit (P 1))(hy:coef ∅ (Y 1)=0) : uncoat (Canvas.foil P Y 1)= - Bu⁻¹ • traceP (Y 1):=by
      have he:Y 1=P 1*Canvas.foil P Y 1:= (Ring.mul_inverse_cancel_left _ _ hz).symm
      let Z:= Canvas.foil P Y 1; let v:=Stiffness.body P 1; have hQ:v≠0:=zeroR_unit (P 1) hz
      have ht : TorusPCAC.Ward.zeroR Z=0:=by apply (mul_eq_zero.mp (?_ : v* TorusPCAC.Ward.zeroR Z=0)).resolve_left hQ; rw [show v* TorusPCAC.Ward.zeroR Z= _ from (TorusPCAC.Ward.zeroR_mul ..).symm,← he]; exact hy
      nth_rw 1 [he] -- Y 1 def? occurrence
      ext i j; have hv: two (P 1 * Z) (Sum.inl j) (Sum.inr i)= v*two Z (Sum.inl j) (Sum.inr i):=by rw [two_mul_form _ _ Z hp,ht,mul_zero,zero_add]; rfl
      change - - (two _ _ _)= - v⁻¹ * (-two _ _ _); rw[hv]; field_simp; rfl
variable (s:Bool)(M:Spike)
lemma localB(i j: Modes c 6): PCAC.localF (0:Site c) M a b i j= if i.1.1=0∧ i.2=a∧j.1.1=0∧j.2=b then wave M i.1.2 j.1.2 else 0:=by
      obtain ⟨⟨i,x⟩,p⟩:=i; obtain ⟨⟨j,y⟩,q⟩:=j; rw [PCAC.localF,zleft]; change (if i=0 then (if i=j then wave M x y else (0:ℂ))*(if p=a∧q=b then 1 else 0) else 0)= (if i=0∧p=a∧j=0∧q=b then wave M x y else 0); split_ifs <;> simp_all
lemma LocalH (v:Sour (Modes c 6))(p q:Site c): QCD.Run.cell (piece a b (localF (0:Site c) M a b*v)) p q= if p=0 then wave M* QCD.Run.cell (piece b b v) 0 q else 0:=by
      ext i j; change (localF (0:Site c) M a b*v) ((p,i),a) ((q,j),b) = _; rw [Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type]; simp_rw [localB]; split
      next ht=> subst p; rw [sum_eq_single (0:Site c)]; simp [ite_mul]; rw [Matrix.mul_apply]; rfl; intro i _ h; simp [h]; simp
      next ht=> simp [ht]
lemma LocalJ (v:Sour (Modes c 6))(p q:Site c): QCD.Run.cell (piece a b (v*localF (0:Site c) M a b)) p q= if q=0 then QCD.Run.cell (piece a a v) p 0 * wave M else 0:=by
      ext i j; change (v*localF (0:Site c) M a b) ((p,i),a) ((q,j),b) = _; rw [Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type]; simp_rw [localB]; split
      next ht=> subst q; rw [sum_eq_single (0:Site c)]; simp [mul_ite]; rw [Matrix.mul_apply]; rfl; intro i _ h; simp [h]; simp
      next ht=>simp[ht]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.hewn
#print axioms YM.Massive.Oriole.Casing
