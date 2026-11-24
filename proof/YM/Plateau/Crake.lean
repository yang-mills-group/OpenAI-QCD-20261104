import YM.Plateau.Curio
import YM.Plateau.Hero
/- Label axis signs. All exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b: Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve UV.Free Clifford
variable (p q:Multi d)(s:Signed)(i j:Axis)(Y:RawSym)
local notation "P★"=>pulp g
lemma jseal : gamma i * (star P★)* gamma i=(-poli g) • P★:=by
    cases g; · simp[poli,pulp]
    rw[show (pulp true)=g5 from rfl,g5_star,Lat.five]; simp[poli,Matrix.neg_mul,Matrix.mul_assoc]
local notation "Θ"=>chargeMatrix
lemma cone : -(Θ* (P★).transpose * Θ)=P★:=by
    cases g; · change -(Θ* (1:Spike).transpose*Θ)=(1:Spike); rw[Matrix.transpose_one,mul_one,charge_sq,neg_neg]
    change -(Θ*g5.transpose*Θ)=g5; rw [transpose_five,← fiveC,mul_assoc,charge_sq,mul_neg,mul_one,neg_neg]
lemma yaw(k:ℕ)(h:6≤k): Y.adj k i (flame a b g k h)=(-poli g) • flame b a g k h:=by apply Subtype.ext; rw [RawSym.adjActs]; change UV.adj i (bilinear _ _ _ _ _) =_; rw[youth, marked_root,jseal,nourish]; rw[mul_one,Complex.ofReal_one,one_smul]; rfl
lemma woke(k:ℕ)(h:6≤k):Y.charge k (flame a b g k h)=flame b a g k h:=by apply Subtype.ext; rw [RawSym.chargeActs]; change UV.chargeAct (bilinear _ _ _ _ _) =_; rw[breeze,cone]; rfl
local notation "A" p:arg=> claw g p
lemma cope(s:Axis) : -(Θ*(claw g s).transpose * Θ)= poli g • claw g s:=by
    cases g
    · simp only[claw,pulp,Bool.false_eq_true,↓reduceIte,poli,mul_one,neg_one_smul]; rw [show chargeMatrix * (gamma s).transpose= -(gamma s*chargeMatrix) from ?_,neg_mul, mul_assoc,charge_sq,mul_neg,mul_one,neg_neg]; rw [transC,neg_neg]
    simp only[claw,pulp,poli,↓reduceIte,one_smul,Matrix.transpose_mul,transpose_five,← Matrix.mul_assoc, ← fiveC]; rw [mul_assoc g5, show C * (gamma s).transpose= -(gamma s*Θ) from ?_]; rw [mul_neg,neg_mul,mul_assoc g5,mul_assoc (gamma s),charge_sq,mul_neg,mul_one,mul_neg, Lat.five,neg_neg] -- inspect
    rw [transC,neg_neg]
lemma rayU(t:Bool): Y.charge 8 (arbor a b g t) = poli g • arbor b a g (!t):=by
    apply Subtype.ext; rw [Y.chargeActs]; change chargeAct _= (poli g) • (arbor b a g _).val; rw [arbola,arbola,map_sum]; simp_rw [breeze,cope,nourish,Bool.not_not]; rw [← smul_sum]
local notation "z"=>((-1:ℂ))
lemma planR : (↑(signT (Signed.mirror i) j):ℂ) • (gamma i * star (claw g j) * gamma i)= z • (claw g j):=by
    cases g
    · simp only[claw,pulp,Bool.false_eq_true,↓reduceIte,mul_one,gamma_star,neg_one_smul]
      by_cases hi:i=j; subst i; rw [Lat.gamma_sq,one_mul]; simp [signT,Signed.mirror]
      rw [clifford hi, neg_mul, Matrix.mul_assoc, Lat.gamma_sq,mul_one]; simp [signT,Signed.mirror,hi]
    simp only[claw,pulp,↓reduceIte,neg_one_smul,star_mul,gamma_star,g5_star]; by_cases hi:i=j
    · subst i; simp [Matrix.mul_assoc,signT,Signed.mirror]; -- gamma square
    rw [show gamma i*(g5*gamma j)*gamma i= -(gamma j*g5) from ?_]; simp [signT,Signed.mirror,hi]; rw [← Matrix.mul_assoc, Lat.five,neg_mul,Matrix.mul_assoc,clifford hi,mul_neg,neg_neg,mul_assoc g5, Matrix.mul_assoc (gamma j),Lat.gamma_sq, mul_one, Lat.five,neg_neg] -- orientation Lat.five i actual read
lemma riseQ(t:Bool):Y.adj 8 i (arbor a b g t)= - arbor b a g (!t):=by
    apply Subtype.ext; rw[Y.adjActs]; change UV.adj i _= -(arbor _ _ _ _).val; rw [arbola,arbola,map_sum,← Finset.sum_neg_distrib]; refine sum_congr rfl fun j _=>?_; rw [youth]; let s:=Signed.mirror i; have he:(↑(marked s (one_jet (!t) j)*marked s (one_jet t j)):ℂ)=(↑(signT (Signed.mirror i) j):ℂ):=by cases t<;>simp [s,one_jet,vital]; -- use nourish simplify
    rw [he,← nourish, planR, nourish,Bool.not_not t]; exact neg_one_smul ℂ (bilinear b a (claw g j) (one_jet (!t) j) (one_jet t j))
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.rayU
#print axioms YM.Massive.Oriole.planR
#print axioms YM.Massive.Oriole.woke
#print axioms YM.Massive.Oriole.yaw
#print axioms YM.Massive.Oriole.riseQ
