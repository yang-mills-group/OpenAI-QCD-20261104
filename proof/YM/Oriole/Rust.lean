import YM.Oriole.Gay
/-! Signed cell touch. payM retained in Pin filters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
variable (p q:Multi d)(D:CensusA d)(s:Signed)(w:EuPin)(B:Bundle)(hw:w.Lifts s)
local notation "F"=>Fiber
local notation "C"=> UV.turned (d:=d) w B
include hw
lemma plucksL : prism a b (hem s p) q ((C).transpose*D)=(((marked s p:ℂ) • B).transpose* prism a b p q D):=by
     ext i j; change _= _; unfold prism; rw [Matrix.of_apply,Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single p]; rw [Matrix.mul_apply]; apply sum_congr rfl; intro k _; rw [sum_eq_single a]; rw [Matrix.transpose_apply,UV.turned,Matrix.of_apply,if_pos rfl,readHem s _ _ hw,if_pos rfl]; rfl
     · intro x _ h; simp [UV.turned,h,Matrix.transpose]
     · simp
     · intro t _ h; have he:hem s t ≠ hem s p:= fun hz=> h ((Hem s _).injective (show Hem s d t=Hem s d p from hz)); refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>?_ ; rw [Matrix.transpose_apply, UV.turned, Matrix.of_apply]; split <;> first|(rw [readHem s _ _ hw,if_neg he]; simp)|(rw [zero_mul])
     simp
lemma plucksR : prism a b p (hem s q) (D*C)=prism a b p q D*((marked s q:ℂ) • B):=by
     ext i j; unfold prism; rw [Matrix.of_apply,Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single q]; rw [Matrix.mul_apply]; apply sum_congr rfl; intro k _; rw [sum_eq_single b]; rw [UV.turned,Matrix.of_apply,if_pos rfl,readHem s _ _ hw,if_pos rfl]; rfl
     · intro x _ h; simp [UV.turned,h]
     · simp
     · intro t _ h; have he:hem s t ≠ hem s q:= fun hz=> h ((Hem s _).injective (show Hem s d t=Hem s d q from hz)); refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>?_ ; rw [UV.turned, Matrix.of_apply]; split <;> first|(rw [readHem s _ _ hw,if_neg he]; simp)|(rw [mul_zero])
     simp
local notation "u"=> w.matrix.val
set_option quotPrecheck false
local notation "v"=> w.matrix⁻¹.val
local notation "X"=> (wave v)
local notation "Y"=> (wave (u).transpose)
omit hw
noncomputable def tintP (w:EuPin)(D:CensusA d):CensusA d:= (UV.turned w (wave w.matrix.val.transpose)).transpose * (D * UV.turned w (wave w.matrix⁻¹.val))
include hw
lemma plumbs : prism a b (hem s p) (hem s q) (tintP w D)= ((marked s p*marked s q:ℝ):ℂ) • (wave u * prism a b p q D * X) :=by
     unfold tintP; rw [plucksL a b p (hem s q) _ s w Y hw,plucksR a b p q D s w X hw,Matrix.transpose_smul]; rw [wave_tr,Matrix.transpose_transpose,Matrix.smul_mul,Matrix.mul_smul,Complex.ofReal_mul,mul_smul,mul_assoc,Matrix.mul_smul] -- Yt=u
lemma portico : assay a b (hem s p) (hem s q) (tintP w D)= Stew.gold ((((marked s p * marked s q:ℝ):ℂ)) • (wave u * prism a b p q D * X)):=by unfold assay; rw[plumbs a b p q D s w hw]
omit hw
lemma giltP(c:ℂ)(T':Bundle): Stew.gold (c • T')= c • Stew.gold T':=rfl
lemma giltA(c:ℂ) : assay a b p q (c • D)=c • assay a b p q D:= rfl
include hw
lemma pockets (h:jcoat D∈labels d): assay a b (hem s p) (hem s q) (tintP w D) = ((marked s p * marked s q:ℝ):ℂ) • (u * assay a b p q D * v):=by rw [portico a b p q D s w hw, king a b p q D h,wave_mul,wave_mul,giltP,Stew.leafy]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.pockets
