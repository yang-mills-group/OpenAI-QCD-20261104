import YM.Plateau.Peak
import YM.Massive.Ribbon.Graft
/-! Orientation proofs on charged cards used below. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b: Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve UV.Free
local notation "T"=> SpinMode d
variable (S:CensusA d)
section swap
variable {J:Type*}[Fintype J][DecidableEq J](X Y D:Matrix J J ℂ)
local notation "V"=> Sum.swap (α:=J) (β:=J)
lemma upward (x:Dirac J) : changeVars (Matrix.fromBlocks 0 X Y 0) x= adapter Y X (embed V x):=by
    induction x using ExteriorAlgebra.induction with
    | algebraMap c=>rw[AlgHom.commutes,AlgHom.commutes,AlgHom.commutes]
    | ι v=> rw [line_atoms (A:=Pairs J)]; simp_rw [map_sum,map_smul,embed_atom]; refine sum_congr rfl fun i _=>?_ ; rcases i with i|i
            · change _ • _= _ • adapter _ _ (bar i); rw [adapt_bar,change_atom,Fintype.sum_sum_type]; simp [bar]
            change _ • _= _ • adapter _ _ (psi i); rw [adapt_psi,change_atom,Fintype.sum_sum_type]; simp [psi]
    | add x y hx hy=> rw[map_add,map_add,map_add,hx,hy]
    | mul x y hx hy=> rw[map_mul,map_mul,map_mul,hx,hy]
lemma versa : embed V (form D)=form (-D.transpose):=by
     unfold form; simp_rw[map_sum,map_smul,map_mul,psi,bar,embed_atom]; rw [sum_comm]; apply sum_congr rfl; intro i _; refine sum_congr rfl fun j _=> ?_; rw [atom_flip (Sum.swap _) _]; simp_rw [smul_neg]; rw[Matrix.neg_apply,neg_smul]; rfl
lemma ncL: changeVars (Matrix.fromBlocks 0 X Y 0) (form D)= form (X.transpose*((-D.transpose)*Y)):=by rw [upward,versa,form_map]
lemma ntL: changeVars (Matrix.fromBlocks 0 X Y 0) (dagger (form D))= form (X.transpose*(star D*Y)):=by rw [upward]; change adapter Y X (Grass.turn _)=_; rw[turn_form,form_map]
end swap
local notation "G"=>SpinPol d
local notation "C"=>chargeMatrix
lemma ride : chargeAct (jcoat S)= jcoat ((spinTable C).transpose*((-S.transpose)*(spinTable (-C)))):=by
    change chargeAct ((1:GPol) ⊗ₜ[ℂ] (-(form S) :SpinPol d))=_; unfold chargeAct; rw [TensorProduct.map_tmul]; simp_rw[AlgHom.toLinearMap_apply,map_one,map_neg] -- danger map_neg inner?
    rw [invertC,ncL]; rfl
lemma reflects (i:Axis): adj i (jcoat S)= jcoat ((flipTable i (-(gamma i).transpose)).transpose*((star S)*flipTable i (-gamma i))):=by
    change adj i ((1:GPol) ⊗ₜ[ℂ] (-(form S):SpinPol d))=_; unfold adj; rw [TensorProduct.map_tmul,LinearMap.comp_apply,LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]; rw [show conjGPol 1=1 from map_one (MvPolynomial.map (starRingEnd ℂ)),map_one,map_neg,map_neg, ntL]; rfl
-- Turn arbitrary cell, including signed mirror. identity charge table from spinTable.
variable (p q:Multi d)
private lemma crestP (p' q':Multi d)(u v:Flavor 6)(F:Bundle):prism a b p q (fieldB u v p' q' F)= if p=p' ∧ q=q' ∧ a=u ∧ b=v then F else 0:=by
     ext i j; change fieldB u v p' q' F ((p,i),a) ((q,j),b)=_; rw[fieldK]; simp only ; split <;> rename_i ht; · obtain ⟨rfl,rfl,rfl,rfl⟩:=ht; simp
     rw[if_neg (by tauto)]; rfl
variable (X Y M: Spike)
local notation "F"=> fieldB a b p q (wave M)
lemma streamC : (F).transpose= fieldB b a q p (wave M.transpose):=by
     ext i j; rw [Matrix.transpose_apply,fieldK,fieldK]; split <;> rename_i ht; · rw [if_pos (by tauto),wave_tr]; rfl
     rw [if_neg (by tauto)]
lemma streamS : star (F)= fieldB b a q p (wave (star M)):=by
     ext i j; rw[Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,fieldK,fieldK]; split <;> rename_i ht; · rw [if_pos (by tauto),← wave_star]; rfl
     rw[star_zero,if_neg (by tauto)]
lemma waltz (s:Signed)(w:EuPin)(hw:w.Lifts s): (UV.turned w (wave X)).transpose*(F * UV.turned w (wave Y))= ((↑(marked s p *marked s q):ℂ)) • fieldB a b (hem s p) (hem s q) (wave (X.transpose*M*Y)):=by
     let U:= UV.turned (d:=d) w (wave Y); let V:= UV.turned (d:=d) w (wave X); let M':Bundle:=wave (X.transpose * M * Y); let B:= fieldB a b (hem s p) (hem s q) M'; let z:ℂ:= ↑(marked s p*marked s q); change V.transpose * (F*U)=z • B; ext ⟨⟨i,t⟩,c⟩ ⟨⟨j,u⟩,e⟩; obtain ⟨i,rfl⟩:= (Hem s d).surjective i; obtain ⟨j,rfl⟩:= (Hem s d).surjective j
     suffices h:prism c e (hem s i) (hem s j) (V.transpose *(F * U))=z • prism c e (hem s i) (hem s j) B from congr_fun (congr_fun h t) u
     unfold V U; rw [plucksL c e i (hem s j) _ s w _ hw,plucksR c e i j _ s w _ hw]; unfold B; rw[crestP,crestP]; by_cases h:i=p∧j=q∧c=a∧e=b
     · obtain ⟨rfl,rfl,rfl,rfl⟩:=h; simp only[and_true,↓reduceIte]; unfold M' z; rw[Matrix.transpose_smul,← wave_tr,_root_.mul_smul_comm,_root_.smul_mul_assoc,_root_.mul_smul_comm,smul_smul,← Matrix.mul_assoc,wave_mul,wave_mul,Complex.ofReal_mul] -- notation wave_tr direction inspect
     have hh: ¬(hem s i=hem s p∧ hem s j=hem s q∧ c=a∧e=b):= fun hK=> h ⟨(Hem s d).injective hK.1,(Hem s d).injective hK.2.1,hK.2.2⟩; rw [if_neg h,if_neg hh,zero_mul,mul_zero,smul_zero]
lemma youth(i:Axis):UV.adj i (bilinear a b M p q)= (↑(marked (Signed.mirror i) q * marked (Signed.mirror i) p):ℂ) • bilinear b a (gamma i * (star M) * gamma i) q p:=by
      obtain ⟨s,hs⟩:= EuPin.choice (Signed.mirror i); rw [←j_stard,reflects,hem_turn _ hs,hem_turn _ hs,streamS,waltz b a q p _ _ _ _ s hs,pinHem,pinHem,Matrix.transpose_neg,Matrix.transpose_transpose,neg_mul,neg_mul_neg,map_smul,j_stard]
lemma breeze:UV.chargeAct (bilinear a b M p q)=bilinear b a (- (C*M.transpose*C)) q p:=by
      rw[←j_stard,ride,streamC,neg_mul,mul_neg,under_spin,under_spin, waltz b a q p _ _ _ 1 1 ((map_one Signed.inclusionO).symm)]
      have hz(v:Multi d):marked 1 v=1:=by unfold marked; simp [show ∀ i:Axis, signT 1 i= 1 from fun _=>rfl]
      rw [hz,hz,one_mul,Complex.ofReal_one,one_smul, Clifford.transpose_charge, neg_mul,neg_mul_neg]
      rw [show hem (1:Signed) q=q from rfl,show hem (1:Signed) p=p from rfl,map_neg,j_stard,← neg_one_smul ℂ (chargeMatrix*M.transpose*chargeMatrix),Massive.Oriole.nourish]; exact (neg_one_smul ℂ _).symm

end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.breeze
#print axioms YM.Massive.Oriole.youth
