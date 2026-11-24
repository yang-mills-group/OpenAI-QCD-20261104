import YM.Tawny.Zinc
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Zinc
open scoped Kronecker
open Rays StressFlux.Offer
open StressFlux (pair pairDeriv curled curl0 curl1)
variable (i j k l:Axis)(B: Spike)(J:Labels.Jet su)
local notation "D"=>10
local notation "U"=> (0:Multi 10)
local notation "F"=> Labels.axes su 0
local notation "X"=> SpinPol D
local notation "K" => PowerPair D
local notation "Q"=> weave a B i j
local notation "Y"=> youthL a i j B
local notation "Y1"=> youthL a i j (truck B)
local notation "Z"=> RawVec 10
private lemma pLight(A C:CensusA D)(h:∀ a b:Flavor 6,∀ i j:Multi D,Oriole.prism a b i j A=Oriole.prism a b i j C):A=C:=by ext ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩; exact congr_fun (congr_fun (h a b p q) i) j
variable (s:Signed)(w:EuPin)(hw:w.Lifts s)(u:su.Color)(z:ℂ)
local notation "V"=> StressFlux.shifted s J
lemma V_neut : chargeAct Y= -Y1:=by
     apply Poised.Display.distinct; intro J; rw [plum,yMobi,map_neg,yMobi,dance,← map_neg]; apply congr_arg
     apply pLight; intro u' v' p q; let α:= Q (Labels.changedJet (fun _=>recolor) J 0); change gravel u' v' p q (dam α)= _; rw [rubDam]; unfold α weave; change -(_*(Oriole.prism v' u' q p (yard a _)).transpose*_) = gravel u' v' p q (-yard a (whirl _ _)); rw [yield_p,map_neg]; change _= -Oriole.prism u' v' p q (yard a _); rw[yield_p]; split <;> rename_i h
     · obtain ⟨hq,hP,hv,hu⟩:= h; subst q p; subst v'; subst u'; simp only[↓reduceIte,and_true]; unfold whirl; rw [show curl0 i j (Labels.changedJet _ J 0)=reflectColor (curl0 i j (J 0)) from Perla.curl_change i j (J 0), BendR.arch]
     rw [if_neg (by tauto)]; rw [Matrix.transpose_zero,mul_zero,zero_mul]
lemma scaleY: youthL a i j (z • B)=z • Y:=by
    apply Poised.Display.distinct; intro J; rw [yMobi,map_smul,yMobi]; unfold weave whirl; rw [Matrix.smul_kronecker, map_smul,map_smul]
include hw
lemma moveX : pinAct w Y=( (signT s i:ℂ)*(signT s j:ℂ)) • youthL a (s.perm i) (s.perm j) (conjug w B):=by
    let r:ℂ:=(signT s i:ℂ)*(signT s j:ℂ); apply Poised.Display.distinct; intro J; rw[scored _ J w s hw,map_smul,yMobi,yMobi,pinoy,← map_smul]; apply congr_arg
    apply pLight; intro u v p q; obtain ⟨p,rfl⟩:= (Hem s D).surjective p; obtain ⟨q,rfl⟩:=(Hem s D).surjective q; change Oriole.prism u v (hem s p) (hem s q) (tintP _ _)=gravel u v (hem s p) (hem s q) (r • weave a (conjug w B) _ _ _); rw [plumbs u v p q _ _ _ hw,map_smul]; change _ = r • Oriole.prism u v (hem s p) (hem s q) _; unfold weave; rw[yield_p,yield_p]; have ht(p:Multi D): hem s p=0 ↔ p=0:= by calc
               _ ↔ Hem s D p=Hem s D 0 :=by rw[show Hem s D 0 = (0:Multi D) from hem_ground ..]; rfl
               _ ↔ _:= (Hem s D).injective.eq_iff
                                                                                                                              --
    by_cases h:p=0∧q=0∧u=a∧v=a
    · rw [if_pos h,if_pos (by rw [ht,ht]; exact h)]; rw [h.1,h.2.1,marked_root,one_mul,Complex.ofReal_one,one_smul]; unfold whirl; rw[StressFlux.curl0_shifted]; let C:=curl0 (s.perm i) (s.perm j) (J 0); rw[show ore ((_ :ℝ) • C)=r • ore C from ?_]; rw [Matrix.kronecker_smul]; exact poker w r C B
      unfold BendR.ore r; rw[← Complex.ofReal_mul]; change BendR.ore (_ • C)=_; exact su.colorMat.map_smul _ C
    rw[if_neg h,if_neg (by rw[ht,ht]; exact h),mul_zero,zero_mul,smul_zero,smul_zero]
omit hw
lemma coalP : med a i j (gamma k)∈Pe D:=by
    refine ⟨(rubyY a i j (gamma k)).2,?_⟩; change chargeAct (youthL ..)=_; rw[V_neut,antiT,←neg_one_smul ℂ (gamma k),scaleY]; exact Eq.trans (congr_arg Neg.neg (neg_one_smul ℂ (youthL a i j (gamma k)))) (neg_neg _)
noncomputable def starV (a:Flavor 6):Z:=stick (fun i=>∑ j:Axis, med a i j (gamma j)) (fun i=> Submodule.sum_mem _ (fun j _=>coalP ..)) (by
     intro s w h i; simp_rw[AddSubmonoidClass.coe_finsetSum,map_sum]; have he(j:Axis) :pinAct w ((med a i j (gamma j)).val)=(↑(signT s i):ℂ) • (med a (s.perm i) (s.perm j) (gamma (s.perm j))).val:=by
          change pinAct w (youthL _ _ _ _)=_; rw [moveX a i j _ _ _ h,E_sigma s w h,scaleY,smul_smul,mul_assoc,← Complex.ofReal_mul (signT s j), UV.sign_sq,Complex.ofReal_one,mul_one]; rfl
     simp_rw [he,← smul_sum]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun j=>(med a (s.perm i) j (gamma j)).val)))
lemma tocP:fog Y=0:=by unfold youthL; rw [map_sum]; simp_rw [mintFog, sum_const_zero]
lemma skinP : skin J Y = Q (J 0):=by unfold skin; rw[LinearMap.comp_apply,yMobi,coat_known]
lemma skinP0:skin 0 Y=0:=by rw[skinP]; unfold weave whirl BendR.ore; rw[show (0:Labels.Jet su) 0=0 from rfl,map_zero,map_zero]; change yard a (B⊗ₖ (0:Mat))=0; rw[show B⊗ₖ (0:Mat)=0 from by ext; simp,map_zero]
end Zinc
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Zinc.starV
