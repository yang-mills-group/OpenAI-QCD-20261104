import YM.Oriole.Rhea
import YM.Oriole.Merit
import YM.Massive.Hawser.Holy
/- UV shape exactly, incl before volumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b: Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve
variable (s:Signed)(w:EuPin)(hw:w.Lifts s)
variable (P Q:Multi d)(M:Spike)
private lemma frameN (p q: Flavor 6)(x y:Multi d) (F:Bundle) : prism a b P Q (fieldB p q x y F)= if P=x∧Q=y∧a=p∧b=q then F else 0:=by
     ext i j; change fieldB p q x y F ((P,i),a) ((Q,j),b)=_; rw[fieldK]; simp only ; split <;> rename_i ht; · obtain ⟨rfl,rfl,rfl,rfl⟩:= ht; simp;
     rw[if_neg (by tauto)]; rfl
include hw
lemma acclaim : pinAct w (bilinear a b M P Q)= ((marked s P * marked s Q:ℝ):ℂ) • bilinear a b (conjug w M) (hem s P) (hem s Q):=by
      let F:=fieldB a b P Q (wave M); let D:=fieldB a b (hem s P) (hem s Q) (wave (conjug w M)); let z:ℂ:= ↑(marked s P * marked s Q)
      rw [←j_stard,turning,←j_stard,← map_smul]; apply congr_arg
      change tintP w F=z • D; ext ⟨⟨p,i⟩,a'⟩ ⟨⟨q,j⟩,b'⟩; obtain ⟨p,rfl⟩:= (Hem s d).surjective p; obtain ⟨q,rfl⟩:= (Hem s d).surjective q
      suffices h: prism a' b' (hem s p) (hem s q) (tintP w F)=z • prism a' b' (hem s p) (hem s q) D from congr_fun (congr_fun h i) j
      rw[plumbs a' b' p q F s w hw]; unfold F D; rw[frameN,frameN]; by_cases h:p=P∧q=Q∧a'=a∧b'=b
      · obtain ⟨rfl,rfl,rfl,rfl⟩:=h; simp only [true_and,and_true,↓reduceIte]; rw [wave_mul,wave_mul]; rfl
      have ht:¬(hem s p=hem s P ∧ hem s q=hem s Q ∧ a'=a∧ b'=b):= fun h₁=> h ⟨(Hem s d).injective (show Hem s d p=Hem s d P from h₁.1), (Hem s d).injective (show Hem s d q=Hem s d Q from h₁.2.1),h₁.2.2⟩
      rw [if_neg h,if_neg ht,mul_zero, zero_mul, smul_zero,smul_zero]
omit hw
lemma blitheP : Wings g (flame a b g 8 (by omega)).val:=by
      intro w s h z hx; change pinAct w (bilinear a b (pulp g) 0 0)= _; rw [acclaim a b s w h,hem_ground,marked_root,hx,nourish]; simp only [one_mul,Complex.ofReal_one,one_smul]; rfl
lemma blazing(t:Bool) : Wings g (arbor a b g t).val:=by
      intro w s hw z h; rw [arbola,map_sum]
      let A(u:Axis):= bilinear a b (claw g u) (one_jet t u) (one_jet (!t) u)
      have he(i:Axis):pinAct w (A i)=z • A (s.perm i):=by
            unfold A; rw [acclaim a b s w hw,claw_pin g s w i hw z h,nourish]
            let x:ℂ:= signT s i; have hX:x*x=1:=by unfold x; rw[← Complex.ofReal_mul,sign_sq,Complex.ofReal_one]
            rw [show hem s (one_jet t i)=one_jet t (s.perm i) from (by cases t <;> simp[one_jet,hem_first,hem_ground]),show hem s (one_jet (!t) i)=one_jet (!t) (s.perm i) from (by cases t <;> simp[one_jet,hem_first,hem_ground]), smul_smul]; rw [show (↑(marked s (one_jet t i)*marked s (one_jet (!t) i)):ℂ)= x from (by cases t<;>simp [one_jet,marked_root,vital,x])]; rw[show x*((signT s i:ℂ)*z)= z from ((mul_assoc ..).symm.trans (by rw [show (signT s i:ℂ)=x from rfl,hX,one_mul]))]
      change ∑ i:Axis,pinAct w (A i)= z • ∑ i:Axis,A i; simp_rw[he]; rw [← Finset.smul_sum, Equiv.sum_comp s.perm]
lemma flareC (t:Bool): CharmC a b (arbor a b g t).val:=by
      intro u; rw [arbola,map_sum]; simp_rw [fun p q M => (charm (d:=8) a b p q M u)]; rw [← Finset.smul_sum] -- craft syntax
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.acclaim
#print axioms YM.Massive.Oriole.blazing
#print axioms YM.Massive.Oriole.blitheP
#print axioms YM.Massive.Oriole.flareC
