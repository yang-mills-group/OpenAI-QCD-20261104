import YM.Tawny.Iona
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Carnal
open Rays
variable (i j k l:Axis)(e:ℂ)(M:Spike)(p q:Multi d)(hp:spinWeight p+spinWeight q≤d)
noncomputable abbrev solstice(a:Flavor 6)(M: Spike)(p q:Multi d)(hp:spinWeight p+spinWeight q ≤ d): Label d:= satin a a p q M hp
local notation "J"=> solstice a M p q hp
include hp
lemma flora :Quiet (J).val:=by -- macro
     constructor
     · change parityAct (bilinear _ _ _ _ _)=bilinear _ _ _ _ _; unfold parityAct bilinear; simp_rw [TensorProduct.map_tmul,LinearMap.id_apply, AlgHom.toLinearMap_apply, map_sum,map_smul,map_mul,psi,bar,Grass.grade_atom,neg_mul_neg]
     intro w; change flavorAct w (bilinear a a M p q)= _; rw [charm]; rw [paidM,(w a).property.1,one_smul]; rfl
omit hp
noncomputable def mixed : Label d:= solstice a M p q hp+ solstice a (truck M) q p ((add_comm (spinWeight q) (spinWeight p)) ▸ hp)
include hp
local notation "D"=>mixed a M p q hp
lemma munity : D ∈ Pe d:=by
    obtain ⟨h,hY⟩:= flora a M p q hp; let v:= solstice a (truck M) q p (by omega); change (J+v)∈ Pe _; obtain ⟨h1,h2⟩:=flora a (truck M) q p (by omega); have hz: chargeAct (J).val=v.val:= breeze ..
    refine ⟨⟨?_,fun i=>?_⟩,?_⟩
    · change parityAct ((J).val+(_ :Label d).val)=_; rw [map_add,h,h1]; rfl
    · change flavorAct _ ((J).val+(_ : Label d).val)=_; rw [map_add,hY,h2]; rfl
    change chargeAct ((J).val+v.val)= _; rw [map_add,← hz,inv_c, hz,add_comm]; rfl
lemma push_neg : (solstice a (-M) p q hp)= -J:=by apply Subtype.ext; change bilinear _ _ _ _ _= -_; rw [← neg_one_smul ℂ M,nourish]; exact neg_one_smul ℂ (bilinear a a M p q)
variable (s:Signed)(w:EuPin)(hw:w.Lifts s)(z:ℂ)(B: Spike)
include hw
lemma ringM(h:conjug w M=z • B) : pinAct w ((J).val)=(((↑(marked s p*marked s q):ℂ))*z) • (solstice a B (hem s p) (hem s q) (by rwa [borderBuck,borderBuck])).val:=by
     change pinAct w (bilinear _ _ _ _ _)=_; rw [acclaim a a s w hw,h,nourish, smul_smul]; rfl
lemma paidM(h:conjug w M=z • B)(he:conjug w (truck M)=z • truck B): pinAct w ((D).val)=(((↑(marked s p * marked s q):ℂ))*z) • (mixed a B (hem s p) (hem s q) (by rwa [borderBuck,borderBuck])).val:=by
     unfold mixed; simp only[Submodule.coe_add,Submodule.coe_smul]; rw[map_add]; rw [ringM a M p q hp s w hw z B h]; rw[ringM a (truck M) q p _ s w hw z (truck B) he, mul_comm (marked s q), ← smul_add]
omit hw hp
-- grade1 S
local notation "U"=> (0:Multi 8)
local notation "L" i:arg=> UV.first i
noncomputable def alter (a:Flavor 6)(i j:Axis): Label 8:= mixed a (gamma i) 0 (L j) (by rw[cost_root,juicy])
local notation "A"=>alter a
lemma amt : (alter a i j).val=UV.spinStressUnsymm a i j:=by
     unfold alter mixed; rw [antiT, push_neg]; change bilinear _ _ _ _ _ + -_= _; rw[← sub_eq_add_neg]; rfl
include hw
lemma scopeY: pinAct w ((alter a i j).val)=((↑(signT s i):ℂ)*(signT s j:ℂ)) • (alter a (s.perm i) (s.perm j)).val:=by
      have h:= E_sigma s w hw i; have hp:= paidM a (gamma i) (0:Multi 8) (L j) (by rw[cost_root,juicy]) s w hw _ _ h (by rw[antiT,antiT, conjug,mul_neg, neg_mul]; change -(conjug w _)=_; rw[h,smul_neg]); simp_rw [marked_root, vital,one_mul, hem_ground,hem_first,mul_comm (signT s j:ℂ)] at hp; exact hp
omit hw
local notation "P"=>RawTensor e 8
noncomputable def treeT (e:ℂ)(h:e*e=1) (v: Flavor 6):RawTensor e 8:= stoke (fun p=>alter v p.1 p.2+e • alter v p.2 p.1) e (by
      intro i j; exact Submodule.add_mem _ (munity v (gamma _) _ _ _) (Submodule.smul_mem _ _ (munity ..))) (by intro s w hw i j; simp only[Submodule.coe_add,Submodule.coe_smul,map_add,map_smul,scopeY v _ _ s w hw, mul_comm (↑(signT s j):ℂ) (↑(signT s i):ℂ)]; rw[smul_comm e,← smul_add]) (by intro i j; simp only; rw [smul_add, smul_smul,h,one_smul,add_comm])
noncomputable def sunS (a:Flavor 6):RawTensor 1 8:= treeT 1 (mul_one _) a
noncomputable def windS(a:Flavor 6):RawTensor (-1) 8:= treeT (-1) (by norm_num) a
noncomputable def wingS (a:Flavor 6):RawTensor 1 8:= diagT 1 (sunS a)
noncomputable def scalarS (a:Flavor 6):RawTensor 1 8:= stoke (fun p=> if p.1=p.2 then solstice a 1 U U (by rw [cost_root]; decide) else 0) 1 (by
       intro i j; split; · refine ⟨flora ..,?_⟩; rw [show ∀(h:spinWeight U+spinWeight U ≤ 8),chargeAct (solstice a 1 U U h).val=(solstice a 1 U U h).val from ?_]; intro h; change chargeAct (bilinear _ _ _ _ _)=_; rw [breeze, show -(chargeMatrix*(1:Spike).transpose*chargeMatrix)=(1:Spike) from truck_one]; rfl
       exact Submodule.zero_mem _) (by
       intro s w hw i j; simp only [s.perm.injective.eq_iff]; split <;> rename_i h; · subst j; change pinAct w (bilinear _ _ _ _ _)=_; rw [acclaim a a s w hw U U, marked_root,mul_one,Complex.ofReal_one,one_smul, hem_ground, show conjug w (1:Spike)=1 from by rw [conjug,mul_one, inv1],← Complex.ofReal_mul, UV.sign_sq,Complex.ofReal_one,one_smul]; rfl
       simp) (by intro i j; simp [eq_comm])
noncomputable def traceT (a:Flavor 6):RawTensor 1 8:= stoke (fun p=> if p.1=p.2 then (∑ i:Axis,alter a i i) else 0) 1 (by intro i j; split; exact Submodule.sum_mem _ fun i _=>munity a (gamma i) _ _ _; exact Submodule.zero_mem _) (by
       intro s w h i j; simp only[s.perm.injective.eq_iff]; split <;> rename_i hp
       · subst j; simp_rw[AddSubmonoidClass.coe_finsetSum,map_sum,scopeY a _ _ s w h,← Complex.ofReal_mul, UV.sign_sq,Complex.ofReal_one,one_smul]; exact Equiv.sum_comp s.perm (fun i=>(alter a i i).val)
       simp) (by intro i j; simp [eq_comm])
end Carnal
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Carnal.amt
#print axioms YM.Massive.Tawny.Cast.Carnal.traceT
