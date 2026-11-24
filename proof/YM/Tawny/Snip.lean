import YM.Tawny.Cast
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
noncomputable def flair (l:List Axis): Spike:= (l.map gamma).prod
noncomputable def visa (l:List Axis)(s:Signed):ℂ:= (l.map fun i=>((signT s i:ℝ):ℂ)).prod
variable (p q:Multi d)(w:EuPin)(z:ℂ)(s:Signed)(hw:w.Lifts s)(e:ℂ)(S U:Spike)
local notation "Z"=> RawTensor e d
lemma truck_v (α:ℂ) : truck (α • S)= α • truck S:=by rw[truck,Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,← smul_neg]
lemma truck_blank:truck (0:Spike)=0:=by simp [truck]
lemma truck_one:truck (1:Spike)=1:=by rw [truck, Matrix.transpose_one,mul_one,Clifford.charge_sq,neg_neg]
lemma antiT(i:Axis): truck (gamma i)=-gamma i:=by
    rw [truck, show chargeMatrix * (gamma i).transpose= -(gamma i* Clifford.C) from ?_]; rw [neg_mul, mul_assoc, Clifford.charge_sq,mul_neg,mul_one,neg_neg];
    rw [Clifford.transC,neg_neg]
lemma antiMul : truck (S*U)= truck U*truck S:=by
    unfold truck; rw[Matrix.transpose_mul,neg_mul_neg]; simp only [mul_assoc]; rw [← mul_assoc chargeMatrix chargeMatrix,Clifford.charge_sq, Matrix.neg_mul,one_mul,mul_neg,mul_neg]
lemma truck_triple (i j k:Axis)(h:i≠j)(ht:k≠i)(hl:k≠j): truck (gamma i *gamma j * gamma k)= gamma i*gamma j*gamma k:=by
     rw [antiMul,antiMul,antiT,antiT,antiT,neg_mul_neg,neg_mul,← mul_assoc,clifford hl,neg_mul,neg_neg,mul_assoc _ (gamma k),clifford ht,mul_neg,←mul_assoc,clifford h.symm,neg_mul,neg_neg]
lemma truck_double (i j:Axis)(h:i≠j): truck (gamma i*gamma j)= -(gamma i*gamma j):=by rw[antiMul,antiT,antiT, neg_mul_neg, clifford h.symm]
lemma truck_invol : truck (truck S)= S:=by unfold truck; rw [Matrix.transpose_neg,Matrix.mul_neg,Matrix.neg_mul,neg_neg]; simp only [Matrix.transpose_mul,Clifford.transpose_charge,Matrix.transpose_transpose,Matrix.neg_mul,Matrix.mul_neg,neg_neg,Matrix.mul_assoc]; rw [Clifford.charge_sq, Matrix.mul_neg, mul_one,Matrix.mul_neg,Matrix.mul_neg, ← mul_assoc, Clifford.charge_sq,Matrix.neg_mul,one_mul,neg_neg]
lemma conj_s (α:ℂ) : conjug w (α • S)=α • conjug w S:=by unfold conjug; rw [Matrix.mul_smul,Matrix.smul_mul]
include hw
@[simp] lemma flair_turn(l:List Axis): conjug w (flair l)=visa l s • flair (l.map s.perm):=by
     induction l with
     | nil=> change conjug w 1=_; rw [conjug,mul_one, inv1]; simp [visa,flair]
     | cons a l h=> rw [show flair _=gamma a*flair l from by simp [flair],L_up,E_sigma s w hw,h]; simp only [List.map_cons,List.prod_cons,visa,flair,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; rw [mul_comm _ (↑(signT s a):ℂ)]
omit hw
lemma flair_b(l:List Axis): flair l∈unitary Spike:=by
     induction l with
     | nil=> exact Submonoid.one_mem _
     | cons a l h=> rw[show flair _=gamma a*flair l from by simp[flair]]; exact Submonoid.mul_mem _ ⟨by simp,by simp⟩ h
lemma vpaid(l:List Axis) : visa l s*visa l s=1:=by
    induction l with
    | nil=>simp [visa]
    | cons i l h=>
          have hp:(signT s i:ℂ)*(signT s i:ℂ)=1:=by rw [← Complex.ofReal_mul, UV.sign_sq,Complex.ofReal_one]
          rw [show visa _ s=(signT s i:ℂ)*visa l s from rfl]; calc
          _ = (((signT s i:ℂ)*(signT s i:ℂ))*(visa l s*visa l s)):=by ring
          _ = _:= by rw [hp,h,one_mul]
lemma shapeQ(l:List Axis)(he:∀ (i:Axis)(w:EuPin),w.Lifts (Signed.mirror i)→ S=visa l (Signed.mirror i) • conjug w S): ∃ z:ℂ,S= z • flair l:=by
    apply shine (flair l) S (flair_b l); intro i w h; let s:= Signed.mirror i; have ht:conjug w S= visa l s • S:= by nth_rw 2 [he i w h]; change _= visa l s • visa l s • _; rw[smul_smul,vpaid,one_smul]
    refine ⟨visa l s,?_,ht⟩; rw [flair_turn w s h]; rw [show l.map (s.perm)=l from List.map_id'' (fun i=>rfl) _] -- inspect
private lemma bill (S:Spike)(he:S∈unitary Spike):∃ i j,S i j≠0:=by
    have hP:S≠0:=fun h=> zero_ne_one (by simpa [h] using he.1 : (0:Spike)=1); contrapose! hP; ext i j; exact hP i j
noncomputable def feeP (l:List Axis): Spike→ₗ[ℂ]ℂ:=
   let h:=bill _ (flair_b l); let i:= h.choose; let j:=h.choose_spec.choose; (flair l i j)⁻¹ • (show _ from {toFun:=fun x:Spike=>x i j, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}: Spike→ₗ[ℂ]ℂ)
lemma chosen(l:List Axis): feeP l (flair l)=1:=by
    have he:= (bill _ (flair_b l)).choose_spec.choose_spec; exact inv_mul_cancel₀ he
lemma germ(l:List Axis)(h:feeP l S=0)(he:∃ z:ℂ,S=z • flair l): S=0:=by obtain ⟨z,h'⟩:=he; rw[h',map_smul,chosen,smul_eq_mul,mul_one] at h; rw [h',h,zero_smul]
-- standardized shapeQ on primal proof. charge rules direct prism equality.
variable {I:Type}(K:Signed→ I→ I)(A:Signed→ I→ℝ)(Cw:I→I)
variable (x:Steno K A Cw e d)(hd:d ≤ 10)
set_option quotPrecheck false
local notation "Aq" i:arg=>prism0 a p q (x.val i).val
include hd
open Function
lemma roleL (i:I) : truck (Aq i)= prism0 a q p (x.val i).val:=let ht:=show Meaning _ _ _ _ d _ from x.property; chargeL a _ (ht.light i) hd p q (ht.coal i)
omit hd
noncomputable def flag (s:Equiv.Perm Axis):Signed:=⟨s,fun _=> false⟩
lemma clean (P:Equiv.Perm Axis) : marked (flag P) p=1:=by simp [marked,flag,signT]
include hd
lemma roleS (i:I)(l:List Axis)(hs:∀ k:Axis, K (Signed.mirror k) i=i)(hl:∀ k:Axis, let s:=Signed.mirror k;let v:ℂ:= ↑(marked s p*marked s q); (A s i:ℂ)*visa l s=v)(ht:∀ k:Axis,(A (Signed.mirror k) i:ℂ)≠0) :∃ z:ℂ,Aq i=z • flair l:=by
     apply shapeQ; intro k w h; let s:=Signed.mirror k; have hp:=show Meaning _ _ _ _ d _ from x.property; have hz:= pinL a w s h (x.val i) (hp.light i) hd p q _ _ (hp.light (K s i)) (hp.ringo s w h i); change _= _ at hz; apply smul_right_injective _ (ht k); simp only; rw [smul_smul,hl]; rw [show K s i=i from hs k,show hem s p=p from pinHem ..,show hem s q=q from pinHem ..] at hz; exact hz
lemma roleP (i:I)(s:Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag s))(h1:A (flag s) i=1): prism0 a (hem (flag s) p) (hem (flag s) q) (x.val (K (flag s) i)).val=conjug w (Aq i):=by
     let t:=flag s; let u:=x.val i; have hp:=show Meaning _ _ _ _ d _ from x.property; have hz:=pinL a w t hw (x.val i) (hp.light i) hd p q _ _ (hp.light _) (hp.ringo _ _ hw i); change _= _ at hz; rw [show A t i=1 from h1,Complex.ofReal_one,one_smul,show marked t p=1 from clean ..,show marked t q=1 from clean .., one_mul,Complex.ofReal_one,one_smul] at hz; exact hz
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.roleS
