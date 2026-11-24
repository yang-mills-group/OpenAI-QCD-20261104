import YM.Tawny.Rays
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
open Rays
local notation "U"=> (0:Multi 10)
local notation "Z"=> RawVec 10
variable (x:RawVec 10)
set_option quotPrecheck false
local notation "X" i:arg=> (x.val i).val
local notation "g" p:arg q:arg i:arg=>prism0 a p q (x.val i).val
local notation "L" i:arg=> leadR i
local notation "H" i:arg j:arg=> ηR i j
variable (p q:Multi 10)(i j k l:Axis)
open StressFlux.Offer
local notation "hR" i:arg j:arg k:arg=> prism1 a U U j k (X i)
private lemma deltaG(k:Axis): (signT (Signed.mirror k) i:ℂ)≠0:=by unfold signT; split <;> norm_num
lemma gr0 : g U U i=0:=by
     obtain ⟨z,hz⟩: ∃ z:ℂ, g U U i=z • flair [i]:= roleS a U U 1 _ _ _ x (by decide) i _ (fun _=>rfl) (fun k=>by intro s v; unfold visa v; simp only [marked_root,List.map_cons,List.map_nil,List.prod_nil,List.prod_cons,one_mul,mul_one]; unfold signT; split <;> norm_num) (deltaG i) -- @? 
     have he:= roleL a U U 1 _ _ _ x (by decide) i; rw[hz]; apply negS; rw[hz,show flair [i]=gamma i from by simp[flair],truck_v,antiT,smul_neg] at he; simpa only [flair,List.map_cons,List.prod_cons,List.prod_nil,List.map_nil,mul_one] using he
lemma grL : ∃ z:ℂ, g U (L j) i=z • flair [i,j]:=by
    exact roleS a U (L j) 1 Vc signT _ x (by decide) i [i,j] (fun _=>rfl) (fun k=>by
         intro s v; simp only [v,marked_root,markedL, visa,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,one_mul,mul_one,← Complex.ofReal_mul]; rw [← mul_assoc (signT s i), UV.sign_sq,one_mul]) (deltaG i)
lemma grS : ∃ z:ℂ, g U (H j k) i=z • flair [i,j,k]:=by
    exact roleS a U (H j k) 1 Vc signT _ x (by decide) i _ (fun _=>rfl) (fun v=>by intro s V; simp only [V,marked_root,markedH, visa, List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,← Complex.ofReal_mul]; rw [← mul_assoc (signT s i), UV.sign_sq,one_mul]) (deltaG i)
lemma grP : ∃ z:ℂ, g (L j) (L k) i=z • flair [i,j,k]:=by
    exact roleS a (L j) (L k) 1 Vc signT _ x (by decide) i _ (fun _=>rfl) (fun v=>by intro s V; simp only [V,markedL, visa, List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,← Complex.ofReal_mul]; rw [← mul_assoc (signT s i), UV.sign_sq,one_mul]) (deltaG i)
lemma grX : ∃ z:ℂ,hR i j k= z • flair [i,j,k]:=by
    apply shapeQ; intro l w hw; let s:= Signed.mirror l; have hp:=show Meaning _ _ _ _ 10 _ from x.property
    have he:= pinR a w s hw (x.val i) (hp.light i) (by decide) U U j k _ (hp.light ((Vc s) i)) _ (hp.ringo _ _ hw i);
    change ((signT s i:ℂ)) • twin a a (x.val i) (hp.light i) (by decide) U U j k=_ at he
    rw [probedT _ _ _ _ _ _ (hp.light i) (by decide)]
    apply smul_right_injective _ (deltaG i l); dsimp only; rw [smul_smul]; refine he.trans ?_; rw [show visa [i,j,k] (Signed.mirror l)= (signT s i:ℂ)*((signT s j:ℂ)*(signT s k:ℂ)) from by simp only [visa,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl]; rw [show signT (Signed.mirror l) i=signT s i from rfl,← mul_assoc (↑(signT s i):ℂ),← Complex.ofReal_mul, UV.sign_sq]; simp
lemma twin0 : hR i k k=0:=by
    unfold prism1; rw [LinearMap.comp_apply,LinearMap.comp_apply,StressFlux.leg0_diag, show ray (0:Labels.Taylor su 0) (X i)=0 from ?_,map_zero,map_zero]; unfold ray; simp
lemma swapX : hR i j k= - (hR i k j):=by
    let v:= x.val i; have hp:= (show Meaning _ _ _ _ 10 _ from x.property).light i; let P:= glow v hp (by decide)
    unfold prism1; rw [LinearMap.comp_apply,LinearMap.comp_apply, LinearMap.comp_apply,LinearMap.comp_apply,glean v hp (by decide), glean v hp (by decide)]; rw [StressFlux.leg0_swap j k]; change gold2 (gravel _ _ _ _ (P (-StressFlux.leg0 k j _)))= _; rw[map_neg,map_neg,map_neg]
lemma vanishX(h:i≠j)(ht:i≠k)(hl:j≠k): hR i j k=0:=by
    have hb:=show Meaning _ _ _ _ 10 _ from x.property; let v:=x.val i; have hp:=hb.light i; have he :hR i j k= -truck (hR i j k):=by rw [probedT _ _ _ _ _ _ hp (by decide)]; exact chargeR a v hp (by decide) _ _ j k (hb.coal i)
    obtain ⟨z,hz⟩:=grX a x i j k; rw [hz] at he; apply negS; rw[hz]; have hF: flair [i,j,k]=gamma i*gamma j*gamma k:=by simp [flair,mul_assoc]
    rw [hF] at he ⊢; rw[truck_v,truck_triple i j k h ht.symm hl.symm] at he; exact he.symm
variable (P:Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag P))
include hw
lemma passP : g (hem (flag P) p) (hem (flag P) q) (P i)=conjug w (g p q i):= roleP a _ _ 1 _ signT _ x (by decide) i P w hw (by simp [flag,signT])
lemma passX : hR (P i) (P j) (P k)=conjug w (hR i j k):=by
    let s:=flag P; have ht:= show Meaning _ _ _ _ _ _ from x.property; have he:= pinR a w s hw (x.val i) (ht.light i) (by decide) U U j k _ (ht.light (P i)) _ (ht.ringo _ _ hw i); rw [hem_ground, marked_root] at he; have hb(v:Axis):signT s v=1:=by simp [s,signT,flag]
    simp only [s,signT,flag,marked_root,Complex.ofReal_mul,Complex.ofReal_one, Bool.false_eq_true, ↓reduceIte,one_mul,one_smul] at he; rw [probedT a _ _ _ _ _ (ht.light (P i)) (by decide),probedT _ _ _ _ _ _ (ht.light i) (by decide)]; exact he
omit hw
lemma tollP : g q p i=truck (g p q i):=Eq.symm (roleL a p q 1 _ signT _ x (by decide) i)
lemma diag_kill : g (L k) (L k) i=0:=by
    have he:= tollP a x (L k) (L k) i; apply negS; obtain ⟨z,hz⟩:= grP a x i k k; rw[show flair [i,k,k]=gamma i from by simp[flair]] at hz; rw [hz] at he; rw[hz]; rw[truck_v,antiT,smul_neg] at he; exact he.symm
lemma combo (hi:i≠j)(ht:i≠k)(hl:j≠k): g U (H j k) i=0∧g (L j) (L k) i=0:=by
    let P:= Equiv.swap j k; obtain ⟨w,hp⟩:=EuPin.choice (flag P); let s:=flag P; have hP :P i=i:= Equiv.swap_apply_of_ne_of_ne hi ht; have h1:s.perm j=k:= Equiv.swap_apply_left ..; have h2:s.perm k=j:=Equiv.swap_apply_right ..; let S:= flair [i,j,k]; have hS:S=gamma i*gamma j*gamma k:=by simp [S,flair,mul_assoc]
    have hW:conjug w S= - S:=by unfold S; rw [flairC P w hp]; simp only [flair,List.map_cons,List.map_nil,hP, List.prod_cons,List.prod_nil,mul_one, show P j=k from h1, show P k=j from h2,clifford hl.symm,mul_neg]
    constructor
    · obtain ⟨z,hz⟩:= grS a x i j k; change _=z • S at hz; have he:= passP a x U (H j k) i P w hp; rw [hem_ground, hem_η,hP, show (flag P).perm k=j from h2,show (flag P).perm j=k from h1,H_swap k j, hz, conj_s,hW,smul_neg] at he; rw [hz]; exact negS _ he.symm
    obtain ⟨z,hz⟩:= grP a x i j k; change _= z • S at hz; have he:= passP a x (L j) (L k) i P w hp; rw [hem_lead,hem_lead,hP,show (flag P).perm j=k from h1, show (flag P).perm k=j from h2, tollP, hz, truck_v, conj_s, hW, show truck S=S from by rw[hS,truck_triple i j k hi ht.symm hl.symm], smul_neg] at he; rw [hz]; exact negS _ he.symm
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.combo
#print axioms YM.Massive.Tawny.Cast.vanishX
