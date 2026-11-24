import YM.Lobo.Nectar
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.NativeV
open Lobo
open scoped Classical BigOperators
variable (D : Tri→Tri→Tri→Tri→Tri→ℂ) (p f e:ℂ)
local notation "w"=> waveT
noncomputable def tiltT(D : Tri→Tri→Tri→Tri→Tri→ℂ)(p f e:ℂ)(i j m q s t:Tri):ℂ:= ∑ k:Tri,(w i m k*p*D j k q s t + w i q k*f*D j m k s t + w i s k*e*D j m q k t + w i t k* e* D j m q s k)
noncomputable abbrev τc(i j:Tri):ℂ:=charI i j
local notation "τ"=> τc
variable (h:∀ i m q s t:Tri,D i m q s t=D i m q t s) (hg:∀ k i m q s t, D i m q s t= τ k i*τ k m*τ k q*τ k s* τ k t * D (roof k i) (roof k m) (roof k q) (roof k s) (roof k t)) (hT:∀ i j m q s t,tiltT D p f e i j m q s t+tiltT D p f e j i m q s t=0)
include h hg hT
lemma fist (he:p≠f): D 1 1 2 1 0=0 ∧ D 2 1 2 2 0=0 ∧ D 0 1 2 0 0=0 ∧ D 0 1 2 1 1+D 0 1 2 2 2=0:=by
     let P:=D 0 0 1 0 2
     let Z:=D 0 1 0 0 2
     let C:=D 0 1 1 1 2
     let U:=D 0 1 2 0 0
     let J:=D 0 1 2 1 1
     let L:=D 0 1 2 2 2
     have m00102: D 0 0 1 0 2=P:=rfl
     have m00201: D 0 0 2 0 1=-P:=by
           have hh:=hg 0 0 0 1 0 2; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m00102] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have Q0: (-2:ℂ)*f*P + (2:ℂ)*e*P=0:=by
            have H:= hT 0 0 0 1 0 1; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m00102 ,m00201] at H; linear_combination H
     have m01002: D 0 1 0 0 2=Z:=rfl
     have m02001: D 0 2 0 0 1=-Z:=by
           have hh:=hg 0 0 1 0 0 2; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m01002] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have Q1: (-2:ℂ)*p*Z + (2:ℂ)*e*Z=0:=by
            have H:= hT 0 0 1 0 0 1; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m01002 ,m02001] at H; linear_combination H
     have m01200: D 0 1 2 0 0=U:=rfl
     have m02100: D 0 2 1 0 0=-U:=by
           have hh:=hg 0 0 1 2 0 0; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m01200] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have Q2: (-2:ℂ)*p*U + (2:ℂ)*f*U=0:=by
            have H:= hT 0 0 1 1 0 0; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m01200 ,m02100] at H; linear_combination H
     have m01222: D 0 1 2 2 2=L:=rfl
     have m02111: D 0 2 1 1 1=-L:=by
           have hh:=hg 0 0 1 2 2 2; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m01222] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m01211: D 0 1 2 1 1=J:=rfl
     have m01112: D 0 1 1 1 2=C:=rfl
     have m01121: D 0 1 1 2 1=C:= (h 0 1 1 2 1).trans m01112
     have Q3: (-2:ℂ)*p*L + (2:ℂ)*f*J + (4:ℂ)*e*C=0:=by
            have H:= hT 0 0 1 1 1 1; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m01112 ,m01121 ,m01211 ,m02111] at H; linear_combination H
     have m02122: D 0 2 1 2 2=-J:=by
           have hh:=hg 0 0 1 2 1 1; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m01211] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have Q4: (-4:ℂ)*e*C + (-2:ℂ)*p*J + (2:ℂ)*f*L=0:=by
            have H:= hT 0 0 1 1 2 2; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m01112 ,m01121 ,m01222 ,m02122] at H; linear_combination H
     have m10002: D 1 0 0 0 2=-C:=by
           have hh:=hg 2 0 1 1 1 2; rw [show roof 2 0=1 from (by decide),show roof 2 1=0 from (by decide),show roof 2 2=2 from (by decide)] at hh; rw[m01112] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m00021:D 0 0 0 2 1=0:=by
          have h0:=hg 0 0 0 0 2 1; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at h0; simp +decide only [τc,charI, ↓reduceIte,Complex.ofReal_one,Complex.ofReal_neg,neg_one_mul,neg_neg,mul_one,one_mul] at h0
          have h1:=h 0 0 0 1 2
          linear_combination ( 1 * h0+ -1 * h1)/2
     have Q5: (-1:ℂ)*e*C + (1:ℂ)*p*Z + (1:ℂ)*f*P=0:=by
            have H:= hT 0 1 0 0 0 1; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m00021 ,m00201 ,m02001 ,m10002] at H; linear_combination H
     have m11210: D 1 1 2 1 0=P:=by
           have hh:=hg 2 0 0 2 0 1; rw [show roof 2 0=1 from (by decide),show roof 2 1=0 from (by decide),show roof 2 2=2 from (by decide)] at hh; rw[m00201] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m11201: D 1 1 2 0 1=P:= (h 1 1 2 0 1).trans m11210
     have m12110: D 1 2 1 1 0=Z:=by
           have hh:=hg 2 0 2 0 0 1; rw [show roof 2 0=1 from (by decide),show roof 2 1=0 from (by decide),show roof 2 2=2 from (by decide)] at hh; rw[m02001] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m12101: D 1 2 1 0 1=Z:= (h 1 2 1 0 1).trans m12110
     have m02221: D 0 2 2 2 1=-C:=by
           have hh:=hg 0 0 1 1 1 2; rw [show roof 0 0=0 from (by decide),show roof 0 1=2 from (by decide),show roof 0 2=1 from (by decide)] at hh; rw[m01112] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m12220: D 1 2 2 2 0=C:=by
           have hh:=hg 2 0 2 2 2 1; rw [show roof 2 0=1 from (by decide),show roof 2 1=0 from (by decide),show roof 2 2=2 from (by decide)] at hh; rw[m02221] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have m12202: D 1 2 2 0 2=C:= (h 1 2 2 0 2).trans m12220
     have Q6: (-2:ℂ)*p*P + (-2:ℂ)*f*Z + (2:ℂ)*e*C=0:=by
            have H:= hT 0 1 2 2 0 1; simp only[tiltT,Fin.sum_univ_three] at H; simp +decide only[signsU, ↓reduceIte,true_and,and_true,false_and,and_false, one_mul, zero_mul,neg_one_mul,zero_add,add_zero,m00201 ,m02001 ,m02221 ,m11201 ,m12101 ,m12202] at H; linear_combination H
     have m21220: D 2 1 2 2 0=-Z:=by
           have hh:=hg 1 0 1 0 0 2; rw [show roof 1 0=2 from (by decide),show roof 1 1=1 from (by decide),show roof 1 2=0 from (by decide)] at hh; rw[m01002] at hh; simp +decide [τc,charI] at hh ⊢; first|exact hh.symm|linear_combination hh|linear_combination -hh
     have W: U=0:= (mul_eq_zero.mp (show (f-p)*U=0 from (by linear_combination Q2/2))).resolve_left (sub_ne_zero.mpr he.symm) -- fix after
     have He:J+L=0:=by
           apply (mul_eq_zero.mp _).resolve_left (sub_ne_zero.mpr he)
           linear_combination ( -Q3 -Q4)/2
     have hp:P=Z:= sub_eq_zero.mp ((mul_eq_zero.mp (show (p-f)*(P-Z)=0 from by linear_combination -Q6/2 - Q5)).resolve_left (sub_ne_zero.mpr he))
     -- once hp, P=Z⇒0 via Q0 and Q1
     rw [←hp] at Q1; have hx:P=0:= (mul_eq_zero.mp (show (p-f)*P=0 from (by linear_combination (Q0-Q1)/2))).resolve_left (sub_ne_zero.mpr he)
     rw [m11210,m21220]; exact ⟨hx, by rw[←hp,hx]; simp, W,He⟩
end YM.NativeV
#print axioms YM.NativeV.fist
