import YM.Kwick.Bower
import YM.Affina.Rights
/-! Supplied Pan to Bowl on two orientations (powers8.D). tolerance rates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
variable {p q:ℕ}(α a ε η L Lb u v M1 M2 γ:ℝ)(x y:Z)(j:Axis)(P Q:BudgetPoint)(w w' r μ M W:ℝ)
variable {n:ℕ}{p:ℕ→Z}{Pt:ℕ→BudgetPoint}{A V:ℕ→ℝ}{Mv:Axis→ℕ→ℝ}(h:Pan n p Pt Mv A V u α a ε)
variable {K:ℕ→ℝ}(hK:0≤L)(hBp:∀ i:ℕ,0 < K i)(hT:∀ (i:ℕ),i<n → K i=L*K (i+1))(hd:L*a*u^11 ≤ 1/2)
local notation "Y"=> trunks p Pt A K
local notation "T"=> fun k:Fin 4=> nuP k Pt A V u L
local notation "F"=> (Fintype.card (Rings 10):ℝ)
local notation "ν" i:arg=> K i * Mv j i
variable (w v t s G ε:ℝ)(B:Fin 4 → ℝ)
-- point ε distortion
private lemma geom_small (x y e:ℝ) (h:0≤ ε)(he:20*ε≤1/4) (h0:0 ≤ e)(hY:e≤4*ε) (hx: |x-1|≤ε)(hz:|y-1| ≤e) : |x*y-1| ≤ 2*ε+e :=by
     have hh:=abs_sub_abs_le_abs_sub y 1; have hp: |y| ≤ 2:=by rw [abs_one] at hh; linarith only [hh,hz,hY,h,he]
     rw [show x*y-1=(x-1)*y+(y-1) from by ring]; refine (abs_add_le _ _).trans (add_le_add ?_ hz); rw[abs_mul,mul_comm 2]; exact mul_le_mul hx hp (abs_nonneg _) h
-- Allow loss constant 40: Step scales F.Epsilon.Growth.P. bound y± recursively with left factor order.
private lemma geom_large (x y e:ℝ) (h:0≤ ε)(he:20*ε≤1/4) (h0:0 ≤ e)(hY:e≤8*ε) (hx: |x-1|≤ε)(hz:|y-1| ≤e) : |x*y-1| ≤ 2*ε+e :=by
     have hh:=abs_sub_abs_le_abs_sub y 1; have hp: |y| ≤ 2:=by rw [abs_one] at hh; linarith only [hh,hz,hY,h,he]
     rw [show x*y-1=(x-1)*y+(y-1) from by ring]; refine (abs_add_le _ _).trans (add_le_add ?_ hz); rw[abs_mul,mul_comm 2]; exact mul_le_mul hx hp (abs_nonneg _) h
private lemma bq_small (t t1 w w1 z:ℝ) (hS:0 < t1)(hw:0<w1)(h:0 ≤ ε)(he:20*ε ≤1/4)(hz: |z^2-1| ≤ ε)(ht: |t/t1-1| ≤ ε)(hK:|w/w1-1| ≤ ε) (i:Fin 4): |bud i t (z*w)/bud i t1 w1-1| ≤ 20*ε:=by
     have hp: |w/w1*(w/w1)-1| ≤2*ε+ε:=geom_small ε _ _ _ h he h (by linarith only [h]) hK hK
     have hv:=geom_small ε (z^2) (w/w1*(w/w1)) (2*ε+ε) h he (by positivity) (by linarith only [h]) hz hp; let C:=2*ε+(2*ε+ε); let D:=z^2*(w/w1*(w/w1)); have hP:(z*w)^2/w1^2=D:=by unfold D; field_simp <;> ring
     have hh: |D-1|≤20*ε:= hv.trans (by linarith only [h])
     fin_cases i
     · change |t^0*(z*w)^2/(t1^0*w1^2)-1|≤_; rw [pow_zero,pow_zero,one_mul,one_mul,hP]; exact hh
     · change |t^0*(z*w)^2/(t1^0*w1^2)-1|≤_; rw[pow_zero,pow_zero,one_mul,one_mul,hP]; exact hh
     · change |t^1*(z*w)^2/(t1^1*w1^2)-1|≤_; rw [pow_one,pow_one,mul_div_mul_comm,hP]; have hz:|t/t1*D-1| ≤ 2*ε+C:= geom_large ε _ _ C h he (by unfold C; positivity) (by unfold C; linarith only [h]) ht hv; exact hz.trans (by unfold C; linarith only [h])
     · change |t^2*(z*w)^0/(t1^2*w1^0)-1|≤_; rw [pow_zero,pow_zero,mul_one,mul_one,←div_pow,pow_two]; exact (geom_small ε _ _ _ h he h (by linarith only [h]) ht ht).trans (by linarith only [h])
-- U recurrence weights ratio.K driven.L.Cost.
variable (hk:∀ i,0 < A i) (hvV:∀ i,i < n →|V i^2-1|≤ ε)(htV:∀ i,i<n→ |(Pt i).threshold/(Pt (i+1)).threshold-1|≤ ε)(hW:∀ i,i<n→|A i/A (i+1)-1|≤ ε)
structure Twist (n:ℕ) (Pt:ℕ→BudgetPoint) (A V:ℕ→ℝ)(d u e:ℝ) :Prop where
    x (i:ℕ)(hi:i<n): |nuP 0 Pt A V u (d^4) i-1| ≤ e
    eT (k:Fin 4)(hk:k≠0)(i:ℕ)(hi:i<n): |nuP k Pt A V u (d^4) i| ≤1
    g (i:ℕ)(hi:i<n):2 ≤ nuP 0 Pt A V u (d^5) i
    t (k:Fin 4)(hk:k≠0)(i:ℕ)(hi:i<n): |nuP k Pt A V u (d^5) i-1| ≤ e
lemma motionV (u d:ℝ)(hV: d*u^2=1)(ha:0 ≤ a)(hu:0 <u)(hd:3 ≤ d)(hf: 4*a*u ≤1/2): d^4*a*u^11≤1/2 ∧ d^5*a*u^11 ≤1/2 :=by
       have hz: d^5*a*u^11=a*u:=(calc d^5*a*u^11=(d*u^2)^5*a*u:=by ring
                                        _ = _ := by rw[hV]; ring) -- syntax
       have h : a*u≤1/2:=by nlinarith only [mul_nonneg ha hu.le,hf]
       have he:1 ≤ d:=le_trans (by norm_num) hd; refine ⟨?_,hz.symm ▸ h⟩; calc
         d^4*a*u^11 ≤ d^5*a*u^11:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ he (by norm_num)) ha) (by positivity)
         _ ≤ _:= hz.symm ▸ h
include hk hvV htV hW
lemma turnsP (d u:ℝ) (hU:0 ≤ ε) (hε:20*ε≤1/4)(hd:3 ≤ d)(hV:d*u^2=1): Twist n Pt A V d u (20*ε):=by
    have hh (i:Fin 4)(j:ℕ)(hj:j<n): |bud i (Pt j).threshold (V j*A j)/bud i (Pt (j+1)).threshold (A (j+1))-1| ≤20*ε:= bq_small ε _ _ _ _ _ ((Pt (j+1)).threshold_pos) (hk _) hU hε (hvV _ hj) (htV _ hj) (hW _ hj) i
    have hk1:d^4*u^8=1:=by rw [show d^4*u^8=(d*u^2)^4 from by ring,hV,one_pow]
    have hk2:d^5*u^10=1:=by rw [show d^5*u^10=(d*u^2)^5 from by ring,hV,one_pow]
    have hp:0 < d:=by linarith only [hd]
    have hQ :d^4*u^10=d⁻¹:=by apply mul_right_cancel₀ hp.ne'; rw [inv_mul_cancel₀ hp.ne',show d^4*u^10*d=d^5*u^10 from by ring,hk2]
    have hx(i:Fin 4)(hk:i≠0): (tierQ i).1=10:=by fin_cases i <;>first | rfl| (apply False.elim; exact hk rfl)
    refine ⟨fun i hi=>?_,fun k hk i hi=>?_, fun i hi=>?_, fun k hk i hi=>?_⟩
    · unfold nuP; rw [show (tierQ 0).1= 8 from rfl,hk1,one_mul]; exact hh _ _ hi
    · unfold nuP; rw[hx _ hk,hQ,abs_mul, abs_of_nonneg (by positivity)]; let X:= bud k (Pt i).threshold (V i*A i)/bud k (Pt (i+1)).threshold (A (i+1)); have hh :|X-1|≤ 20*ε:=hh k i hi; have h: |X| ≤ d:=by have h:=abs_sub_abs_le_abs_sub X 1; rw[abs_one] at h; linarith only [h,hh,hd,hε]
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)).trans_eq (inv_mul_cancel₀ hp.ne')
    · unfold nuP; rw [show (tierQ 0).1=8 from rfl,show d^5*u^8=d*(d^4*u^8) from by ring,hk1, mul_one]; let X:= bud 0 (Pt i).threshold (V i*A i)/bud 0 (Pt (i+1)).threshold (A (i+1)); obtain ⟨h,_⟩:=abs_le.mp (hh 0 i hi); have hp':3/4≤X:=by change _ ≤ X-1 at h; linarith only [h,hε]
      exact le_trans (by norm_num:(2:ℝ)≤3*(3/4)) (mul_le_mul hd hp' (by norm_num) hp.le)
    unfold nuP; rw [hx _ hk,hk2,one_mul]; exact hh _ _ hi
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.turnsP
