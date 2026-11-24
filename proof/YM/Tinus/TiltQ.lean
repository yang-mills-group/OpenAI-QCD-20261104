import YM.Tinus.Turn
import YM.Clays.Mica
import YM.HONE.Bird
import YM.QCD.Creek.Horizon
import YM.QCD.Cove.Wave
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide Creek QCD.Cove
open Finset
open scoped Kronecker
variable (a b:Flavor F)(u: Site c)(X:Spike)
local notation "Φ"=> localF u X a b
open Revolve
lemma w_herd (v:Site c)(s:Signed)(l:Site c→ℂ)(P X':Spike)(hP:star P*X'=X*star P): localF u X a b* Lat.copies F (hues v s l P)= Lat.copies F (hues v s l P)*localF (shiftE s v u) X' a b:=by
    let z:=shiftE s v; let V:=hues v s l P; let w:= Lat.copies F V; let A:= zone F u; let B:= zone F (z u)
    have ht:A*w=w*B:=by
          unfold A B; ext i j; rw [zleft,zright]; by_cases h:z i.1.1=j.1.1
          · simp only [show (j.1.1=z u)=(i.1.1=u) from propext (by rw [←h]; exact z.injective.eq_iff)]
          have hk: w i j=0:=by
             unfold w V; unfold copies; rw [Matrix.blockDiagonal_apply]; split; · rw [hues,rides]; exact if_neg h
             rfl
          rw [hk,ite_self,ite_self]
    have hs: onSpin c X*V=V*onSpin c X':=by unfold V hues onSpin; rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext x; simp only [Equiv.refl_apply, Matrix.mul_smul, Matrix.smul_mul,wave_mul,hP]
    let f:=flavorW X a b c; let f':=flavorW X' a b c; have hC: A*f*w=w*(B*f'):=by
          have he:f*w=w*f':=by
              change (_ ⊗ₖ spot a b)*Kit.choir F V=Kit.choir F V*(_ ⊗ₖ spot a b); rw [QCD.Sway.choir_in]; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]; rw [hs]; simp
          rw [mul_assoc,he,←mul_assoc,ht,mul_assoc]
    exact hC
lemma L_tilt(g:Bool)(P Q R:Sour A)(hQ: Q *R=R*star P)(hP: R*Q=star P*R) (u: Dirac A): tilt R (applyMark g P u)=applyMark (!g) Q (tilt R u):=by
    let f:=tilt R; let t:=applyMark g P; let w:=applyMark (!g) Q; suffices h:∀ (i:Pairs A), f (t (atom i))= w (f (atom i)) by
        have H (s:List (Pairs A)): f (t (s.map atom).prod)=w (f (s.map atom).prod):=by
             induction s with
             | nil=> simp [f,t,w,L_one]
             | cons i s ih=>
                simp only [List.map_cons,List.prod_cons]; rw [show f (atom i* (List.map atom s).prod)= f (List.map atom s).prod *f (atom i) from tilt_mul ..,show t (atom i* (List.map atom s).prod)= t (atom i)*(List.map atom s).prod+atom i*t (List.map atom s).prod from LMark ..,map_add, show w (_*_)=_ from LMark ..]; rw [show f (t (atom i)*_)= _ from tilt_mul ..,show f (atom i* t _)= _ from tilt_mul ..]; change f _ * f (t _)+ f (t _) * f _ = w (f _) * f _ + f _ * w (f _); rw [h,ih,add_comm]
        have h (s:Finset (Pairs A)):f (t (mono s))=w (f (mono s)):=by obtain ⟨q,-,-,hq⟩:= expression s; rw [hq]; simpa only [List.map_ofFn] using H (List.ofFn q)
        change f (t u)=w (f u); rw [←write u]; simp_rw [map_sum,map_smul,map_smulₛₗ,h]; rfl
    intro i; rcases i with i|i
    · cases g
      · change tilt R (applyMark false P (psi i))= applyMark true Q (tilt R (psi i)); rw [leftP,tilt_psi,map_sum,map_sum]; simp_rw [map_smul,map_smulₛₗ,tilt_psi,leftB,smul_sum,smul_smul]; rw [sum_comm]; conv_rhs=> rw [sum_comm]
        apply sum_congr rfl; intro j _; rw [← Finset.sum_smul,← Finset.sum_smul]; congr 1; have hz:=congr_fun (congr_fun hQ j) i
        simp_rw [mul_neg,neg_mul,sum_neg_distrib]; rw[neg_inj]; refine Eq.trans (?_ : _=(R*star P) j i) (hz.symm.trans ?_);
        · rw [Matrix.mul_apply]; exact sum_congr rfl (fun k _=> mul_comm ..)
        · rw [Matrix.mul_apply]; exact sum_congr rfl (fun k _=> mul_comm ..)
      change tilt R (applyMark true P (psi i))= applyMark false Q (tilt R (psi i)); rw [passP,map_zero,tilt_psi,map_sum]; simp_rw [map_smul,passB,smul_zero,sum_const_zero]
    cases g
    · change tilt R (applyMark false P (bar i))= applyMark true Q (tilt R (bar i)); rw [passB,map_zero,tilt_bar,map_sum]; simp_rw [map_smul,passP,smul_zero,sum_const_zero]
    change tilt R (applyMark true P (bar i))= applyMark false Q (tilt R (bar i)); rw [leftB,tilt_bar,map_sum,map_sum]; simp_rw [map_smul,map_smulₛₗ,tilt_bar,leftP,smul_sum,smul_smul]; rw [sum_comm]; conv_rhs=> rw [sum_comm]
    apply sum_congr rfl; intro j _; rw [← Finset.sum_smul,← Finset.sum_smul]; congr 1; have h:=congr_fun (congr_fun hP i) j; simp_rw [mul_neg,neg_mul,sum_neg_distrib]; rw[neg_inj]; exact h.symm
open Patria Patria.Depth TorusPCAC.Geometry Exposure
variable (i:Axis)(x y:Flavor 6)
lemma pots : star (spot a b)= spot b a:=by ext i j; simp [Matrix.star_eq_conjTranspose,spot, and_comm]
lemma zoneF : star (localF u X a b)=localF u (star X) b a:=by
    have hx: star (flavorW X a b c)= flavorW (star X) b a c:=by
       unfold flavorW; rw [←Lat.on_spin_star,←pots]; ext i j; rw [Matrix.star_eq_conjTranspose]; simp
    unfold localF; rw [star_mul,hx,zstar]; exact (commute_here ..).eq.symm
lemma carriesF (Y:Spike)(hy:gamma i*Y=star X*gamma i): let P:=eyeP c i; let s:=Signed.mirror i; star (localF u X x y)*P=P*localF (s.act u) Y y x:=by
    intro P s; have hu:= w_herd y x u (star X) 0 s (Patria.prism s) (gamma i) Y (by rw [gamma_star]; exact hy); rw [Patria.rotor,gamma_star] at hu; change _= _; rw[zoneF]; rw [show s.act u =shiftE s 0 u from (by simp [shiftE,Signed.actEquiv])]; exact hu
lemma tilt_L (u:Site c)(Y:Spike)(hy:gamma i*Y=star X*gamma i)(g:Bool)(V: QCD.Lat.Fields c 6): tilt (eyeP c i) (ore u g x y X V)= ore ((Signed.mirror i).act u) (!g) y x Y (tilt (eyeP c i) V):=by
    let R:=eyeP c i; let U₀:=localF u X x y; let U₁:=localF ((Signed.mirror i).act u) Y y x; have h:R*U₁=star U₀*R:= (carriesF u X i x y Y hy).symm; apply L_tilt _ U₀ U₁ R _ h; calc
         _= R*R*U₁*R:=by rw [show R*R=1 from eye_sq _,one_mul]
         _= R*star U₀:=by rw [mul_assoc R R U₁,h,mul_assoc,mul_assoc (star U₀),eye_sq,mul_one]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.tilt_L
