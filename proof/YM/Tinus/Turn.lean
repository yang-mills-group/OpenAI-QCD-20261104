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
lemma L_slope (q:Bool)(X:Sour A)(Y:Sour A)(D D':Sour A)(h:X*D=D'*X)(hY:D *Y.transpose= Y.transpose*D')(x: Dirac A): applyMark q D (adapter X Y x)=adapter X Y (applyMark q D' x):=by
    let f:=adapter X Y; let g:=applyMark q D; let t:=applyMark q D'; suffices hh:∀ i:Pairs A,g (f (atom i))=f (t (atom i)) by
       have h (S:List (Pairs A)):g (f (S.map atom).prod)= f (t (S.map atom).prod):=by
            induction S with
            | nil=> simp [f,g,t,L_one]
            | cons i s ih=> simp only [List.map_cons,List.prod_cons,map_mul]; unfold g t; rw [LMark q,LMark q,map_add,map_mul,map_mul]; exact congr_arg₂ (·+·) (congr_arg (·*_) (hh i)) (congr_arg (_*·) ih)
       have h (s:Finset (Pairs A)):g (f (mono s))=f (t (mono s)):=by obtain ⟨w,-,-,hp⟩:= expression s; rw [hp]; simpa only [List.map_ofFn] using h (List.ofFn w)
       change g (f x)= f (t x); rw [← write x]; simp_rw [map_sum,map_smul,h]
    have H (p:Sour A)(D:Sour A)(x:A→ Dirac A)(i:A) : ∑ j,p i j • ∑ k,D j k • x k= ∑ j,(p*D) i j • x j:=by
        simp_rw [smul_sum, smul_smul,Matrix.mul_apply,sum_smul]; rw [sum_comm]
    intro i; cases q
    · rcases i with i|i
      · change applyMark _ _ (adapter X Y (psi i)) =adapter X Y (applyMark _ _ (psi i)); rw [adapt_psi,leftP,map_sum,map_sum]; simp_rw [map_smul,adapt_psi,leftP,H,h]
      change applyMark _ _ (adapter X Y (bar i))=adapter X Y (applyMark _ _ (bar i)); rw [adapt_bar,passB,map_zero,map_sum]; simp_rw [map_smul,passB,smul_zero,sum_const_zero]
    rcases i with i|i
    · change applyMark _ _ (adapter X Y (psi i))=adapter X Y (applyMark _ _ (psi i)); rw [adapt_psi,passP,map_zero,map_sum]; simp_rw [map_smul,passP,smul_zero,sum_const_zero]
    change applyMark _ _ (adapter X Y (bar i))=adapter X Y (applyMark _ _ (bar i)); rw [adapt_bar,leftB,map_sum,map_sum]; simp_rw [map_smul,adapt_bar,leftB]; change (∑ j,Y i j • ∑ k,D.transpose j k • bar k)= ∑ j,D'.transpose i j • ∑ k,Y j k • bar k; rw [H,H]
    have hh:= congr_arg Matrix.transpose hY; rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose] at hh; rw [hh]

open Revolve
lemma L_hue (g:Bool)(v:Site c)(s:Signed)(l:Site c→ℂ)(P:Spike)(t t':Site c)(h:Glare s t t' v l)(hp:Swing s P)(X':Spike) (hP:star P*X'=X*star P)(x: Fields c F) : let R:=Kit.disguise (Lat.copies F (hues v s l P)); let z:=shiftE s v; ore (z u) g a b X' (R x)=R (ore u g a b X x):=by
    let z:=shiftE s v; let V:=hues v s l P; let w:= Lat.copies F V; let A:= zone F u; let B:= zone F (z u); have hw: w∈unitary _:= Lat.copies_unitary _ _ (colour_wheel h hp)
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
    apply L_slope g w (star w).transpose (B*f') (A*f) hC.symm
    rw [Matrix.transpose_transpose]
    calc
          B*f'*star w = star w*w*(B*f')*star w:=by rw [hw.1,one_mul]
          _=star w*(A*f):=by rw [mul_assoc _ w,← hC,mul_assoc,mul_assoc ..,hw.2,mul_one]
open Patria Patria.Depth TorusPCAC.Geometry
variable {S:Scheme}{r:Side}(Y:Run S n r 6)(κv:Massive.Averaging)(hY:Y.Actual) {i m:ℕ}
noncomputable def stalk (a b:Flavor 6)(g:Bool)(T:ℕ)(v:Cover):Insertion (S.side r T) 6:= mark g (localF (wrap _ v) X a b) (actor Y T)
-- order X,Y
noncomputable abbrev sold (g:Bool)(a b:Flavor 6)(T:ℕ):= Patria.Depth.report Y (stalk X Y a b g T) κv
include hY
lemma stagger (x y:Flavor 6)(g: Bool)(h:i≤ n): Patria.Depth.TideT Y κv i (sold X Y κv g x y i):=by
     refine stampF Y _ κv ?_; intro a b; funext U; let X' := (actor Y i); let R:= shiftE (n:=S.side r i) 1 (wrap _ b); have ht: Patria.march b (⇑X')= ⇑X':=by unfold X'; rw [act Y hY h]; rw [pier Y hY h]; exact Patria.Depth.first _ _ h _
     have hk:= L_hue x y (wrap (S.side r i) a) X g (wrap _ b) 1 (heat b) 1 0 0 (TorusPCAC.Geometry.glares b) Revolve.Swing.none X (by simp) (actor Y i (pull 1 (wrap _ b) U)); change crank (n:=S.side r i) 1 1 (wrap _ b) (heat b) (ore (wrap _ a) g x y X (X' (pull 1 (wrap _ b) U)))= ore (wrap _ (a+b)) g x y X (X' U)
     rw [← show Patria.march b X' U=X' U from congr_fun ht U, show wrap (S.side r i) (a+b)= R (wrap _ a) from (by simp [R,shiftE,Signed.actEquiv])]; exact hk.symm
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.stagger
