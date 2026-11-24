import YM.Lobo.Trident
set_option maxHeartbeats 670000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable (k i j:Tri)(t:ℝ){M:Type}[AddCommGroup M][Module ℂ M]
local notation "Y"=> edgeK k
local notation "Z"=> backK k
local notation "W"=> wing k t
variable (f:Tri→Tri→M)(hf:∀ i j,f i j= -f j i)
-- spatial Hodge orientation
include hf
lemma heelL : wing k t (fun a=>wing k t (f a) (backK i)) (edgeK i)= wing k t (fun a=> f (edgeK a) (backK a)) i:=by
      have h(j:Tri): f j j=0:=by
          apply smul_right_injective M (two_ne_zero (α:=ℂ)); change (2:ℂ) • _=(2:ℂ) • (0:M); rw [two_smul,smul_zero]; nth_rw 1[hf]; simp
      let c:ℂ:= Real.cos t; let s:ℂ:= Real.sin t; have hc: c^2+s^2=1:=by unfold c s; rw[← Complex.ofReal_pow,← Complex.ofReal_pow,←Complex.ofReal_add, show Real.cos t^2+Real.sin t^2=1 by rw[add_comm,Real.sin_sq_add_cos_sq], Complex.ofReal_one]
      obtain ⟨hy,hk,hz,hj⟩:= tracesI k
      have e(w:M): c • (c • w)+ s • (s • w)=w:=by rw [smul_smul,smul_smul, ← add_smul,← pow_two,← pow_two,hc,one_smul]
      rcases stateU k i with hp|hp|hp
      · subst i; rw [(wingsI k t _).2.1,(wingsI k t _).1,(wingsI k t _).2.2,(wingsI k t _).2.2,h Y,h Z,smul_zero,smul_zero,sub_zero,zero_sub, hf Z Y]; simp only [smul_neg,neg_neg]; exact e _
      · subst i; simp_rw[hy,hk]; rw[(wingsI k t _).2.2,(wingsI k t _).1,(wingsI k t _).1,(wingsI k t _).2.1]; rw [hk,hy,hz,hj,hf Y k,smul_neg, sub_neg_eq_add]
      · subst i; rw[hz,hj,(wingsI k t _).1,(wingsI k t _).2.1,(wingsI k t _).2.2, hz,hj,hk,hy, hf k Z, smul_neg]; abel
omit hf
-- double palm
noncomputable def hood (w:Bool)(i:Tri):Axis × Axis:= if w then (lieu i,timeAxis) else (lieu (edgeK i),lieu (backK i))
variable (F:Axis→Axis→M)(hp:∀ a b,F a b= -F b a)
include hp
lemma screw (w:Bool): let x:= hood w i; palm k t (fun j=> palm k t (F j) x.2) x.1= wing k t (fun a=>F (hood w a).1 (hood w a).2) i:=by
     intro x; cases w
     · change palm k t (fun j=> palm k t (F j) (lieu _)) (lieu (edgeK i))=_; rw[hat]; have h(a:Tri):palm k t (F (lieu a)) (x.2) = wing k t ((F (lieu a)) ∘lieu) (backK i):=hat ..
       refine Eq.trans (congr_arg (fun f:Tri→M=> W f (edgeK i)) (funext h)) ?_; exact heelL k i t (fun i a=> F (lieu i) (lieu a)) (fun _ _=> hp ..)
     change palm k t (fun j=> palm k t (F j) timeAxis) (lieu i)= _; simp_rw[lastB]; exact hat ..
end YM.Lobo
#print axioms YM.Lobo.screw
