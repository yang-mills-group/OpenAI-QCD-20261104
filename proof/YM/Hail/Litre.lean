import YM.Next.MAXWELL.Stress
import YM.Next.MAXWELL.Mark
import YM.Avian.Icarus
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat
open Maxwell Maxwell.Free Maxwell.WaveOn Maxwell.Wick
open Massive Massive.Tawny Massive.Tawny.Cast Massive.Tawny.Cast.Perla Massive.Tawny.Cast.TableT
open scoped ContDiff Topology BigOperators InnerProductSpace
variable (a b i l j:Axis)(A:TaylorTower su)
open StressFlux (pair pairDeriv curl0 curl1)
lemma rowH (m:ℕ):takeCurl (gaugeJet (A m))=(A m).val:= match_leg _
lemma hZ:omegaLeg (G:=su)=omegaLeg:=rfl
lemma cryst0 : curl0 a b (gaugeJet (A 0))=asWave (A 0) a b 0:=by
   unfold StressFlux.curl0 StressFlux.curled; -- inspect
   change Tensor.diagonal (takeCurl (gaugeJet (A 0)) a b) 0= Tensor.diagonal ((A 0).val a b) 0; rw [rowH]
lemma cryst1 :curl1 l a b (gaugeJet (A 1))= Maxwell.grad l (asWave (A 1) a b) 0:=by rw [← Perla.BrickM.oneH]; change _= Maxwell.grad _ (Tensor.diagonal _) _; rw[rowH] -- binder w chosen ?
lemma pairR :reduceEq (pair su a i b l).val= Maxwell.Free.phi a b i l := equalPol _ _ fun X=>by rw[measure_phi,jet_value,StressFlux.pair_value,cryst0,cryst0]
lemma feeL(c:su.ColorIndex): glide su (basis i) 0 (omegaLeg c a b) (A 1)= curl1 i a b (gaugeJet (A 1)) c:=by
    let f:=asWave (A 1); let e:= (wavePoly (A 1)); have hh: nth f 1 0=(A 1).val:=asWave_jet _; have h:= samples_D (j:=0) e isOpen_univ (basis i) (mem_univ 0); let B: Solution su.Color 1:=⟨_,e.jets isOpen_univ (x:=0) (mem_univ _)⟩; rw[cryst1]; change omegaLeg c a b (lower _ _ _ (A 1))=Maxwell.grad _ (f a b) _ c; rw [show A 1=B from Subtype.ext hh.symm]; change (lower _ _ _ B).val a b _ c=_; rw [show (lower su.Color 0 (basis i) B).val=_ from h.symm]; simp only[nth,Tensor.coeff_apply_zero]; rfl
lemma meterL :probe A (rewired (glide su (basis j)) (Maxwell.Free.phi a b i l))= probe A (reduceEq ((pairDeriv su a i j b l).val+(pairDeriv su b l j a i).val)):=by
   have he (c : su.ColorIndex) (a b) : omegaLeg c a b (A 0) = curl0 a b (gaugeJet (A 0)) c :=by rw [cryst0]; rfl
   have hh(x y:su.Color):inner ℝ x y=∑ i:su.ColorIndex,x i*y i:=by rw [real_inner_comm]; rfl
   simp only [Maxwell.Free.phi,map_sum, Derivation.leibniz,smul_eq_mul,map_mul,map_add,
      rewired_symbol,symbol_test,he]; simp only [feeL, Finset.sum_add_distrib]; rw [jet_value, StressFlux.pairDeriv_value,jet_value,StressFlux.pairDeriv_value]; simp only [hh,Complex.ofReal_sum,Complex.ofReal_mul];
lemma cutL :rewired (glide su (basis j)) (reduceEq (pair su a i b l).val) = reduceEq (pairDeriv su a i j b l).val+reduceEq (pairDeriv su b l j a i).val:=by
    rw[pairR,←map_add]; apply equalPol; exact fun X=>meterL ..
end YM.Hail
#print axioms YM.Hail.cutL
