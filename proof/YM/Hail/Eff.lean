import YM.Hail.Quota
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical ComplexOrder
open Massive.Tawny Massive.Tawny.Cast Perla Perla.Fore Carnal Rays TableT Drill Maxwell.Free
open Finset Module LinearMap
variable {d e k:ℕ}(a b i l j:Axis)(r:QCD.Flavor 6→ℂ)(p: ℂ)
-- offshell gives exact conservation plane matrix. propose
local notation "H"=>symbS 1
noncomputable def flood (p:ℂ)(r:QCD.Flavor 6→ℂ) : RawTensor 1 8:=p • solid + ∑ i: QCD.Flavor 6, r i • ((1/4:ℂ) • sunS i)
noncomputable def shore (p:ℂ)(r:QCD.Flavor 6→ℂ):= H (flood p r)
lemma reachZ (x:Fin 4→ℂ)(u:Values 4)(h:quoV (hydra u,striga x)=0): H (poseσ (u,x))= shore (x 1) (fun i=> 4 * u i 1)+ x 0 • H epi:=by
     obtain ⟨hp,hx,hc⟩:= (omegaV (striga x) (hydra u)).1 h; have ht:x 2=0:= (mul_eq_zero.mp hp).resolve_left (by norm_num); have hz:x 3= -(1/4)*x 1:=by
          change 1/2*x 1+2*x 3=0 at hx; linear_combination hx/2
     have hk(i:QCD.Flavor 6): H (axisσ i (u i))=(4*u i 1) • ((1/4:ℂ) • H (sunS i)):=by
          have H' : u i 0=0:= (hc i).1; have HE:u i 2=0:= (mul_eq_zero.mp (hc i).2.1).resolve_left (by norm_num)
          unfold axisσ; simp only[H',HE,_root_.map_add,_root_.map_smul,zero_smul,simplify_s,smul_zero,zero_smul,zero_add,add_zero]; module
     rw [show poseσ (u,x)= poseσT u + gaugeσ x from rfl]; simp only[poseσT,_root_.map_add,_root_.map_sum,hk]; unfold gaugeσ shore flood solid;
     simp only[_root_.map_sum,_root_.map_add,_root_.map_smul,_root_.map_sub, ht,hz]; module
variable (X: Points 1) (hx: X∈ conf 1) (f:QCD.Flavor 6)
set_option quotPrecheck false
local notation "V"=> (moment (fun _:Fin 1=> 8) X).toLinearMap 0 0
local notation "R"=> Maxwell.Wick.moment su X
private lemma pillow {d:ℕ}(t:Fin d→ℕ)(i:Fin d)(X:Points d)(hx:X∈conf d)(S T:Seed (letters (t i))) : lease (chime t X) (twig t i (line S * line T))=0:=by
      let P:=rifle t i; rw [_root_.map_mul, show twig t i (line S)=line (P S) from ExteriorAlgebra.map_apply_ι _ _, show twig t i (line T)=line (P T) from ExteriorAlgebra.map_apply_ι _ _, ← show pwn [P T]=line (P T) from (by simp [pwn]), DawnS.veil]; apply sum_eq_zero; intro j _; have hP:[P T].get j=P T:=by have ht: j=(0:Fin 1):=Subsingleton.elim (α:=Fin 1) _ _; rw [ht]; rfl
      rw [hP,show unionB (chime t X) (P S) (P T)=0 from quiets X hx i S T,mul_zero,zero_mul]
include hx
lemma monoV (v:Pol 8): V v=moment (fun _:Fin 1=>8) X (fun _=>v):=by rw [MultilinearMap.toLinearMap_apply]; apply congr_arg; funext i; fin_cases i; simp
lemma spirit (g:GPol)(h:SpinPol 8) : V (g⊗ₜ[ℂ] h)= R (fun _=>Maxwell.reduceEq g)* lease (chime _ X) (twig (fun _:Fin 1=> 8) 0 h):=by rw [monoV X hx]; have hh:= stroll (u:=fun _:Fin 1=>8) X hx (fun _=>g) (fun _=>h); refine hh.trans ?_; rw [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
lemma meansE :V (UV.unit 8)=1:=by change V ((1:GPol)⊗ₜ[ℂ] 1)=_; rw[spirit X hx, map_one,map_one, DawnS.clean1]; rw[mul_one]; exact Maxwell.Wick.constants _
lemma meansP : V (GG a b i l).val=0:=by
      change V ((StressFlux.pair su a b i l).val⊗ₜ[ℂ]1)=0; rw[spirit X hx, map_one,DawnS.clean1,mul_one,pairR];
      -- phi sum exploits delta.P.
      let cy(v:Maxwell.WickPol su):= R (fun _=>v); have ht(v: Maxwell.WickPol su): cy v= (R).toLinearMap 0 (0:Fin 1) v:=by change R _= R _; apply congr_arg; funext i; fin_cases i; simp
      change cy _=_; rw[ht]; unfold Maxwell.Free.phi; rw [_root_.map_sum]; apply sum_eq_zero; intro c _; rw [← ht]; have hN:= Maxwell.Free.moment_one (G:=su) (omegaLeg c a b) (fun _:Fin 1=>Maxwell.symbol 0 (omegaLeg c i l)) 0 hx; rw [show (univ.erase (0:Fin 1))=∅ from (by decide),sum_empty] at hN; refine Eq.trans ?_ hN; unfold cy; apply congr_arg; funext i; fin_cases i; simp
set_option maxHeartbeats 590000 in
lemma meansB(c:Hue)(u v: Pinor)(p q:Multi 8) : V ((1:GPol)⊗ₜ[ℂ] (bar ((p,u,c),f)*psi ((q,v,c),f))) =0:=by
    rw[spirit X hx]; apply mul_eq_zero_of_right; let g:Fin 1→ℕ:=fun _=>8; let P:=rifle g 0; let s:letters 8:= bt u c f p; let t: letters 8:= cl v c f q; let S:= thetaBasis _ s; let T:= thetaBasis _ t
    change lease (chime _ _) (twig g 0 (line S*line T))=_; exact pillow g 0 X hx S T
lemma meansS (p q:Multi 8)(F:Spike): V (UV.bilinear f f F p q)=0:=by unfold bilinear; simp_rw [TensorProduct.tmul_sum,TensorProduct.tmul_smul, _root_.map_sum,_root_.map_smul,meansB X hx,smul_zero,sum_const_zero] -- fix
end YM.Hail
#print axioms YM.Hail.reachZ
#print axioms YM.Hail.meansE
#print axioms YM.Hail.meansP
#print axioms YM.Hail.meansB
