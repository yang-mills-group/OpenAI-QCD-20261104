import YM.MassiveQCD.Palette.Refund
/-! # Sum law and bills of republished regular column. 
 `lamp` after activation: one canon positive mass term plus Remainder at just the corresponding
 Healthy sites. Higher will deactivate. Must sum through the weighted exponent costs, radius
 reductions and paid units still separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ}{a r u t σ η ξ T :ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {ι:Type}(E:Gem c N ι)(z:Bool)(i:ι)(V:Grid c)
local notation "Z"=>EvenA c N
noncomputable def amount (E:Gem c N ι): Flavor N→ℝ:= fun b=> qMass (till E b 0)
noncomputable def canon (c: Side)(U:Flavor N→ℝ): Gem c N (Site c):= ⟨fun i=> ⟨i,{i},mem_singleton_self _⟩,fun i _=> beam i (fun b=>(U b:ℂ) • (1: Spike))⟩
noncomputable def beamCL (o:Site c)(N:ℕ): (Flavor N→ Spike) →L[ℂ] EvenA c N := LinearMap.toContinuousLinearMap ((meterF c N).comp ({ toFun:= fun f b=> localX o (f b),map_add':=fun _ _=>funext fun _=>lives ..,map_smul':=fun a X=>funext fun i=> pineS o (X i) a } : (Flavor N→ Spike) →ₗ[ℂ] FlavorF N c)) -- sig check.
private lemma spokeBegin (V:Grid c)(he:E.Gather)(hp:Keyed E)(hU:∀ b s,Summable fun i=> ‖lane E b i s‖):
     HasSum (letters (spoke E true) t V) (Patron.total (canon c (amount E)) t V):=by
    let A:=spoke E true
    let B:=canon c (amount E)
    let f (o:Site c)(i:ι)(b):=unitM E b o none i
    have hx o: HasSum (f o) (fun b=> (amount E b:ℂ) • (1:Spike)):= Pi.hasSum.2 (fun b=> by
        have hv:= (concession E b (hU b none) o).hasSum; change HasSum (unitM E b o none) _; change HasSum _ (till E b o none) at hv; rw [Phased.plums E b he hp (hU b) o, muse (Phased.portraits E b he hp (hU b))] at hv; exact hv)
    let F (o:Site c)(i:ι):= if Healthy t {o} V then beam o (f o i) else 0
    have he' (o:Site c): HasSum (F o) (letters B t V o):=by
       unfold F letters; split
       next h=> rw [masked_eq _ _ _ _ (show Healthy t (B.addr o).support V from h)]; exact (beamCL o N).hasSum (hx o)
       next h=> rw [masked_ne _ _ _ _ (show ¬ Healthy t (B.addr o).support V from h)]; exact hasSum_zero
    unfold Patron.total; rw [tsum_fintype]; apply (hasSum_sum (s:=univ) (fun i _=> he' i)).congr_fun
    intro i; let o:= (E.addr i).site
    change (letters A t V i)= ∑ o:Site c, F o i; rw [sum_eq_single o]
    · unfold F; split
      next h=> unfold letters; rw [masked_eq _ _ _ _ (show Healthy t (A.addr i).support V from h)]; apply congr_arg (beam o); exact funext fun b=> (if_pos rfl).symm -- defeq photon? lean
      next h=> exact masked_ne _ _ _ _ h
    · intro w _ hn; have hv : f w i=0:=funext (fun b=> if_neg hn)
      unfold F; rw [hv, show beam w (0:Flavor N→Spike)=0 from map_zero (beamCL w N),ite_self]; -- tactic syntax
    simp
lemma spokeLamp (he:E.Gather)(hp:Keyed E)(hU:∀ b s,Summable fun i=> ‖lane E b i s‖): HasSum (letters (spoke E z) t V) (if z then Patron.total (canon c (amount E)) t V else 0):=by
    cases z
    · refine ((show HasSum (fun _:ι=> (0:Z)) 0 from hasSum_zero)).congr_fun ?_;
      intro x; unfold letters; by_cases h: Healthy t ((spoke E false).addr x).support V; · rw [masked_eq _ _ _ _ h]; exact map_zero (beamCL (E.addr x).site N)
      exact masked_ne _ _ _ _ h
    simpa only [↓reduceIte] using spokeBegin E V he hp hU (t:=t)
noncomputable def tideCost (N:ℕ)(M:ℝ):ℝ:=stampFee N * M +2
lemma weightEase (M:ℝ) (h:1≤M): 1 ≤ tideCost N M:= one_le_two.trans (le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans stampFound) (zero_le_one.trans h))) -- potential 1≤2 simp
variable (hM :∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ u*Sen i w X)
variable (f:ι→ℝ)(h:1 ≤ u)(hv:0<t)(ht:∀ i,Woven (E.addr i).site (E.addr i).support p t (E.view i) (f i))
local notation "S'"=> shadowE E z
local notation "Υ"=> (refund E z p.threshold)
local notation "C"=> (tideCost N u)
include hM h ht hv
lemma payed (x y:ℝ)(hL:Anchored (fun i=>(E.addr i).site) f (fun i=>coverNumber p.B (E.addr i).support) x r) (he:y+1+1≤x)(hx:0 ≤ y) :
    Anchored (fun i=>(E.addr i).site) (fun i=>C*f i) (fun i=>coverNumber p.B (E.addr i).support) x (C*r) ∧ Ac.Hit (Υ).bud p.B (fun i=>C*f i) y (payment 1 (4*p.B+2) 0 1 1 (C*r) y 0) ∧
    (∀ i,Woven (E.addr i).site (E.addr i).support p t ((S').view i) (C*f i)) ∧ (∀ i V, ‖token c N t ((Υ).mean i V)‖≤ C*f i) :=by
    have hF:=weightEase (N:=N) u h; have hz:= zero_le_one.trans hF; have hQ : Anchored (fun i=>(E.addr i).site) (fun i=>C*f i) (fun i=>coverNumber p.B (E.addr i).support) x (C*r):= fun V=> by
       convert! budget_scale hz (hL V) using 1; funext i; by_cases h:(E.addr i).site=V <;> first| rw [if_pos h,if_pos h,mul_assoc]| rw [if_neg h,if_neg h,mul_zero]
    have hf i:= mul_nonneg hz (ht i).travel; have hh i:= tempo E z i (zero_le_one.trans h) hM hv (ht i); refine ⟨hQ,Stem.tipped E _ hQ hf he hx,fun i=> (hh i).2.2,?_⟩
    intro i V; change ‖token _ _ _ (ite _ 0 _)‖≤ _; split
    next _=> rw [map_zero,norm_zero]; exact hf i
    next _=>
     obtain ⟨ht',hG,-⟩:=hh i
     rw [map_neg,map_add,norm_neg]
     apply (norm_add_le ..).trans; have hM': ‖token c N t ((baker c N) (gemTone E i))‖≤ f i:= (shot (lens (E.addr i).site) (Cove.light (Keys c N) ((baker c N) (gemTone E i))) t hv).trans ((vine (E.addr i).site (gemTone E i) t hv.le).trans_le ht') -- defeq.
     apply (add_le_add (d:=stampFee N*u*f i) hM' ?_).trans ?_
     swap
     · unfold tideCost; nlinarith only [(ht i).travel]
     unfold letters; by_cases hP: Healthy p.threshold ((spoke E z).addr i).support V
     · rw [masked_eq _ _ _ _ hP]; apply (shot _ _ t hv).trans; exact hG.sizeU V hP
     rw [masked_ne _ _ _ _ hP,map_zero,norm_zero]; exact hG.travel
end YM.QCD.Stew.Phased
