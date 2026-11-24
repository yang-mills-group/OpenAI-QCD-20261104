import YM.Lust.Sans
/-!
  On arbitrary compact and time-varying poly persists. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} {P: Calibration C} {β ν:ℝ}(hp:C.Path β ν) {n:ℕ} (hr:Sway C.S)
-- if dim implies light even w/o system.
variable (U:Fin n→ (k:ℕ)→stalk C k) (v:(k:ℕ)→ stalk C k)
include hp hr
lemma torch (hU:∀ i, LightP C (U i))(r:ℝ)(hx:0<r):∃ L:ℝ,0≤L∧∀ᶠ i in atTop,∀ f:Fin n→ Cover,localSep C i f r → ‖readS C i (fun k=> U k i) f‖ ≤ L:=by
    obtain ⟨N,hN⟩:=eventually_atTop.mp ((eventually_all.mpr hU).and (hr.high.eventually_gt_atTop (6*n))); obtain ⟨j,hj,h⟩:= shyness hp r hx N; obtain ⟨he,hQ⟩:=hN j hj; choose v hv H using he; refine ⟨∏ i,v i,Finset.prod_nonneg (fun i _=> hv i),?_⟩; filter_upwards [eventually_all.mpr H,hp.uv.tendsto_atTop.eventually_ge_atTop (j+1)] with i hi hk f hx; exact reapS i j _ _ hp hi f (tide _ _ _ hx (Nat.le_of_lt hk) h) hQ hk
lemma silver (p:Fin n)(hU:∀ i,i≠p→ LightP C (U i))(h:DimP C v)(r:ℝ)(hx:0<r)(ε:ℝ)(he:0<ε):∀ᶠ i in atTop,∀ f:Fin n→ Cover,localSep C i f r → ‖readS C i (update (fun k=> U k i) p (v i)) f‖ ≤ ε:=by
    let L:= {i:Fin n// i≠p}; obtain ⟨N,hN⟩:=eventually_atTop.mp (((eventually_all.mpr (fun i:L=> hU i.val i.property)).and h).and (hr.high.eventually_gt_atTop (6*n))); obtain ⟨j,hj,hJ⟩:=shyness hp r hx N; obtain ⟨⟨H,F,hF,hV⟩,hG⟩:=hN j hj; choose! c hc H using H
    let W (i:Fin n):ℝ:= if h:i=p then 0 else c ⟨i,h⟩; let K:= ∏ i∈ Finset.univ.erase p,W i; have ht:Tendsto (fun i=> F i*K) atTop (𝓝 0):=by simpa only [zero_mul] using hF.mul_const K
    filter_upwards [eventually_all.mpr H,hV,hp.uv.tendsto_atTop.eventually_ge_atTop (j+1), ht.eventually_le_const he] with i h hp hi hF f hv
    let w:= update W p (F i); let u:= update (fun k=> U k i) p (v i); have hV(t):GreenP C i j (u t) (w t):=by
         by_cases hz:t=p; · subst t; unfold u w; rw[update_self,update_self]; exact hp.2
         unfold u w; rw[update_of_ne hz,update_of_ne hz,show W t=c ⟨t,hz⟩ from dif_neg hz]; exact h ⟨t,hz⟩
    apply le_trans (reapS i j u w ‹C.Path β ν› hV f (tide _ _ _ hv (le_trans (Nat.le_succ _) hi) hJ) hG hi)
    rwa [show ∏ t,w t= w p*∏ t∈Finset.univ.erase p,w t from (mul_prod_erase _ _ (mem_univ _)).symm,show ∏ t∈Finset.univ.erase p,w t=K from prod_congr rfl (fun i hi=> update_of_ne (Finset.ne_of_mem_erase hi) ..),show w p= _ from (update_self ..)] -- ambiguity
omit hr
-- idem for brush. one unmatched
variable (d:ℕ)
open GaugeP
lemma purseB (Z':Cottage P d)(p:Fin n)(hU:∀ i,i≠p→LightP C (U i))(z:ℕ→Stokes d→ℂ)(hq:Brush Z'.E Z'.K v z)(r:ℝ)(hx:0<r)(ε:ℝ)(he:0<ε):∀ᶠ i in atTop,∀ f:Fin n→ Cover,localSep C i f r → ‖readS C i (update (fun k=> U k i) p (v i-stem P d i (Z'.K.ridge i (z i)))) f‖ ≤ ε:=by
    let L:= {i:Fin n// i≠p}; obtain ⟨N,hN⟩:=eventually_atTop.mp ((eventually_all.mpr (fun i:L=>hU i.val i.property)).and (hq.dimin n p)); obtain ⟨j,hj,hJ⟩:=shyness hp r hx N; obtain ⟨H,h⟩:=hN j hj; choose c hc hU using H; let W(t:Fin n):ℝ:= if h:t=p then 0 else c ⟨t,h⟩; have hs:∀ᶠ i in atTop, ∀ k,k≠p→ GreenP C i j (U k i) (W k):=(eventually_all.mpr hU).mono (fun i h k hk=>by rw[show W k=c ⟨k,hk⟩ from dif_neg hk]; exact h ⟨k,hk⟩); filter_upwards [h _ W hs ε he,hp.uv.tendsto_atTop.eventually_ge_atTop j] with i hi hk f hv; exact hi _ (tide _ _ _ hv hk hJ)
-- labels.Ang for constant
include hr
variable (Zp:∀ d,Cottage P d)
lemma cupR (X:Label d) (D:ℕ)(h:d≤ D):∃ z:ℕ → Stokes D→ℂ, Brush (Zp D).E (Zp D).K (fun i=>stem P d i X) z:=by
    obtain ⟨p,hP⟩:=(Zp D).ink d h X; exact ⟨_, braidVal _ hp hr (Zp D).rise _ hP ((Zp d).pointsP hp hr none (fun _=>X) ⟨‖X‖,norm_nonneg _, Eventually.of_forall fun _=> le_rfl⟩).1⟩
lemma crossP (X:Label d)(D:ℕ)(h:d+2 ≤D)(b:Axis):∃ z:ℕ → Stokes D→ℂ, Brush (Zp D).E (Zp D).K (fun i=> lDer C i b (stem P d i X)) z:=by
    obtain ⟨p,hP⟩:=(Zp D).eye d h X b; exact ⟨_, braidDer _ hp hr (Zp D).rise _ b hP ((Zp d).pointsP hp hr none (fun _=>X) ⟨‖X‖,norm_nonneg _, Eventually.of_forall fun _=> le_rfl⟩).1⟩
end YM.Massive.Needle
#print axioms YM.Massive.Needle.cupR
#print axioms YM.Massive.Needle.crossP
#print axioms YM.Massive.Needle.purseB
