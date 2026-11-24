import YM.Cape.Stove
import YM.Mills.Vivid
/-!
# Reboxing E's at a common parent on actual fields.
 Indicator sharpening exactly reimbursed via Lure incidences. Through not required of these.
 An element may have reps even if the taxable support yields identically zero masked amplitude.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch Creek SC
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I]
variable (p:I→Site c)(q:I→Bool) (F: Film c N I D)(M: Patron.Rail c N U) (E: Reel c N I J)
variable {t v α s h u κ a A b m:ℝ}
local notation "K"=> Keys c N
local notation "Xk"=> Ribbon.Spine I
variable (hz: Reel.Book p q E)
-- ticket.E opaque meet. map covers support or all mist zero. stash archive at new roots.
structure Lake (R:Type)(t:ℝ) where
    addr:R→RegularAddress c
    z:R→Finset I
    send:J→Option R
variable (X:Lake (c:=c) (I:=I) (J:=J) R t)
structure Lake.Pillar : Prop where
    zU i: (X.z i).Nonempty
    stamp i:(X.z i).image p⊆(X.addr i).support
    tapes i (j:R)(h:X.send i=.some j): E.z i=X.z j
    brim i (j:R) : X.send i=.some j → (RG.inspected (E.addr i).support ⊆ (X.addr j).support) ∨ Reel.mist E t i=0
-- primary check uses *any* enclosing W. Tax increasing paid.K.Weak...
noncomputable abbrev Gate (r:Option R):= {i:J// X.send i=r}
noncomputable def riseP (i:R)(V:Grid c):=∑' j: Gate X (.some i),Reel.mist E t j.val V
noncomputable def brightP : Reel c N I R:=⟨X.addr,X.z,riseP E X⟩ -- color
noncomputable abbrev dullX:= Gate X none
noncomputable def reelShot : Reel c N I (Gate X none):=⟨E.addr ∘ Subtype.val,E.z ∘ Subtype.val,E.mark ∘ Subtype.val⟩
noncomputable def plusR (F:Reel c N I D): Reel c N I (J⊕D):=⟨Sum.elim E.addr F.addr, Sum.elim E.z F.z,Sum.elim E.mark F.mark⟩
noncomputable def unitR:= plusR (brightP E X) (reelShot E X)
local notation "L₀"=> brightP E X
local notation "W"=> reelShot E X
local notation "Kᴿ"=> unitR E X
variable {ξ:J→ℝ} {n:ℕ}
lemma flyer (Y :Reel c N I J) (hv:Valve Y p q v t n α s ξ)(ha:0≤α)(hξ:∀ i,1≤ ξ i)(ht:1≤v)(V:Grid c) : Summable fun i=> Reel.mist Y t i V:=by
    obtain ⟨f,hf,hV⟩:=hv.back
    let k i:= ξ i*f i; have he(i):0 ≤ f i:=(Creek.load_nn ..).trans (hf i V); have ht'(i):f i ≤ k i:=le_mul_of_one_le_left (he i) (hξ _)
    apply Summable.of_norm_bounded (f:=fun i=>Reel.mist Y t i V) (Loom.fishes _ _ hV (fun i=> (he i).trans (ht' i)) ha (fun i _=>⟨_,(Y.addr i).anchor⟩)) fun i=>?_ -- signature
    let g:K⊕ Ribbon.Spine I→ℝ:= Stitch.Tablet.chip v K (Ribbon.Spine I); let x:= Reel.mist Y t i V
    have hx:‖x‖ ≤ Tablet.credits v x:=by
        change ‖x.val‖≤ Creek.load g x.val; have he:∀ i,1≤g i:=Sum.rec (fun _=>ht) (fun _=>le_rfl)
        rw [dry g (fun i=>zero_lt_one.trans_le (he i)),Grass.norm_def]; refine sum_le_sum fun j _=>?_ ; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_prod fun _ _=> he _)
    exact hx.trans ((hf _ V).trans (ht' i))
variable (hp:X.Pillar p E) (hE:∀ V,Summable fun i=> Reel.mist E t i V)
include hz
lemma upM (i:J)(V:Grid c) : lights (E.z i) (E.addr i).support p q (Reel.mist E t i V):=by
    unfold Reel.mist; by_cases hv:Healthy t (E.addr i).support V; rw [masked_eq _ _ _ _ hv]; exact hz.stage i V; rw [masked_ne _ _ _ _ hv]; exact ⟨polite_nil ..,clad.nil _⟩
omit hz
lemma MaskR (O:Support c)(T:Grid c→Tine c N I)(h:LocalOn O T): UsesFinal t O (masked t O T):=by
    intro U V he ht; by_cases hM:Healthy t O U
    · rw [masked_eq _ _ _ _ hM,masked_eq _ _ _ _ (?_:Healthy t O V)]; exact h U V he; exact disjoint_iff_inter_eq_empty.mpr (ht.symm.trans (disjoint_iff_inter_eq_empty.mp hM)) -- Fuel
    rw [masked_ne _ _ _ _ hM,masked_ne _ _ _ _ (?_:¬Healthy t O V)]
    exact fun hv=> hM (disjoint_iff_inter_eq_empty.mpr (ht.trans (disjoint_iff_inter_eq_empty.mp hv)))
include hz hp hE
lemma lighthouse (i:R)(V:Grid c): lights (X.z i) (X.addr i).support p q (riseP E X i V):=by
    have hx(j: Gate X (.some i)): lights (X.z i) (X.addr i).support p q (Reel.mist E t j.val V):=by
       rcases hp.brim j.val i j.2 with h|h; · rw [← hp.tapes _ _ j.2]; obtain ⟨hx,hQ⟩:=upM p q E hz _ V; exact ⟨hx,hQ.raise (limitsMon _ _ (subset_union_left.trans h))⟩
       rw [h,Pi.zero_apply]; exact ⟨polite_nil ..,clad.nil _⟩
    refine ⟨polite_tsum fun j=> (hx j).1,fun t'=>?_⟩
    let T:=Gate X (.some i); let W' (j:T) := pluck K t' (Reel.mist E t j.val V)
    let P:=region (limits (F:=N) (X.addr i).support)
    exact (Creek.Stays.Shut _).mem_of_tendsto (f:=fun s:Finset T=>∑ j∈s, W' j) (b:=atTop) ((pluck K t').hasSum ((hE V).comp_injective (Subtype.val_injective (p:=fun j=> X.send j=.some i))).hasSum) (Eventually.of_forall fun s=> P.sum_mem (fun j _=> (hx j).2 t')) -- limits binder
variable [Countable J]
lemma reading : Reel.Book p q L₀:=by
    refine ⟨hp.zU,hp.stamp,fun i=>Measurable.tsum (fun j=>masked_measurable _ _ _ (hz.permit _)),?_,fun i V=>lighthouse p q E hz X hp hE i V,?_⟩
    · intro i U V h; apply tsum_congr; intro j; rcases hp.brim j.val i j.2 with hv|hv; exact RG.UsesFinal.allReads t (E.addr j.val).support (Reel.mist E t j.val) (MaskR _ _ (hz.room j.val)) U V (agrees_mono h (coe_subset.mpr hv)); rw [hv,Pi.zero_apply, Pi.zero_apply]
    intro i V g; let D:= (parcelColor N g I).toLinearMap.toContinuousLinearMap
    change D (∑' j:Gate X (.some i), Reel.mist E _ _ _) = _; rw [D.map_tsum (show Summable (fun j:Gate X (.some i)=> Reel.mist E t j.val (gauge g V)) from (hE _).comp_injective Subtype.val_injective)] -- explicit j
    refine tsum_congr (fun j=>?_); unfold Reel.mist;  have hk: Healthy t (E.addr j.val).support (gauge g V) ↔ Healthy t (E.addr j.val).support V:=by simp [Healthy]
    by_cases hV:Healthy t (E.addr j.val).support V; rw [masked_eq _ _ _ _ (hk.mpr hV),masked_eq _ _ _ _ hV]; exact hz.tint j.val V g
    rw [masked_ne _ _ _ _ (mt hk.mp hV),masked_ne _ _ _ _ hV]; exact map_zero D
omit [Countable J] hp hE
lemma chocolate : Reel.Book p q W:=⟨fun j=>hz.stays j.val,fun j=>hz.stamp j.val,fun j=>hz.permit j.val,fun j=>hz.room j.val,fun j=>hz.stage j.val,fun j=>hz.tint j.val⟩
lemma powerV (Y':Reel c N I D)(he:Reel.Book p q Y'): Reel.Book p q (plusR E Y'):=by
    constructor
    all_goals rintro (i|j)
    all_goals first|exact hz.stays i|exact he.stays j|exact hz.stamp i|exact he.stamp j|exact hz.room i|exact he.room j|exact hz.permit i|exact he.permit j|exact hz.stage i|exact he.stage j|exact hz.tint i|exact he.tint j
omit hz
-- Soft lure after; budgets from archive vault.
noncomputable def lured : Lure c N I R:=⟨fun i=> (X.addr i).support,fun i V=>riseP E X i V - Reel.mist (brightP E X) t i V,X.z⟩
include hz hp hE
lemma summerC [Countable J] : Lure.On p q (lured E X) t:=by
    have hr:=reading p q E hz X hp hE
    let f(i:R):= (X.addr i).support; let T:= lured E X
    refine ⟨fun i U V hu hx=> congr_arg₂ (·-·) (hr.room i U V hu) (MaskR _ _ (hr.room i) U V hu hx), fun i=> (hr.permit i).sub (masked_measurable _ _ _ (hr.permit i)),fun i V h hV=> h (?_:T.wick i V=0),?_,?_,hp.stamp,hp.zU⟩
    · change Healthy t (f i) V at hV; change riseP E X i V-masked t (f i) _ V=0; rw [masked_eq _ _ _ _ hV]; exact sub_self _
    · intro i V; change lights _ _ _ _ (_-_); rw [sub_eq_add_neg]; obtain ⟨hx,hQ⟩:= lighthouse p q E hz X hp hE i V; obtain ⟨hv,hS⟩:=upM p q (L₀) hr i V; exact ⟨hx.lays hv.minus,hQ.plus hS.neg⟩
    · intro i V g; have hk: Healthy t (f i) (gauge g V) ↔ Healthy t (f i) V:=by simp [Healthy]
      change parcelColor _ _ _ ((L₀).mark i (gauge g V)-masked t (f i) ((L₀).mark i) (gauge g V)) = (L₀).mark i V-masked t (f i) ((L₀).mark i) V; rw [map_sub,show parcelColor _ _ _ _ =_ from hr.tint i V g]; apply congr_arg; by_cases hv:Healthy t (f i) V; rw [masked_eq _ _ _ _ (hk.mpr hv),masked_eq _ _ _ _ hv]; exact hr.tint i V g
      rw [masked_ne _ _ _ _ (mt hk.mp hv),masked_ne _ _ _ _ hv,map_zero]
-- checkpoint relative equivalence on entire algebra.
omit hz hp [Countable J]
lemma reportOptions [Finite R] (V:Grid c): Reel.rope E t V= Reel.rope Kᴿ t V+ ∑' i,(lured E X).wick i V:=by
    let u := fun i=> Reel.mist E t i V; let f : Option R→ Tine c N I:= fun r=>∑' i:Gate X r,u i.val
    have hu:Reel.rope E t V=∑' i,f i:= ((hE V).hasSum.tsum_fiberwise X.send).tsum_eq.symm
    have hr : HasSum (fun i=>Reel.mist Kᴿ t i V) (Reel.rope L₀ t V+Reel.rope W t V):= HasSum.sum (f:=fun i=>Reel.mist Kᴿ t i V) (show HasSum (fun i=>Reel.mist L₀ t i V) _ from (show Summable (fun i=>Reel.mist L₀ t i V) from Summable.of_finite).hasSum) ((hE V).comp_injective (Subtype.val_injective (p:=fun i=> X.send i=none))).hasSum
    haveI:= Fintype.ofFinite R; rw [hu,tsum_fintype,Fintype.sum_option, show Reel.rope Kᴿ t V=_ from hr.tsum_eq]
    change Reel.rope W t V + (∑ i,riseP E X i V)=(_+_)+ ∑' i:R,(riseP E X i V- Reel.mist L₀ t i V); unfold Reel.rope; simp_rw [tsum_fintype (β:=R),sum_sub_distrib]; abel
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.reportOptions
