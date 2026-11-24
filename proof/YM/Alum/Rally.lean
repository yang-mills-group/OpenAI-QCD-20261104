import YM.Alum.Suds
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Ibis
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
variable {n D i ℓ k m j₀ p w:ℕ}{L:Side}{Hp:Dial D}{Vb z:ℝ}
variable {I:Type}[Fintype I](e v:ℝ)
open Metric
-- collar demand: increasing κ to absorb.L shrinking → L/E etc.
noncomputable def flats (I:Type)[Fintype I](e v:ℝ): Set (I→E4):= closedBall 0 (v/2) ∩ (⋂ i:I,⋂ j:I,⋂ (_ : i≠j), {x:I→E4 | e ≤ ‖x i -x j‖})
local notation "K"=> flats I
lemma compact : IsCompact (flats I e v) := by
   refine (isCompact_closedBall ..).inter_right (isClosed_iInter (fun i=> isClosed_iInter (fun j=> isClosed_iInter (fun _=>?_))))
   exact isClosed_le continuous_const ((continuous_apply i).sub (continuous_apply j)|>.norm)
variable (x:I→E4) (hx:x∈flats I e v)
lemma outward : x∈flats I e v ↔ ‖x‖ ≤ v/2 ∧ ∀ i j:I,i≠j→e ≤ ‖x i-x j‖:=by simp [flats]
lemma profits (y:I→E4)(z:ℝ)(h:0 ≤ z)(hz:∀ i,‖x i-y i‖ ≤ z) : ‖x-y‖ ≤ z:=(pi_norm_le_iff_of_nonneg h).2 hz
include hx
lemma perim (hv:0 ≤ v)(i:I): ‖x i‖ ≤ v/2:=(pi_norm_le_iff_of_nonneg (by linarith)).1 ((outward ..).1 hx).1 i
lemma iris (hv:0 ≤ v)(i j:I)(he:i≠j): x i-x j∈ Oasis e v:=by
    apply disc ((outward ..).1 hx|>.2 i j he); linarith only [perim e v x hx hv i, perim e v x hx hv j, norm_sub_le (x i) (x j)]
lemma noCol (he:0<e): Injective x:=fun i j h=>not_not.mp (fun hp=> (not_le.mpr he) (by simpa [h] using ((outward ..).1 hx).2 i j hp))
lemma puff (y:I→E4)(e' v' u:ℝ)(ht:‖y-x‖ ≤ u)(hu:e'+2*u ≤ e)(hy:v+2*u ≤ v'): y∈flats I e' v':=by
     obtain ⟨hx,hP⟩:=(outward ..).1 hx; refine (outward ..).2 ⟨?_,?_⟩; · linarith only [hx, ht, norm_sub_norm_le y x,hy]
     intro i j he; have ht(i:I):‖y i-x i‖ ≤ u:=(pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) ht)).1 ht i
     have h : ‖x i -x j -(y i-y j)‖ ≤ ‖y j -x j‖+‖y i-x i‖:=by rw [show x i-x j-(y i-y j)=(y j-x j)-(y i-x i) from (by abel)]; exact norm_sub_le ..
     linarith only [norm_sub_norm_le (x i-x j) (y i-y j),ht i,ht j,h,hP i j he,hu]
omit hx
open Grammar Tarot Tarot.Vista
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Clover
variable (P: Fin n→ Glyph D) (hb:0<e)(hV:0<v)
noncomputable def candle (y:Fin n→E4) :ℂ:= UV.Free.wick (menuP P) (points y) (fun j=> (P j).material)
local notation "G"=> Fin n
local notation "K'"=> flats (Fin n) e v
local notation "Q"=> weightsT P
local notation "W"=> codes P
local notation "Z"=> menuP P
include hb
lemma smooth (y:G→ E4)(h:y∈K'):ContDiffAt ℝ ω (candle P) y:=by
    have ht: points y∈conf n:= noCol _ _ y h hb
    let j : (G→E4)≃L[ℝ] Points n:=(PiLp.continuousLinearEquiv 2 ℝ (fun _=> E4)).symm -- name.Verify
    exact (UV.Free.Sip.smoothC ht (menuP P) (fun i=> (P i).material.val)).comp y j.contDiff.contDiffAt
structure Faucet (P:G→ Glyph D)(H:ℝ) : Prop where
    save y:y∈flats (Fin n) e v→∀ p ⊆(crest (id:Fin n→Fin n)), ‖saves (weightsT P) (menuP P) (codes P) y id p‖ ≤ H
    compZ y:y∈flats (Fin n) e v→∀ p:Finset (Fin n), ‖Clover.compZ (weightsT P) (menuP P) (codes P) y (List.finRange n) p‖ ≤H
    house y:y∈flats (Fin n) e v→ ‖fderiv ℝ (fun x=> UV.Free.wick (menuP P) (points x) (fun j=>(P j).material)) y‖ ≤H
#print Faucet
lemma dawn : ∀ᶠ H:ℝ in atTop, Faucet e v P H:=by
     let U(x:G → E4):= fderiv ℝ (candle P) x
     have hf:ContinuousOn (fun x=> ‖U x‖) K':=by intro x hx; exact (((smooth e v P hb x hx).fderiv_right (m:=0) le_top).continuousAt.norm).continuousWithinAt
     obtain ⟨C,h⟩:= (compact (I:=G) e v|>.image_of_continuousOn hf).bddAbove
     have hκ(i:Finset G):∀ᶠ H in atTop,∀ x∈ K', ‖Clover.compZ Q Z W x (List.finRange n) i‖ ≤ H:=by
           obtain ⟨C,h⟩:= ((compact (I:=G) e v).image_of_continuousOn (show ContinuousOn (fun x=> ‖Quills.Clover.compZ Q Z W x (List.finRange n) i‖) K' from (fun x hx=> ((Quills.Pulp.continuity Q Z W x i (List.finRange n) ((noCol e v x hx hb).injOn)).norm).continuousWithinAt))).bddAbove; exact (eventually_ge_atTop C).mono fun z hz x hx=> (h ⟨x,hx,rfl⟩).trans hz
     have hS(i:Finset G):∀ᶠ H in atTop,∀ x∈ K', i ⊆ crest (id: G→ G)→‖saves Q Z W x id i‖ ≤ H:=by
            have hp:i⊆crest (id:G→G):=fun x _=>(exists_fix ..).2 ⟨x,rfl⟩; have h: ContinuousOn (fun x=> ‖saves Q Z W x id i‖) K':= fun x hx=> ((Quills.Pulp.enhance Q Z W x i id ((noCol e v x hx hb).injOn) hp).norm).continuousWithinAt; obtain ⟨C,h⟩:= ((compact (I:=G) e v).image_of_continuousOn h).bddAbove; exact (eventually_ge_atTop C).mono fun z hz x hx _=> (h ⟨x,hx,rfl⟩).trans hz
     filter_upwards [eventually_ge_atTop C,eventually_all.mpr hκ,eventually_all.mpr hS] with H hz hκ hS using ⟨fun x hx i hp=> hS i x hx hp, fun x hx i=> hκ i x hx,fun x hx=> (h ⟨x,hx,rfl⟩).trans hz⟩
-- permit var.EXPLICIT only.Ball gives Lipschitz compensated on interiors.
variable (e' v' H:ℝ)(hz:Faucet e v P H)
include hz
lemma strenuous (x y:G→ E4)(hx:x∈ flats G e' v')(hu:e+2*‖y-x‖ ≤e')(hX:v'+2*‖y-x‖≤v): ‖candle P y-candle P x‖ ≤ H * ‖y-x‖:=by
      let V:= closedBall x ‖y-x‖; have hf: V⊆ K':=fun i hi=> puff e' v' x hx i e v _ (by simpa [mem_closedBall,dist_eq_norm_sub,V] using hi) hu hX
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun i hi=>(show HasFDerivWithinAt (candle P) _ V i from (((smooth e v P hb i (hf hi)).differentiableAt (by decide)).hasFDerivAt.hasFDerivWithinAt))) (fun i hi => hz.house i (hf hi)) (convex_closedBall ..) (mem_closedBall_self (by positivity)) (by rw [Metric.mem_closedBall,dist_eq_norm_sub]); -- rewrite goal etc.
end YM.Intag.Ibis
#print axioms YM.Intag.Ibis.strenuous
#print axioms YM.Intag.Ibis.dawn
