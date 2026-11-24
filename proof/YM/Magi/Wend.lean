import YM.Magi.Pish
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open Function Lattice RG Pressure MeasureTheory Finset QCD Kites Kit Port Flume
open Grass Lat Play QCD.Bera
open Stitch Plate Loom Loom.Fleet Sway OrbitG Ribbon Rebus Creek Cove Apron Apron.Grove Cupola QCD.Acre QCD.Acre.Rails
open Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I] {l φ k B P A A':ℕ} {v α s t:ℝ}
local notation "F0"=> (Keys c N)
open QCD.Brick QCD.Dust -- edit
-- payload color for actual evaluator. does not insert new face handshake.
namespace LampV
-- support charges for (almost) arbitrary repricing at end, no loss of flag rights. Require ANY partitions before.K. mℓ≥? ℓ≥ 1 monotone.Space.
variable (L:Side)(N:ℕ){z t' d s Λ ξ κ' ε α' τ:ℝ}{n m l b k':ℕ}
open Bera QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby QCD.Acre.Stratum.MarchQ.Suburb
open Suburb.Melt.Lobby.LeaseV LeaseV.Advent Suburb.Affair.Nimbus
variable (p:I→Site c)(q:I→Bool) (T: Finset (Finset I)) (E: Reel c N I J)(S₇:Finset J)(P:BudgetPoint)(F:Film c N I D)
open Push Push.AbsoluteSums Metric
variable {a b1 C M γ η :ℝ} (w:I→ℝ)
set_option quotPrecheck false
local notation "Iv"=>T
-- abstraction.Sector separation if not same Tile.Plausible from utility below.
-- install ghosts when ANY T components.spark.Genuine needed. Permit correction delta at those later. occ.Item.Real.
variable {Λ S:ℝ}
variable (hT:Bearing p q T E S₇ L l m v τ Λ P S F)
local notation "γ₀"=> baseTZ P.B
local notation "T!"=> parish p T γ₀
noncomputable abbrev outcasts:= {i:parish p T (baseTZ P.B)// i.val∉ S₇.image E.z}
local notation "Qo"=> outcasts N p T E S₇ P
noncomputable def zeroLane (l:ℕ): Reel c N I (outcasts N p T E S₇ P) :=⟨(rayA p T (baseTZ P.B) (orbital l*P.B)) ∘ Subtype.val,Subtype.val∘ Subtype.val, fun _ =>0⟩
local notation "Lp"=>zeroLane N p T E S₇ P l
local notation "K0"=> Keys c N
local notation "X!"=> Ribbon.Spine I
lemma ghostsP (V:Grid c)(i:Qo) : Reel.mist Lp t i V=(0:Patio (K0⊕ Ribbon.Spine I)):=by
      unfold Reel.mist; by_cases h:Healthy t ((Lp).addr i).support V; · rw [masked_eq _ _ _ _ h]; rfl
      rw [masked_ne _ _ _ _ h]
variable (hC:∀ i∈T,i.card≤ l)
include hC
lemma lanesP (V:Qo)(i:I)(h:i∈ (Lp).z V): (Lp).z V∈T ∧ (Lp).z V=V.val.val ∧ ((Lp).z V).Nonempty ∧ halo (refuge l*P.B+10) {p i}⊆ ((Lp).addr V).support ∧ ((Lp).addr V).support⊆ halo (majorT l*P.B) {p i}:=by
    let u:= (rayA p T γ₀ (orbital l*P.B) V.val).site; let a:=P.B; have hh:=P.B_pos; have ht:=configurationD l _ hh; have hg: separation u (p i)≤ l*(110*P.B):= brood_unit _ _ _ _ hC hh V.val i h
    refine ⟨V.val.2.1,rfl,V.val.2.2.1,subray _ _ _ _ _ hg (?_),subray (l*(110*P.B)) _ _ _ _ ((separation_comm ..).le.trans hg) (?_)⟩
    · exact ht.2.2.2.1
    exact ht.2.2.2.2.1
local notation "S₀"=> S₇.disjSum (Finset.univ:Finset (Qo))
local notation "Yp"=>plusR E Lp
open SC FlareV
lemma beads : Reel.Book p q (Lp):=⟨fun i=>i.val.2.2.1,fun i j hj=> by obtain ⟨u,hu,rfl⟩:=mem_image.mp hj; exact (lanesP N p T E S₇ P hC i u hu).2.2.2.1 (halo_subset _ _ (mem_singleton_self _)), fun _=> measurable_const,fun _ _ _ _=> rfl,fun _ _=>⟨polite_nil ..,clad.nil _⟩,fun _ _ _=>map_zero _⟩
include hT
lemma starvedV : Bearing p q T (Yp) S₀ L l m v τ Λ P S F :=by
      have hv:= hT.rise; refine ⟨⟨?_, ?_, ?_,?_,?_,?_⟩,?_,hT.flag,hT.cost⟩
      · rintro (i|i) hi (j|j) hj h
        · exact congr_arg Sum.inl (hv.mug (inl_mem_disjSum.mp hi) (inl_mem_disjSum.mp hj) h)
        · exact (j.2 (mem_image.mpr ⟨i,inl_mem_disjSum.mp hi,h⟩)).elim
        · exact (i.2 (mem_image.mpr ⟨j,inl_mem_disjSum.mp hj,h.symm⟩)).elim
        exact congr_arg Sum.inr (Subtype.ext (Subtype.ext h))
      · rintro (i|i) hi; exact hv.arcs _ (inl_mem_disjSum.mp hi); exact i.val.2
      · rintro (i|i) hi j hj; exact hv.brood i (inl_mem_disjSum.mp hi) j hj; exact (lanesP N p T E S₇ P hC i j hj).2.2.2.2
      · rintro (i|i) hi j hj; exact hv.shield i (inl_mem_disjSum.mp hi) j hj; exact (lanesP N p T E S₇ P hC i j hj).2.2.2.1
      · rintro (i|i) hi j hj; exact hv.domain i (inl_mem_disjSum.mp hi) j hj; exact fun _ _ h=> rfl
      · rintro (i|i) hi V; exact hv.degree i (inl_mem_disjSum.mp hi) V; exact Submodule.zero_mem _
      have hl: SC.Valve Lp p q v P.threshold P.B (3/32) 0 (fun _=>1):=by
          refine ⟨beads N p q T E S₇ P hC,fun _=>0,fun i V=>?_,fun i=>?_⟩
          · rw [ghostsP N p T E S₇ P V i]; unfold Tablet.credits; rw [map_zero,QCD.Cove.load_zero]
          apply budget_of_sum (fun i=>?_) (fun s=>?_); all_goals simp
      have hm:= mixH p q E Lp hT.boost hl; rw [add_zero] at hm
      convert hm using 1; funext i; rcases i with i|i; · simp only [boosts,inl_mem_disjSum,plusR,Sum.elim_inl] -- adapt
      rw [boosts,if_pos (Or.inl (inr_mem_disjSum.mpr (mem_univ _)))]; rfl
lemma absentsP (T':Finset I)(h:T'∈T)(hp:Ac.Spark (Play.Camp.Ray p (baseTZ P.B)) T') : ∃ i∈ S₀,(Yp).z i=T':=by
      by_cases hz:T'∈ S₇.image E.z; · obtain ⟨i,hi,he⟩:=mem_image.mp hz; exact ⟨Sum.inl i,inl_mem_disjSum.mpr hi,he⟩
      let i:parish p T (baseTZ P.B):= ⟨T',h,hp⟩; exact ⟨Sum.inr (⟨i,hz⟩:Qo),inr_mem_disjSum.mpr (mem_univ _),rfl⟩
omit hT hC
lemma slidesV (V:Grid c) (s:Finset I) : sled Yp S₀ s V= sled E S₇ s V:=by unfold sled; simp_rw [sum_filter]; rw [sum_disjSum]; simp only [plusR,Sum.elim_inl,Sum.elim_inr,zeroLane,Pi.zero_apply,ite_self,sum_const_zero,add_zero]
lemma vouch {h:ℕ}(D:Quince c N I)(r s v ε:ℝ)(hp:Moor p T E S₇ D P.B l h m P.threshold r v s ε) :Moor p T Yp S₀ D P.B l h m P.threshold r v s ε:= ⟨hp.syntaxP,hp.height,fun i hi he B h H=> by rw [slidesV]; exact hp.mirrors _ hi he _ h H⟩
include hT hC
lemma vignette (hR:1 ≤Λ)(hv:1≤ v)(U:Grid c) : Reel.rope Yp P.threshold U= Reel.rope E P.threshold U:=by
      -- direct. summable along sums.S.
      have hg i:1 ≤ boosts T E S₇ Λ i:=by unfold boosts; split; exact le_rfl; exact hR
      let f i:= Reel.mist E P.threshold i U; have hh:Summable f:= flyer p q E hT.boost (by norm_num) hg hv U
      let h: Qo →Patio ((Keys c N)⊕ Ribbon.Spine I):=0
      have he: (fun i=> Reel.mist Yp P.threshold i U)= Sum.elim f h:=by
           funext i; rcases i with i|i; · rfl
           exact ghostsP N p T E S₇ P U i
      unfold Reel.rope; rw [he]; exact (hh.hasSum.sum (f:=Sum.elim f h) (b:=0) hasSum_zero).tsum_eq.trans (add_zero _)
end LampV
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.LampV.starvedV
#print axioms YM.MassiveQCD.Cape.LampV.absentsP
#print axioms YM.MassiveQCD.Cape.LampV.vignette
