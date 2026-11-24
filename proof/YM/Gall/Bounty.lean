import YM.Patria.Lawn
import YM.Oriole.Nett
import YM.Further.LOCAL_LOG_JETS.Series
/-! Harvest root Tally derivatives under pose budget. No increasing-volume chart constants. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a v A D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open MultiNext.SignedSource PhysicalNext.JointLoad Lyre Metric
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised Display Beacon Pipes Further.LogJets
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
namespace Gall
variable (o:Site c)(P:BudgetPoint)(X:Grid c→Lat.Fields c 6)
structure Tutor (v:ℝ)(n j:ℕ)(a:ℝ): Prop where
   smooth: Chart P.order X 1
   large: ∀ l,List.length l ≤ P.order → (∀ i∈l,P.dirBound o i) → ‖leftDerivs X l 1‖ ≤ a
   fortune:∀ l,List.length l ≤ P.order → (∀ i∈l,P.dirBound o i) → ∀ i<j, ‖framesF (purseX o n v) (mantel i (leftDerivs X l 1))‖ ≤ a
variable {X}
private lemma heal (V:V₀)(H:flags P.threshold V=∅) (W: Support c): Healthy P.threshold W V:=by unfold Healthy; rw [H]; simp
lemma courtesy {W: Support c}(h:Flame X P W o v n j a)(ht:1 ≤ v): Tutor o P X v n j a:=by
    let U: V₀:=1; have hT: flags P.threshold U=∅:=(show flags P.threshold=ᶠ[𝓝 U] (fun _=>∅) from allflag P).eq_of_nhds; have hk:= heal P U hT W
    have hx:= h.sight.use _ hk
    refine ⟨hx,fun l hl hd=> (visible _ o _ ht).trans (h.sight.pole _ hk l hl hd),fun l hl hd i hi=> ?_⟩
    let F: G₀→L[ℝ]G₀:= (framesF (purseX o n v)).comp (mantel i)
    change ‖F (leftDerivs X l 1)‖ ≤ _
    rw [←left_linear F _ hx hl]; exact (h.issues _ hi).2 _ hk l hl hd
lemma of_eq {W:Grid c→Lat.Fields c 6}(h:Tutor o P W v n j a)(he:X=ᶠ[𝓝 (1:Grid c)] W): Tutor o P X v n j a:=by
    have hg:Tendsto (increment (1:Grid c)) (𝓝 0) (𝓝 1):=by simpa [increment] using (increment_cont (1:Grid c)).tendsto 0
    have hm:= he.comp_tendsto hg
    exact ⟨h.smooth.congr_of_eventuallyEq hm,fun l hl hd=>by rw [left_congr l 1 hm]; exact h.large _ hl hd,fun l hl hd i hi=>by rw [left_congr l 1 hm]; exact h.fortune _ hl hd i hi⟩
lemma together {W:Grid c→Lat.Fields c 6}(h:Tutor o P X v n j a)(hh:Tutor o P W v n j t): Tutor o P (X+W) v n j (a+t):=by
    refine ⟨h.smooth.add hh.smooth,fun l hl hd=>?_,fun l hl hd i hi=>?_⟩
    · rw [Push.Local.left_add l h.smooth hh.smooth hl]; exact (norm_add_le ..).trans (add_le_add (h.large l hl hd) (hh.large l hl hd))
    rw [Push.Local.left_add l h.smooth hh.smooth hl,map_add,map_add]; exact (norm_add_le ..).trans (add_le_add (h.fortune l hl hd i hi) (hh.fortune l hl hd i hi))
variable {I:Type} (Y:I→ Support c)(Z:I→ Grid c→ Lat.Fields c 6){f:I→ℝ}
lemma balance (h:∀ i, Flame (Z i) P (Y i) o v n j (f i))(hf:Summable f)(hh:∑' i,f i ≤ D)(hv:1≤v): Tutor o P (fun U=>∑' i, Z i U) v n j D:=by
    obtain ⟨W,hW,hO,H⟩:= _root_.mem_nhds_iff.mp (allflag (c:=c) P)
    change W ⊆ {U:V₀|flags P.threshold U=∅} at hW; have hQ U (hx:U∈W) S:= heal P U (hW hx) S
    have hm:Termwise P.order W Z:=by
       refine ⟨fun i U hU=>(h i).sight.use U (hQ _ hU _),fun l hl=>?_⟩
       let t:= P.threshold + l.toFinset.sum fun a=> ‖a‖; have ht : 0<t:= add_pos_of_pos_of_nonneg P.threshold_pos (sum_nonneg fun _ _=> norm_nonneg _)
       have hr(x)(hx:x∈l): ‖x‖ ≤ t:= (single_le_sum (fun i _=> norm_nonneg i) (List.mem_toFinset.mpr hx)).trans (le_add_of_nonneg_left P.threshold_pos.le)
       let b:= t/P.threshold; have hb : 0<b:= div_pos ht P.threshold_pos
       let l':=l.map fun a=> b⁻¹ • a; have hT : l'.map (b • ·)=l:= by simp[l',List.map_map,comp_def,smul_smul,hb.ne']
       have he : List.length l' ≤ P.order:=by simpa[l']
       have hx : ∀ i∈l',P.dirBound o i:= by
          intro x hh e; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hh; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hb).le]; apply (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans (hr _ ha)) (inv_pos.mpr hb).le).trans; rw [show b⁻¹*t=P.threshold from (by unfold b; field_simp)]; exact le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp))
       refine ⟨fun i=> b^l'.length*f i,hf.mul_left _,fun i U hU=>?_⟩
       rw [← hT,Push.Local.left_homogeneous l' ((h _).sight.use U (hQ _ hU _)) he,norm_smul,Real.norm_of_nonneg (pow_pos hb _).le]; exact mul_le_mul_of_nonneg_left ((visible _ o _ hv).trans ((h i).sight.pole U (hQ _ hU _) l' he hx)) (pow_pos hb _).le
    obtain ⟨hG,hp⟩:= Termwise.smooth_exchange hO hm _ H
    have ha i:=courtesy o P (h i) hv
    refine ⟨hG,fun l hl hd=>?_,fun l hl hd i hi=>?_⟩
    · rw [hp l hl]; have h:=hf.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>(ha i).large _ hl hd); exact (norm_tsum_le_tsum_norm h).trans ((h.tsum_le_tsum (fun i=> (ha i).large _ hl hd) hf).trans hh)
    rw [hp l hl]; let Q: G₀ →L[ℝ] G₀:= (framesF (purseX o n v)).comp (mantel i)
    change ‖Q (∑' i,_)‖ ≤ _; rw[Q.map_tsum (hm.sums l hl 1 H)]; have ht (j:I): ‖Q (leftDerivs (Z j) l 1)‖ ≤ f j:=(ha j).fortune _ hl hd _ hi
    have hq:= hf.of_nonneg_of_le (fun _=>norm_nonneg _) ht; exact (norm_tsum_le_tsum_norm hq).trans ((hq.tsum_le_tsum ht hf).trans hh)
end Gall
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Gall.balance
