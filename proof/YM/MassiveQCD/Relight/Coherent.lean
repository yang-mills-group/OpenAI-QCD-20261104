import YM.MassiveQCD.Relight.Seal
import YM.MassiveQCD.Relight.Generic
import YM.MassiveQCD.Tangent.Aisle
/-! # Rotate with respect to `Honest` occupancy; preserve weight classes
 before remasking (uses the robust `relight` eventual equality in the complex range). -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival Shells Shells.Warmlet Finch Stem Grove Calm
-- arbitrary bounded reweight (at most 1). only on licensed column
abbrev UnitCoeff (v:ℕ→ℂ):= ∀ i, ‖v i‖ ≤1
def Coherent (E:Gem c N I) (t:ℝ)(h:I→ℕ):Prop :=∀ (z:ℕ→ℂ),UnitCoeff z→ potion (Stem.income (weight E h z) t)=Stem.income (weight E h z) t
variable (G:Gem c N I) (U:Grid c)(v:I→ℕ)(z:ℕ→ℂ)
lemma coherentW (h:Noted G)(P:I→Prop): Noted (Moss.muteK G P):=by
     constructor
     · intro i; rw [Moss.eitherX]; split; exact h.gauge _; exact fun i k=>congr_arg Subtype.val (map_zero (sways (Lat.rotates N k)))
     · intro i; rw [Moss.eitherX]; split; exact h.num _; exact fun _ _ _=> map_zero _
     intro i; rw [Moss.eitherX]; split; exact h.real i; exact fun U=>map_zero _
lemma mutedLoan (i:I→Prop) (k:I→ℝ)(h:∀ i,Woven (G.addr i).site (G.addr i).support p r (G.view i) (k i))(hx : Ac.Hit (fun i=>(G.addr i).support) p.B k a t):
    let E:= Moss.muteK G i; Licence p a t r E ∧∀ j, Woven (G.addr j).site (G.addr j).support p r (E.view j) (k j):=by
      intro E
      have hh j: Woven (G.addr j).site (G.addr j).support p r (E.view j) (k j):=by
          rw [show E.view j= _ from Moss.eitherX G i j]
          split
          next he=> exact h j
          next _=> exact (Moss.freeK _ _).stretches (Subset.refl _) (h j).travel
      exact ⟨⟨k, Stem.anchorM G k (fun i=> (h i).travel) hx,hh⟩,hh⟩
section thermal
variable {N': ℕ}{S:StepData c f} -- namespace
open ConnectedActivityE6 Pressure Push.SectorMeasure
variable {Γ:Teller su}{x:ℝ}{P:Rep su f}{T':Tube su S}{Q:Target su Γ}{o':Target.Order su a}{H:Cash a x t L Q o' σ T' P}
variable (Y:Fleet H I N)(p':ℂ→I→Grid f→Grid c→EvenA c N) (A:Clusters Y.Bright→RegularAddress c)(χ:Chi)(M:ℕ→Prop) (h:∀ z:ℝ,|z| ≤1 → ∀ i U V,p' z i U V=(z:ℂ)^v i •Y.works i U V) (he:∀ z:ℝ, |z|<1 → (tintF Y (p' z)).Famous ∧ Colorful (tintF Y (p' z)))
set_option quotPrecheck false
local notation "K*"=> depthT Y v
local notation "V*"=> crude Y χ A
local notation "R*"=> Moss.muteK (V*) (fun i=> M (K* i))
include he h
lemma carte [Countable (Clusters Y.Bright)] (p:BudgetPoint)(hP:p.threshold=temp x)(hF:Y.Famous) (hr:0<r)(ho:0≤u)(hA:∀ i,(A i).support=seatP Y.lightF i)(hd:Licence p u η r (R*)) (hY: Colorful Y) (k:ℕ→ℕ): Coherent R* p.threshold (k ∘ (K*)):=by -- syntax
    intro q hq; let f j:=if M j then q (k j) else 0; have hW (i:Grid c):Summable fun j=> (letters (weight (R*) (k ∘ K*) q) p.threshold i j):= permits _ (payments R* _ q (fun i=>hq _) zero_le_one hd) hr ho i; have hh V : letters (weight (R*) (k ∘ K*) q) p.threshold V= fun i=> f (K* i) • Y.honest χ V i:=by
        funext i; rw [earns, Stem.masking, hP]; unfold f; by_cases hm : M (K* i);
        · rw [if_pos hm,if_pos hm,literal_color Y A χ hA hF hY.warp]; rfl -- signature A etc
        rw [if_neg hm,if_neg hm, smul_zero,zero_smul]
    rw [show Stem.income (weight ..) p.threshold=(fun V=>∑' i,f (K* i) • Y.honest χ V i) from funext (fun i=> tsum_congr (fun j=>congr_fun (hh i) j))]; funext i; exact Patron.parade Y χ v p' (fun i hi=>h i hi.le) he f (fun i=> hh i ▸ hW i) i -- exact h via nonshadow
end thermal
end YM.QCD.Relight
#print axioms YM.QCD.Relight.carte
