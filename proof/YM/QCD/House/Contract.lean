import YM.QCD.House.Jamb
import YM.QCD.House.Casks

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
set_option quotPrecheck false
local notation "B"=>radiusB τ
section
-- c not countable assumption tested explicitly
variable (h:Y.Famous)(he:Y.Feasible)(hp:Territory.Gate Y)(hs:Y.speaking)
include h hs
lemma courtB (χ:Chi)(s:Clusters Y.Bright):Measurable (fun V=> Y.furnace χ V s) ∧ LocalOn (seatP Y.lightF s) (fun V=> Y.furnace χ V s):=by
   constructor
   · unfold furnace termP; exact measurable_const.smul (measurable_const.smul (Finset.measurable_fun_prod _ fun i _=> (Y.brass _ _ h hs).2))
   intro V U hV; unfold furnace termP; apply congr_arg; apply congr_arg; exact prod_congr rfl fun i hi=> (Y.brass _ _ h hs).1 V U (agrees_mono hV (subset_biUnion_of_mem (Y.lightF∘ s.2) hi))
omit hs
include hp
lemma sensesP (χ:Chi)(V:Grid c)(s:Clusters Y.Bright):Gated (seatP Y.lightF s) (Y.furnace χ V s):=by unfold furnace termP; apply Territory.club; apply Territory.club; exact gate_prod _ _ _ fun i hi=> gateMon _ _ (subset_biUnion_of_mem (Y.lightF ∘ s.2) hi) _ (Territory.avenueL Y _ _ _ hp h) -- order h?
include he hs
lemma inletC (χ:Chi)(u:Y.Wort)[Countable Y.Bright]: Measurable (fun V=>Y.mission χ V u) ∧ UsesFinal (Pressure.temp τ) (GasP.wound Y.broad u) (fun V=>Y.mission χ V u)∧ ∀ V,Gated (GasP.wound Y.broad u) (Y.mission χ V u):=by
    let K i V:=Y.dawnV χ V i; let X:=GasP.wound Y.broad u
    haveI : Countable (Clusters Y.Bright):=by unfold Clusters; infer_instance
    have hg (p :Support c): Measurable (fun V=>portion Y.lightF (Y.dawnV χ V) p):=by
       unfold portion; apply Measurable.tsum -- shape (∀ z)
       intro z; split
       · unfold termP; exact measurable_const.smul (measurable_const.smul (Finset.measurable_fun_prod _ fun i _=> Y.readableB _ _ h hs))
       exact measurable_const
    let D (V:Grid c):=RG.flags (Pressure.temp τ) V
    have hk : MeasurableSet {V : Grid c| GasP.wagon Y.broad u∧D V∩X=GasP.sweep Y.invD u}:= by
       rw [show {V:Grid c|GasP.wagon _ _∧D V∩X=GasP.sweep Y.invD u}= ⋃ i∈univ.filter (fun i:Support c=> GasP.wagon Y.broad u ∧ i∩X=GasP.sweep Y.invD u), {V|D V=i} from ?_]; exact MeasurableSet.iUnion (fun i=> MeasurableSet.iUnion fun _=>flags_measurable_eq ..)
       ext V; simp only [Set.mem_setOf_eq,Set.mem_iUnion, mem_filter,mem_univ,true_and]; refine ⟨fun ht=>⟨_,ht,rfl⟩,?_⟩; rintro ⟨b,h,rfl⟩; exact h
    refine ⟨Measurable.ite hk (Finset.measurable_fun_prod u fun i _=>?_) measurable_const,?_,fun V=>?_⟩
    · rcases i with i|i; exact Y.readableB i.val _ h hs
      exact (NormedSpace.exp_continuous.measurable.comp (hg i).neg).sub measurable_const
    · intro U V hV hF; unfold mission GasP.motto; refine if_congr ?_ (prod_congr rfl fun i hi=>?_) rfl
      · rw [inter_comm _ X, hF, inter_comm X]
      have hf:facesP Y.broad i⊆X:=subset_biUnion_of_mem _ hi
      rcases i with i|i
      · exact Work.H03.reads_larger (show Y.fullA i.val ⊆X from hf) (ambitS Y _ _ h) U V hV hF
      change NormedSpace.exp _-1= NormedSpace.exp _-1
      apply congr_arg₂ (·-·) _ rfl; apply congr_arg; apply congr_arg; unfold portion; apply tsum_congr; intro z; split
      next hh=>
         unfold GasP.termP; apply congr_arg; apply congr_arg; refine prod_congr rfl fun j hj=> Work.H03.reads_larger (show Y.lightF (z.2 j)⊆_ from (subset_biUnion_of_mem (Y.lightF ∘ z.2) hj).trans (le_trans hh.le (show i≤X from hf))) (ambitS Y _ _ h) U V hV hF
      rfl
    unfold mission motto; split; swap; · exact Fleet.spruce _
    apply gate_prod; intro i hi; have hk : facesP Y.broad i ⊆ X:=subset_biUnion_of_mem _ hi; rcases i with i|i
    · exact gateMon _ _ hk _ (Territory.avenueF Y _ _ _ he hp h)
    refine gate_exp _ _ ?_; have hg:Gated X (portion Y.lightF (Y.dawnV χ V) i):=by
       apply Territory.spearm; intro j; split
       next hx =>
           apply Territory.club; apply Territory.club; exact gate_prod _ _ _ fun a ha=>gateMon _ _ ((subset_biUnion_of_mem (Y.lightF∘j.2) ha).trans (le_trans hx.le (show i ≤X from hk))) _ (Territory.avenueF Y _ _ _ he hp h)
       exact Fleet.spruce _
    simpa using! Territory.club X (-1:ℝ) _ hg
end
end YM.QCD.Loom.Fleet
