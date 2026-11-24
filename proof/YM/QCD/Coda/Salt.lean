import YM.QCD.Coda.Vent
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings Grass Kites Flume Tee YM.Next.Free Oasis Pressure SectorMeasure Presented
open Jets Beam Villa AbsoluteSums Gas Greenbelt Patron
variable {n f c:Side}{N j k B B':ℕ}{P:Teller su}
variable {S:Flight j k}{H:f.val=c.val*S.L.val}{w d v u t p C A b m a q W β δ:ℝ} {X:Grid f→Sheet f}
section books
variable {K:StepData c f}{T:Tube su K}{Y:BudgetPoint}
variable {Q:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}{ι:Type}
variable {L:Side}{R:Rep su f} {Z: Cash W d v L Q o C T R}
open scoped PhysicalNext.Repeat.Greenbelt
open GasP Ursell
lemma turquoise (U:Fleet Z ι N)(χ:Chi)(V:Grid c)(B:Clusters U.Bright→RegularAddress c)(hp:∀ i,(B i).support=seatP U.lightF i)(hY: flags (Pressure.temp d) V=∅)(hx:Mercy U χ):
   let t i:=(crude U χ B).view i V; U.honest χ V=t ∧ Summable t ∧ (∑' i,U.ket χ V i)=1 ∧ indigo c N (∑' i,t i)=0 :=by
   intro t
   have hp':U.honest χ V=t:=funext fun i=>by rw [← literalX U B χ hp hx.famous hx.graph]; exact masked_eq _ _ _ _ (show Healthy _ _ _ from by unfold Healthy; rw [hY]; simp)
   have hh: Summable t:=hp' ▸ (hx.budgets _).1; refine ⟨hp',hh,?_,?_⟩
   · rw [tsum_eq_single ∅]; unfold ket; rw [hY,if_pos,prod_empty]; simp [Set.PairwiseDisjoint, Set.Pairwise]
     intro i hi; obtain ⟨p,hp⟩:=nonempty_iff_ne_empty.mpr hi; unfold ket; rw [hY]; apply if_neg; intro h; obtain ⟨q,hq⟩:=(fuel U p).1; exact notMem_empty q ((show _ from h.2) ▸ (mem_biUnion.mpr (show _ from ⟨p,hp,hq⟩))) -- eligibility
   have hv i: indigo _ _ (t i)=0:=by change (mud _).im=_; rw [realP (upstream U B χ hx.graph|>.real i V)]; simp
   rw [(indigo c N).map_tsum hh]; simp_rw [hv]; exact tsum_zero
open scoped Matrix.Norms.Frobenius
-- cost Vac. no leak through probe sign. solar is independent
abbrev gala (T:Tube su K)(R: BudgetPoint)(η:ChartRatio su)(s:ℝ)(χ:Chi)(β w:ℝ)(F:Forest K.ratio):ℝ:= Real.log (Fare.solar F η β)- Real.log (Greenbelt.prism T s χ w (1:Grid c) F).blank.plate.det/2
lemma wool (T:Tube su K) (R: BudgetPoint) (η: ChartRatio su)(s:ℝ)(χ:Chi)(X:Grid c)(u δ:ℝ) (he:Y.threshold=Pressure.temp s)(hg: flags Y.threshold X=∅)(h:LocalRatio η)(hv:0 < β)(F:Forest K.ratio): Matter.overhead (Greenbelt.prism T s χ u X F) (trimP T R δ β 0) η=Real.exp (gala T R η s χ β u F-β* secondTerm T.low T.down X) :=by
     let x:= Greenbelt.prism T s χ u X F
     change Matter.overhead x (Pane.virgin T R β) η= _; rw [Fare.overdraft F T β R Y x η he hg]; let P':=Real.log (Fare.solar F η β); let A':=Real.log x.blank.plate.det / 2; let B:= β* secondTerm T.low T.down X
     have hh : gala T R η s χ β u F=P'-A':=rfl; rw [hh,show P'-A'-B=P'+(-B-A') from (by ring),Real.exp_add]; change Fare.solar F η β * Real.exp _ = _* _; rw [show Real.exp P'= _ from Real.exp_log (Fare.sun F η β hv h)]; congr 1; unfold B; rw [neg_mul]; rfl
end books
end YM.QCD.Coda
