import YM.MassiveQCD.Cupola.Binding
/-! # Paying SAME layout at extraction, geometry retained through all costs to come
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6 Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt MassiveQCD MassiveQCD.Cupola MassiveQCD.Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{N M:ℕ}
local notation "W'"=> Pipe.Clump S ι
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut Patron
variable (p:EvenA c N→ₐ[ℂ] EvenA c M)(Y₂ : ι→ Grid f→Grid c→EvenA c M)
noncomputable def align : Fleet H ι M:= ⟨Y.limit,Y.ground,Y.fine,Y.window, Y.compat,Y₂⟩ -- order? simp
local notation "Zⁱ"=> align Y Y₂
variable (h: Y.Famous)(he:∀ i U V,p (Y.works i U V)=Y₂ i U V)
section plank
include he
variable {J:Type}[Fintype J] (X:Coat T F)(s:Pipe.Clump S ι)(z:Air f su)(χ:Chi)(U:Grid c)(hp:Summable (Y.honest χ U))
omit he in
lemma plank (x)(k:ℝ) : p (k • x)=k • p x:= map_smul (p.toLinearMap.restrictScalars ℝ) ..
lemma loom_he (x: Finset ℕ) : p ((Y.suitcase F).capacityP s x X z)= ((Zⁱ).suitcase F).capacityP s x X z:=by
    unfold Pipe.capacityP; rw [plank]; apply congr_arg; unfold Pipe.averageP; rw [map_prod]; exact prod_congr rfl (fun i _=> (plank p ..).trans (congr_arg (fun x=> Y.riseP X z i • x) (he i _ _)))
omit he in
lemma chosenC (f:J→EvenA c N)(g:J→EvenA c M) (hp:∀ i,p (f i)=g i) : p (choiceS f)=choiceS g:=by unfold choiceS; rw [plank, map_sum]; exact congr_arg _ (sum_congr rfl fun i _=> hp i)
include h
lemma loomX (hx:X.x=τ)(hk:X.width=o.K) : p ((Y.suitcase F).shootsP X s)= ((Zⁱ).suitcase F).shootsP X s:=by
    unfold Pipe.shootsP; split
    swap; next hh=>rw [if_neg (show ¬ (Ac.Spark ((Zⁱ).suitcase F).gP s ∧ ((Zⁱ).suitcase F).born s ∧ RG.flags (Pressure.temp X.x) X.V ∩((Zⁱ).suitcase F).full s=(roster s.toLeft).flags) from hh)]; exact map_zero _
    next hh=>
      rw [if_pos (show Ac.Spark ((Zⁱ).suitcase F).gP s ∧ ((Zⁱ).suitcase F).born s ∧ RG.flags (Pressure.temp X.x) X.V ∩((Zⁱ).suitcase F).full s=(roster s.toLeft).flags from hh)] -- syntax R
      apply chosenC; intro i; let M' := ((Matter.planted X s.toLeft).taggedL i)
      have h2:= envPlot ((Y.suitcase F).ripeP (own s.toLeft) s (Y.forwarded F h) M' hx hk (planted_valid ..)) ((F.order su).prod (M'.dice))
      unfold Beam.call; let p':= p.toLinearMap.toContinuousLinearMap.restrictScalars ℝ; exact Eq.trans (p'.integral_comp_comm h2).symm (integral_congr_ae (Eventually.of_forall (fun i=> loom_he Y p Y₂ he _ s _ _))) -- let aliases
lemma dawned : p (Y.vF s χ U)=(Zⁱ).vF s χ U:= chosenC p _ _ (fun _i=> loomX Y p Y₂ h he _ _ rfl rfl)
lemma affirmed (t:Clusters Y.Bright) : p (termP (blocked Y.lightF) (dawnV Y χ U) t)=termP (blocked (Zⁱ).lightF) (dawnV (Zⁱ) χ U) t :=by unfold termP; rw [plank,plank, map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun i _=> dawned Y p Y₂ h he ..)
lemma loomDay (hZ : (Zⁱ).Famous)(s:Clusters Y.Bright): p (Y.honest χ U s)= (Zⁱ).honest χ U s:=by rw [phoenix Y χ U h,phoenix _ χ U hZ]; exact affirmed Y p Y₂ h he χ U s
include hp
lemma mottoDay (s:Y.Wort) : p (mission Y χ U s)=mission (Zⁱ) χ U s:=by
    unfold mission motto; split
    swap; next hh=>rw [if_neg (show ¬(wagon (Zⁱ).broad s ∧ RG.flags (Pressure.temp τ) U∩ wound (Zⁱ).broad s=GasP.sweep (Zⁱ).invD s) from hh)]; exact map_zero _
    next hh=>rw [if_pos (show wagon (Zⁱ).broad s ∧ RG.flags (Pressure.temp τ) U∩ wound (Zⁱ).broad s=GasP.sweep (Zⁱ).invD s from hh),map_prod]; apply prod_congr rfl; intro i _; rcases i with i|i; exact dawned Y p Y₂ h he ..
             unfold GasP.samples GasP.dropsP; simp only [Sum.elim_inr]; let p':= p.toLinearMap.toContinuousLinearMap
             rw [map_sub,map_one,NormedSpace.map_exp p p'.continuous,map_neg]; apply congr_arg (fun x=> NormedSpace.exp (-x)-1); unfold portion; let fY (v:Clusters Y.Bright):= if GasP.seatP Y.lightF v=i then termP (blocked Y.lightF) (Y.dawnV χ U) v else 0; have hK: Summable fY :=by unfold fY; simp_rw [← phoenix Y χ U h]; exact somG (k:=Y.honest χ U) (p:= GasP.seatP Y.lightF) hp.norm i -- check
             exact (p'.map_tsum hK).trans (tsum_congr (fun j=>by
                    unfold fY; split
                    next hT=> exact (affirmed Y p Y₂ h he χ U j).trans (if_pos (show unionOf Zⁱ.lightF j.snd=i from hT)).symm
                    next hT=> exact (map_zero p).trans (if_neg (show unionOf Zⁱ.lightF j.snd ≠ i from hT)).symm)) -- defeq if dif
end plank
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.mottoDay
