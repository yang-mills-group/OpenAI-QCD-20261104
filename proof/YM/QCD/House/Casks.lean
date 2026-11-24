import YM.QCD.House.Streams

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
open scoped Matrix Kronecker
namespace Territory
-- actual queries at force boundaries + ghost
structure Gate :Prop where
 rights :∀ i U V,Gated (Y.ground i) (Y.works i U V)
-- projection membership even when Bochner 0
lemma solvent (A: Support c): ∃ Z:Submodule ℝ (EvenA c N),∀ i,Gated A i↔ i∈ Z:=by
   let V:=Creek.region (limits (F:=N) A); let p:= (Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ
   exact ⟨Submodule.comap p (V.toSubmodule.restrictScalars ℝ),fun i=> Iff.rfl⟩
lemma club (A:Support c)(r:ℝ)(x:EvenA c N)(h:Gated A x): Gated A (r • x):=by obtain ⟨Z,hZ⟩:=solvent (N:=N) A; rw [hZ]; exact Z.smul_mem r ((hZ x).1 h)
lemma inhabit {I₀:Type*}(A:Support c)(Q:I₀→EvenA c N)(s:Finset I₀)(h:∀ i∈s,Gated A (Q i)):Gated A (∑ i∈s,Q i):=by obtain ⟨Z,hZ⟩:=solvent (N:=N) A; rw [hZ]; exact Z.sum_mem fun i hi=> (hZ _).1 (h i hi)
lemma spearm {ι:Type*} (A:Support c)(Q:ι → EvenA c N)(h:∀ i,Gated A (Q i)):Gated A (∑' i,Q i):=by
    obtain ⟨Z,hZ⟩:=solvent (N:=N) A; rw [hZ]; by_cases hh:Summable Q
    swap; · rw [tsum_eq_zero_of_not_summable hh]; exact Z.zero_mem
    exact IsClosed.mem_of_tendsto (Submodule.closed_of_finiteDimensional Z) hh.hasSum (Eventually.of_forall (fun i:Finset ι=> (hZ (∑ x∈i,Q x)).1 (inhabit A Q i fun p _=> h p)))
lemma froth {ι:Type*}[MeasurableSpace ι](A:Support c)(Q:ι→EvenA c N)(h:∀ i,Gated A (Q i))(μ:Measure ι): Gated A (∫ i, Q i ∂μ):=by
    obtain ⟨Z,hZ⟩:=solvent (N:=N) A; rw [hZ]; let s:= ∫ i,Q i ∂μ; by_cases hh: Integrable Q μ
    swap; · rw [integral_undef hh]; exact Z.zero_mem
    obtain ⟨F,hF⟩:= Submodule.exists_isCompl Z; let V:=LinearMap.toContinuousLinearMap (Z.projection F hF); have he i: V (Q i)=Q i:= Submodule.projection_apply_of_mem_left hF ((hZ _).1 (h i))
    have hx:V s=s := by unfold s; rw [← ContinuousLinearMap.integral_comp_comm _ hh]; apply integral_congr_ae; exact Eventually.of_forall he
    rw [show _root_.Eq (∫ i,Q i ∂μ) (V s) from hx.symm]; exact Submodule.projection_apply_mem hF _
lemma avenueF (s:Pipe.Clump S ι)(V:Grid c)(χ:Chi)(hv:Y.Feasible)(h:Gate Y)(hp:Y.Famous): Gated (Y.fullA s) (Y.vF s χ V):=by
    unfold vF choiceS; apply club; apply inhabit; intro i _; let P:= (Y.suitcase (allot i)); let X:= prism T τ χ o.K V (allot i)
    change Gated (Y.fullA s) (P.shootsP X s); unfold Pipe.shootsP; split
    swap; · unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
    unfold draws choiceS; apply club; apply inhabit; intro u hu; let Q:= ((Matter.planted X s.toLeft).taggedL u)
    apply froth; intro r; apply club; exact gate_prod _ _ _ (fun i hi=>gateMon (Y.ground i) _ (P.leP _ hi) _ (club _ _ _ (h.rights ..))) -- r defeq
lemma avenueL (s:Pipe.Clump S ι)(V:Grid c)(χ:Chi)(h:Gate Y)(hp:Y.Famous): Gated (Y.fullA s) (Y.brisk s χ V):=by
    unfold brisk choiceS; apply club; apply inhabit; intro i _; let P:= (Y.suitcase (allot i)); let X:= prism T τ χ o.K V (allot i)
    unfold bandL; split
    swap; · unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
    unfold choiceS; apply club; apply inhabit; intro u hu
    unfold lows; apply froth; intro z; apply froth; intro a; apply club; apply club
    exact gate_prod _ _ _ (fun i hi=> gateMon (Y.ground i) _ (P.leP _ hi) _ (club _ _ _ (h.rights ..)))
end Territory
end YM.QCD.Loom.Fleet
