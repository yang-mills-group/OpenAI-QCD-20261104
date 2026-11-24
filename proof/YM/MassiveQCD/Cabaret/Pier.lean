import YM.MassiveQCD.Palette.Hang
import YM.QCD.Purse.Blank
/-! # Cut identities for positive-power cylinders.
 Keep `Y` underlying anchors and forests; no `∃` over comparable lengths; true principal.
 Shutters only on WORKS, since preparing at input via Hue yields exactly homogeneous matrix
 currents. `p` represents the one-choice port here, λ arbitrary.
 -/
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
open Sway OrbitG Villa Loom Bay Strut Patron
variable (dep : ι→ℕ)(ζ ζ₀ : ℂ)
-- pay family `X` any exact match. helps rewrite defeq even if callers choose tableau ctor proofs; works explicitly, no HEq cheating.
noncomputable def tintF (M:ι→Grid f→Grid c→EvenA c N): Fleet H ι N:={ Y with works:=M }
variable (M:ι→Grid f→Grid c→EvenA c N)(χ:Chi) -- remove p
set_option quotPrecheck false
local notation "A"=> tintF Y M
variable (h:∀ i U V, M i U V=ζ^dep i • Y.works i U V)(i:ι) (X: Coat T F) (W':Air f su)
lemma tuneP {β:Type} (w: β→ℕ)(ζ:ℂ){f g:β→EvenA c N}(s:Finset β)(h:∀ i∈s,g i=ζ^w i • f i): (∏ i∈s,g i)=ζ^(∑ i∈s,w i) • ∏ i∈s,f i:=by -- ghost
    induction s using Finset.induction_on with
    | empty=> rw [Finset.prod_empty,Finset.sum_empty,pow_zero,Finset.prod_empty,one_smul]
    | insert i s hi ih=> rw [prod_insert hi,prod_insert hi,sum_insert hi,h i (mem_insert_self _ _), ih fun j hj=>h j (mem_insert_of_mem hj), pow_add,smul_mul_smul_comm]
include h
private lemma legalU : (A).coming (F:=F) i X W'=ζ^(dep i) • Y.coming (F:=F) i X W':=by unfold coming; rw [show (A).works i _ _ =_ from h i _ _, smul_comm]; rfl
private lemma legalC : (A).muscle i X W'=ζ^(dep i) • Y.muscle i X W':=by dsimp only [muscle]; rw [show (A).works i _ _ = _ from h i _ _,smul_comm]; rfl
noncomputable def depthF (dep:ι→ℕ)(s: Pipe.Clump S ι):ℕ:=∑ i∈s.toRight,dep i
variable (s: Pipe.Clump S ι)
local notation "Uv"=> depthF dep s
lemma penned (x:Finset ℕ): ((A).suitcase F).capacityP s x X W'=ζ^(Uv) • (Y.suitcase F).capacityP s x X W':=by
    unfold Pipe.capacityP; rw [← smul_comm _ (ζ^(Uv))]; apply congr_arg; exact tuneP dep ζ s.toRight fun j _=> legalU Y dep ζ M h j X W'
omit h in
lemma choicer {β:Type}[Fintype β](Q':β→EvenA c N)(V:β→EvenA c N)(α:ℂ)(he:∀ i,V i=α • Q' i): choiceS V= α • choiceS Q':=by
    unfold choiceS; simp_rw [he,← Finset.smul_sum]; exact smul_comm ..
lemma speeds : ((A).suitcase F).shootsP X s = ζ^(Uv) • (Y.suitcase F).shootsP X s:=by
    unfold Pipe.shootsP
    split <;> rename_i hp
    · rw [if_pos (show Ac.Spark (Y.suitcase F).gP s ∧ (Y.suitcase F).born s ∧ RG.flags (Pressure.temp X.x) X.V ∩(Y.suitcase F).full s=(roster s.toLeft).flags from hp)]; apply choicer; intro i; unfold Beam.call; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with a; exact penned Y dep ζ M h _ _ _ _ -- F
    rw [if_neg (show ¬ (Ac.Spark (Y.suitcase F).gP s ∧ (Y.suitcase F).born s ∧ RG.flags (Pressure.temp X.x) X.V ∩(Y.suitcase F).full s=(roster s.toLeft).flags) from hp),smul_zero]
lemma speedS (V:Grid c): (A).vF s χ V=ζ^(Uv) • Y.vF s χ V:=choicer _ _ _ (fun _=> speeds Y dep ζ M h _ s) -- order χ not used in body, specify.
lemma borderline (p: Finset (Tubular f su))(t:F.Slice su)(z:Body (↥p)): (A).regards p s X t z = ζ^(Uv) • Y.regards p s X t z :=by
    let U:= X.wrapY t; let k:=spill p z
    dsimp only [regards]; rw [← smul_comm _ (ζ^(Uv))]; apply congr_arg; rw [← smul_comm _ (ζ^(Uv))]; apply congr_arg; exact tuneP dep ζ s.toRight fun j _=> legalC Y dep ζ M h j U k
lemma currentL (p:Finset (Tubular f su)) : (A).lows p s X = ζ^(Uv) • Y.lows p s X :=by unfold lows; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with y; rw [← integral_smul]; exact integral_congr_ae (ae_of_all _ (fun i=> borderline Y dep ζ M h _ s p _ i))
lemma border : (A).bandL s X= ζ^(Uv) • Y.bandL s X:=by
    unfold bandL; split
    next he=> rw [if_pos (show Ac.Spark (Y.suitcase F).gP s ∧ (Y.suitcase F).born s from he)]; exact choicer _ _ _ fun _=> currentL Y dep ζ M h _ s _
    next he=> rw [if_neg (show ¬ (Ac.Spark (Y.suitcase F).gP s ∧ (Y.suitcase F).born s) from he),smul_zero]
lemma sparkB (V:Grid c): (A).brisk s χ V= ζ^(Uv) • Y.brisk s χ V:= choicer _ _ _ (fun _=> border Y dep ζ M h _ s)
noncomputable def depthT (dep:ι→ℕ)(t:Clusters (Y.Bright)):= ∑ i,depthF dep (t.2 i).val
variable (t:Clusters (Y.Bright))(V:Grid c)(W':Clusters (Y.Bright)→RegularAddress c) -- split g
set_option maxRecDepth 4800 in
lemma fuelM : (tintF Y M).furnace χ V t=ζ^(depthT Y dep t) • Y.furnace χ V t:=by -- defeq
    unfold furnace termP; rw [← smul_comm _ (ζ^(depthT Y dep t))]; apply congr_arg; rw [← smul_comm _ (ζ^(depthT Y dep t))]; apply congr_arg; exact tuneP (fun i=>depthF dep (t.2 i).val) ζ _ (fun i _=>sparkB Y dep ζ M χ h (t.2 i).val V) -- order M χ ok.
lemma paysS : (tintF Y M).honest χ V t=ζ^(depthT Y dep t) • Y.honest χ V t:=by
    unfold honest; by_cases ht: Healthy (Pressure.temp τ) (seatP Y.lightF t) V
    · rw [masked_eq _ _ _ _ (show Healthy _ (seatP (tintF Y M).lightF t) V from ht),masked_eq _ _ _ _ ht]; exact fuelM Y dep ζ M χ h t V
    rw [masked_ne _ _ _ _ (show ¬ Healthy _ (seatP (tintF Y M).lightF t) V from ht),masked_ne _ _ _ _ ht,smul_zero]
lemma regalF : (Patron.crude (tintF Y M) χ W').view t V = ζ^(depthT Y dep t) • (crude Y χ W').view t V :=by
   unfold crude pepper; dsimp only; rw [← integral_smul]; refine integral_congr_ae (ae_of_all _ (fun i=>?_)); dsimp only; rw [fuelM Y dep ζ M χ h, swayC] -- numeral.B
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.regalF
