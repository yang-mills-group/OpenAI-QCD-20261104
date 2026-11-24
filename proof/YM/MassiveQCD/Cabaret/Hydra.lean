import YM.MassiveQCD.Cabaret.Pier
/-! # Fleet for HUE gas from core Expansion -- marked stages -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R : BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}

open Patron
-- `view/place/hat` fixed, only spin payloads changes budget. Packed witness evalu at ζ=1, met-1 phases. Supports tags zero at marker zero demand caller unmarked.
structure StageF (n:Side) (N:ℕ)(E J:Type) where
 row : E→RegularAddress n
 front : J→ Cove.Hat n
 mass : ℂ→E→Grid n→ EvenA n N
 mark : ℂ→ J→Grid n→EvenA n N
 generation : E → ℕ
 degree : J→ℕ
noncomputable def StageF.get (A:StageF f N E K)(z:ℂ): Rise f N E K:= ⟨A.row,A.front,A.mass z,A.mark z⟩
structure StageF.Scale (A:StageF f N E K) (t:ℝ) :Prop where
 regular (i:ℂ)(he:‖i‖≤1)(j:E)(V:Grid f): NormedSpace.exp ((A.get i).reading t V j)-1=i^A.generation j • (NormedSpace.exp ((A.get 1).reading t V j)-1)
 knots (i:ℂ)(he:‖i‖≤1)(j:K)(V:Grid f): (A.get i).plug j V=i^A.degree j • (A.get 1).plug j V
variable (D₀:StageF f N E K) (h:D₀.Scale R.threshold) [Fintype D][Countable E][Countable K]
variable (H)(Y:Send S.ratio N D)(ζ:ℂ)(G : Fleet H ι N) (t:ℝ)
local notation "Ξ"=>Fj D E K
variable (s:Finset (Fj D E K))(V:Grid f)(hp:‖ζ‖≤1)
local notation "T'"=>R.threshold
local notation "d"=> D₀.get
noncomputable def depth_g (D₀:StageF f N E K) (s: Finset (Fj D E K)) :ℕ:= (∑ x∈leftE s,D₀.generation x)+∑ x∈spent s,D₀.degree x
include h hp
omit [Fintype D][Countable E][Countable K] in
lemma fight : Cove.hue Y (D₀.get ζ) T' s V= ζ^depth_g D₀ s • Cove.hue Y (D₀.get 1) T' s V:=by
    let t:=T'
    have hM : made (d ζ) t V s=ζ^depth_g D₀ s • made (d 1) t V s:=by unfold made; rw [tuneP D₀.generation ζ (f:=fun i=> NormedSpace.exp ((d 1).reading t V i)-1) (leftE s) (fun i _=> h.regular ζ hp i V), tuneP D₀.degree ζ (f:=fun i=>(d 1).plug i V) (spent s) (fun i _=> h.knots ζ hp i V), depth_g,pow_add,smul_mul_smul_comm]
    unfold Cove.hue; split
    next ht=>
      rw [if_pos (show (d 1).spare (spent s)∧ closeS Y (d 1) T' s V from ht)]; apply YM.QCD.Port.lit_eqn; rw [map_smul,dipping,dipping,hM]; simp only [map_smul]; rfl
    next ht=> rw [if_neg (show ¬ ((d 1).spare (spent s)∧ closeS Y (d 1) T' s V) from ht),smul_zero]
set_option quotPrecheck false
local notation "VQ"=> (roof Y (d 1) 30 (radiusB τ))
local notation "X("i")"=> deckHue H Y (d i) VQ
local notation "M("v")"=> united (X( v )) G
noncomputable def depth_charge (D₀:StageF f N E K) (Y:Send S.ratio N D)(z:ℝ)(p: Wound (roof Y (D₀.get 1) 30 (radiusB z))⊕ι):ℕ:=Sum.elim (fun (p:Wound (roof Y (D₀.get 1) 30 (radiusB z)))=> depth_g D₀ p.val) (fun _=> 0) p
local notation "Y!"=>P
local notation "d!"=> depth_charge D₀ Y τ -- explicit notation. No using var
-- maybe use outer sc.ass
set_option maxRecDepth 3000 in
omit [Fintype D][Countable E][Countable K] in
lemma val_cash (i:Wound (roof Y (D₀.get 1) 30 (radiusB τ)) ⊕ ι) (U:Grid c): (M(ζ)).works i V U= ζ^((d!) i) • (M(1)).works i V U:=by
    cases i with
    | inl i=>
      let v:= i.val; let a:=(δ⁻¹ ^ budget (d 1) v)
      change a • Cove.hue .. = ζ ^ depth_g D₀ v • (a • Cove.hue ..)
      rw [show Cove.hue Y (d ζ) T' i.val V= _ from fight D₀ h Y ζ i.val _ hp,smul_comm a]
    | inr i=>
      rw [show (d!) (Sum.inr i)=0 from rfl,pow_zero,one_smul]; rfl
open GasP Ursell
local notation "x!"=> M(1)
-- Avoid defeq problems using map-tint explicit in consumer;
-- Use ℝ bounds `PortC` transported after exact stage-pawn relation. Result
-- `Pier` honest/value identities with Cluster and mission inputs preserving same Y. 
omit h hp [Fintype D][Countable E][Countable K] in
lemma tint_id : (M(ζ))=tintF (x!) (M(ζ)).works:=by rfl
end YM.QCD.Loom
#print axioms YM.QCD.Loom.tint_id
