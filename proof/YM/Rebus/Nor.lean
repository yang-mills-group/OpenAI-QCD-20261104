import YM.Rebus.Pledge
import YM.Play.Cause
import YM.Cape.Peace
/-! # Common ownership W. Awakening exact by Brief. Calculus upcoming. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
section
-- forecast eventual.Spec.Any w=φ.C Logging permits. uniform clocks choose gear after. 
variable {a b d d₁ w k₁ h δ ε:ℝ}
open Spice
lemma braze (P : Plan j)(k:ℕ)(L:Side)(q u v a η:ℝ)(l:ℕ)(hη:0<η)(hu:0<u)(W:ℝ→ℝ)(hW:Rate su L (-(1/2)) W) (hB:∀ᶠ x in atTop,0≤W x) : ∃ Z:ℝ→ℝ, Rate su L (-(1/32)) Z ∧ ∀ᶠ x:ℝ in atTop,0≤Z x∧∀ (N:ℕ)(F:Flight j k), F.L=L→∀ (c f:Side)(h:f.val=c.val*F.L.val)(r r' s s' m t':ℝ) (X:Offer 1 r s)(Y:Offer 2 r' s') (D:Sun F c f h (coneK L η x) v q u a l (pesto P F h (trunkM X Y t' m f))), |m| ≤ haloK L x→ Skiff (N:=N) F h D (radiusB x) (W x) (Z x) :=by
    obtain ⟨C,hC,h⟩:= Spice.boughtX; obtain ⟨U,V,hU,hV,hF⟩:= Rot.aurora P k L q u v a η l hη hu _ (hW.mul_left C)
    let H x:= |U x| + |V x|; have hm : Rate su L (-(1/32)) H:= Rate.add (hU.compare (Eventually.of_forall (fun x=>by change |(|U x|)| ≤ _; rw [abs_abs]))) (hV.compare (Eventually.of_forall (fun x=> by change |(|V x|)| ≤ _; rw [abs_abs]))) -- nested bars
    refine ⟨H,hm,?_⟩; filter_upwards [hB,hF] with x hx hz; refine ⟨add_nonneg (abs_nonneg _) (abs_nonneg _),?_⟩; intro N F hL c f he r r' s s' m t' X Y D hM
    constructor
    · intro G d i j ht hw; exact ((hz N c f F he hL r r' s s' m t' X Y D hM G (mul_nonneg hC.le hx)).1 i j (h f G 1 _ (W x) (fun a hi hj=> (ht a hi hj).trans hw))).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    intro G d i j ht hw; exact ((hz N c f F he hL r r' s s' m t' X Y D hM G (mul_nonneg hC.le hx)).2 i j (h f G 1 _ (W x) (fun a hi hj=> (ht a hi hj).trans hw))).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
lemma rollW (P:Plan j)(k:ℕ)(L:Side)(N:ℕ) : ∃ C:ℝ,∀ᶠ x in atTop,∀ (c f:Side)(F: Flight j k)(h:f.val=c.val*F.L.val), F.L=L→Spins F h N (radiusB x) C := by
    obtain ⟨C,V⟩:= Rot.pretzel P k L N; obtain ⟨S,hV,h⟩:= V 0
    refine ⟨max C 1,?_⟩; filter_upwards [h] with x hx c f F H hP; exact ⟨fun i=> ((hx c f F H hP).2 i).2.trans (le_max_left ..),fun i j=> ((hx c f F H hP).1 i j).2.trans (le_max_left ..),le_max_right C 1⟩
end
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.braze
