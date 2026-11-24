import YM.Rebus.Crest
import YM.Cape.Bark
import YM.Play.Dulce
/-!
 # cert read kernels charged. Once resident.S of X always see entire required cube. No chart from incidental flags. Uses threshold & flags equality internally.
-/
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
variable {c f L:Side}{P:Teller su}{β τ C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {N i j n k m l B Q: ℕ}
-- observed on globally scaled coupling
open Stitch Plate Twist FlareV Cupola
-- CAPSULE bound polynomial unit.Q scalable P predicted. phase.Unit includes K tolerance.Next
variable {Yp D':Type}{r r' t v κ' a K₀ ε α Λ:ℝ}
variable (p:I→Site f)(q:I→ Bool)(V:Finset (Finset I))
variable (z: Reel f N I D)(X:Finset D)
local notation "D0"=> Dh f N I
local notation "Dv"=> Quince f N I
def sled (T:Finset I)(U: Grid f): Patio (Dh f N I):=∑ i∈ X with z.z i=T,z.mark i U
structure Moor (C:Quince f N I)(B l k m:ℕ)(t r κ' v ε:ℝ) : Prop where
    syntaxP : SetL p V B l k m C
    height : ∀ i∈V, i.Nonempty→ cents (C i) ≤ v^i.card -- loosen appropriately from moll.A caps later
    mirrors i : i∈V→ i.Nonempty → ∀ U:Directions su f, ‖U‖≤ r → Healthy t (Cape.cups p (innerT l *B) i) (increment 1 U)→ ‖sled z X i (increment 1 U)-Oce.rose (Dh f N I) (karm κ' (increment 1 U)) (C i)‖ ≤ ε
variable (F:Film f N I D')(Y: Rise f N E J)(P' : Twist.Register Y z F) (Φ : Quince f N I) (O:BudgetPoint)
local notation "S0"=> collection z F X Y P'
local notation "Z'"=> result Y z F P'
lemma paddle (U:Grid f)(i: Finset I): glen Y Z' S0 U i= sled z X i U:=by
    classical
    let K':= P'.ear; let u : E → Patio D0:=fun j=> (Z').main j U
    unfold glen collection sled; rw [sum_filter,sum_filter, sum_image P'.ear.injective.injOn]; apply sum_congr rfl; intro j _; rw [(figures Y z F P' _).2,(figures ..).1] -- flags
lemma reaches (hp:Bearing p q V z X L l m v τ α O K₀ F)(h:Moor p V z X Φ O.B l k m O.threshold r κ' Λ ε) : Vitae p Y Z' S0 V r O.threshold κ' ε O.B l Φ:=by
    refine ⟨?_,fun i hi he u hu h' =>?_⟩; · intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; rw [(figures ..).2]; exact ⟨hp.boost.book.stays _,fun i hi=> by rw [P'.homeP]; exact hp.rise.brood j hj i hi⟩
    rw [paddle]; exact h.mirrors i hi he _ hu h'
-- polynomial cost interpolate.X and rescale.
variable (w:I→ℝ)
def unitsF (Φ: Quince f N I): Quince f N I := fun i=> FlareV.give w i • Φ i
lemma stampWP (i:Finset I)(U:Kh f→ℝ): Oce.rose D0 U (unitsF w Φ i)= FlareV.give w i • Oce.rose D0 U (Φ i):= by
    let p:= FlareV.give w i; change Oce.rose _ U (p • Φ i)=p • _; rw [← one_smul (Patio D0) (Φ i), ← smul_assoc,one_smul,map_smul,smul_assoc,one_smul]
lemma peg (h:SetL p V B l k m Φ) : SetL p V B l k m (unitsF w Φ):=⟨fun i hi h'=> Submodule.smul_mem _ _ (h.scope i hi h'),fun i hi h' hh=> h.core i hi h' (fun hz=> hh (by unfold unitsF; rw [hz,smul_zero]))⟩
lemma powersF (i: Finset I)(h:∀ i,|w i| ≤ r): ‖FlareV.give w i‖ ≤ r^i.card:=by
    induction i using Finset.induction_on with
    | empty=> simp [give]
    | insert a i hi ih=> unfold FlareV.give; rw [prod_insert hi,norm_mul,card_insert_of_notMem hi,pow_succ',Complex.norm_real]; exact mul_le_mul (h a) ih (norm_nonneg _) ((abs_nonneg _).trans (h a))
lemma paysP (v:ℝ)(hv:0 ≤ v)(W: Finset I) (h:cents (Φ W)≤v^W.card) (hz:∀ i,|w i|≤ r)(ht:0 ≤ r): cents (unitsF w Φ W)≤(v*r)^W.card:=by
    unfold unitsF; rw [Bera.smul_cent,mul_comm v,mul_pow]; exact mul_le_mul (powersF w _ hz) h (cent _) (pow_nonneg ht _)
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.reaches
#print axioms YM.MassiveQCD.Rebus.paysP
