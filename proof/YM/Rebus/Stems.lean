import YM.Rebus.Theta
/-! # Cyclopean.S tests. Econometric gauge Forecast moving LETTER and costs True covariance . -/
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
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Current
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Bera.Oce Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁ p₀ q₁ q₂ r' r t t' A₀ A₁ B' u u' s' σ θ η η₁ Ω' ε :ℝ}{S: StepData c f}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {T:Tube su S}{N i j n k m l B Q: ℕ}
open FreeResolvent
variable (W : Support c) (V:Directions su c) (b:Kh c) (Z₀: Web su)
local notation "Vh"=> increment 1 V
-- height.L gloss
section
attribute [-instance] Sample.LoomT.instFintypeTo
private lemma breezeP0 (G : Gauge) (b: Col G c)(P:Directions G c)(Z₀: Web G)(hv:‖P‖≤ v)(hi:v≤ Z₀.radius):
    |Hypnos.marrow (increment 1 P) (bleep b) b.2.2-Fruit.jet P b| ≤ Z₀.scale*v^2:=by
    rw [Fruit.peal]; have he:=labels_area P; have hz:= Z₀.defect _ (bleep b) ((he.trans hv).trans hi); rw [labels_eq] at hz
    let z:= Hypnos.marrow (increment 1 P) (bleep b)-Hypnos.tide P (bleep b)
    exact (PiLp.norm_apply_le z b.2.2).trans (hz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (he.trans hv) _) (zero_le_one.trans Z₀.cost)))
private lemma linearZ (G:Gauge)(b:Col G c)(P:Directions G c)(Z₀:Web G)(hv:‖P‖≤ v): ‖Fruit.jet P b‖≤ Z₀.scale*v:=by rw [Fruit.peal]; exact (PiLp.norm_apply_le (Hypnos.tide P (bleep b)) b.2.2).trans ((Z₀.linear _ _).trans (mul_le_mul_of_nonneg_left ((labels_area P).trans hv) (zero_le_one.trans Z₀.cost)))
attribute [instance] Sample.LoomT.instFintypeTo
end
lemma breezeK (hv:‖V‖≤ v)(hi:v≤ Z₀.radius): |Hypnos.marrow Vh (bleep b) b.2.2-Fruit.jet V b| ≤ Z₀.scale*v^2:= breezeP0 su b V Z₀ hv hi
lemma linearK (hv:‖V‖≤v): ‖Fruit.jet V b‖ ≤ Z₀.scale*v:=linearZ su b V Z₀ hv
lemma gust (σ:ℝ)(hv: ‖V‖≤v)(hs: v≤ Z₀.radius): ‖karm σ Vh b‖ ≤ |σ⁻¹| * (Z₀.scale*v+Z₀.scale*v^2):=by
    unfold karm; rw [norm_mul]; refine mul_le_mul_of_nonneg_left (?_) (show 0≤‖σ⁻¹‖ from norm_nonneg _)
    let m:= Hypnos.marrow Vh (bleep b) b.2.2
    have ht: ‖m‖≤ ‖m-Fruit.jet V b‖+‖Fruit.jet V b‖:= by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub m (Fruit.jet V b) 0
    exact ht.trans ((add_le_add (show ‖m-Fruit.jet V b‖≤ Z₀.scale*v^2 from breezeK V b Z₀ hv hs) (linearK V b Z₀ hv)).trans_eq (add_comm ..))
-- μ_true.Q
variable (H H': Bed)(U':Towers S.patch.L)
local notation "T0"=> view su S H H' U'
local notation "T1"=> Fruit.cones su S H H' U' B
local notation "V0"=> Fruit.curtain su S H H' U'
local notation "V1"=> Fruit.sprig su S H H' U' B
section cast
-- cast mania. package REAL conditional identity.Enrollment.B with post normals. Use explicit Subsingleton.elim et al
-- Try attribute local.
attribute [-instance] Sample.LoomT.instFintypeTo
variable {a p b:ℝ}{Q:Teller su}
variable (hq:Fruit.Myth su S H H' U' B q₁ q₂)
include hq
lemma cardGun (i:Kh f) : (∑ j, |(Fruit.view su S H H' U') i j|) ≤ q₁:=by simpa only [FreeResolvent.Cost.weight_zero,one_mul] using hq.broad.bound i
lemma cardGad (i:Kh f) : (∑ j, |(T0-T1) i j|) ≤ q₂:=by simpa only [FreeResolvent.Cost.weight_zero,one_mul] using hq.tight.bound i
lemma columnGad (i j:Kh f) : |V0 i j| ≤q₁∧|(V0-V1) i j|≤q₂:=by
    refine ⟨?_,?_⟩; simpa only [FreeResolvent.Cost.weight_zero,one_mul] using hq.paysC.weighted i j; simpa only [FreeResolvent.Cost.weight_zero,one_mul] using hq.tightC.weighted i j
attribute [instance] Sample.LoomT.instFintypeTo
end cast
section
private lemma sites {A B C:Type}[AddCommMonoid B]{f g:Fintype A}(p:A→B): ∑ i∈ ( @Finset.univ A f),p i=∑ i∈ ( @Finset.univ A g),p i:=by rw [Subsingleton.elim f g]
variable (hq:Fruit.Myth su S H H' U' B q₁ q₂)
include hq
lemma windK (i:Kh f) : (∑ j, ‖T0 i j‖) ≤ q₁ ∧ (∑ j, ‖T1 i j‖) ≤ q₁ ∧ (∑ j, ‖T0 i j-T1 i j‖) ≤ q₂:= by
    have ht:= cardGun H H' U' hq i; have hx:(∑ j, ‖T0 i j‖) ≤ q₁ :=by
       simp_rw [Real.norm_eq_abs]; exact le_trans (sites (C:=Unit) _).le ht
    refine ⟨hx,(Finset.sum_le_sum (g:=fun j=>‖T0 i j‖) (?_)).trans hx,?_⟩
    · intro j _; unfold Hypnos.Fruit.cones stuns; rw [of_apply]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
    simp_rw [Real.norm_eq_abs,← Matrix.sub_apply]; exact le_trans (sites (C:=Unit) _).le (cardGad H H' U' hq i)
lemma deemed (i j:Kh f): ‖V1 i j‖≤q₁ ∧ ‖V0 i j-V1 i j‖≤q₂:=by
    obtain ⟨h,h'⟩:=columnGad H H' U' hq i j; refine ⟨?_,h'⟩; unfold Fruit.sprig stuns; rw [of_apply]; split; exact h; rw [norm_zero]; exact (abs_nonneg _).trans h
-- also means travel equality adapt `mulVec`
omit hq
variable (h0 : Towers.Diagonal S H H' U')
variable {c': Clip}
local notation "TK"=> T0
lemma wander (h:T.R.A0=U'.A0)(hF:Floor H c' f η Ω') (hT:Towers.Diagonal S H H' U') :
    (T0 *ᵥ jet V) = Fruit.jet (route T V) := by
    have he:= Fruit.travel_match H H' U' V hT h hF; rw [← he]; funext i; unfold Matrix.mulVec dotProduct; exact sites (C:=Unit) _
end
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.wander
