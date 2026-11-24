import YM.Infer.Bravo
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {K:KernelChoices}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R: BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P: SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
open Suburb Rails
namespace Tribute
open Massive.Poised Massive Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.Poised.Pipes
open Bank Hike Stative Stair -- Hike nested? open Bank before
variable {D U M A:Type}(Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0 Gn :ℕ)
variable {θ tol:ℝ}(Y:Metros P J θ F₀ χ)
-- same base.Cliff. Pre prices per node; Lois K-neighbor max in bootstrap of progress; simple sum bound†.
namespace Nacre
open Bounce Ivy MeasureTheory
variable (f:Fluke Θ Uv Gn) (V:PreLoan Θ Uv i0 Y Gn f)
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised.Sieve Orientation
open QCD
variable (p: Massive.UV.Label Gn)(W:Gallery.Knot p)(h:Requisite Θ p W)(ε:ℝ)
open Rails.Reference.Sharp Suburb.Melt Conductor Conductor.Quant
open MassiveQCD.Sample MassiveQCD.Sample.GreenCap.Works
variable (Φ:Capsule Θ Uv Gn f p W ε)(E: RiseBook Y)(b:ChangeQ)(L:Side)
open Finset
variable (Z:Symph Θ Uv Gn f)
-- use Price cap topology constants. fixed Q per V.Balance α prior.ε_Q error.
abbrev pedal (a:ℝ):Prop:=∀ i:Venus Gn,Z.J*(1/(2*a)*(Z.T₁ i).D) ≤ Z.ε
lemma adjusts (p:ℝ) : ∃ a:ℝ, PilotW Θ Uv i0 Gn Y f V b a ∧ p ≤ a ∧ pedal Θ Uv Gn f Z a:=by
    let s:= ∑ i:Venus Gn, Z.J*(Z.T₁ i).D; obtain ⟨a,hp,ha⟩:= knocks Θ Uv i0 Gn Y f V b (max p (s/Z.ε)); refine ⟨a,ha,(le_max_left ..).trans hp,fun i=>?_⟩; have hs: s ≤ a*Z.ε:= (div_le_iff₀ Z.pos).mp ((le_max_right ..).trans hp); have hx:Z.J*(Z.T₁ i).D ≤ s:= Finset.single_le_sum (fun i _=> mul_nonneg (zero_le_one.trans Z.up) (zero_le_one.trans (Z.T₁ i).day)) (mem_univ i); apply le_trans (mul_le_mul_of_nonneg_left (show 1/(2*a)*(Z.T₁ i).D≤ (1/a)*(Z.T₁ i).D from (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left zero_le_one (zero_lt_one.trans_le ha.tall) (by linarith only [ha.tall])) (zero_le_one.trans (Z.T₁ i).day))) (zero_le_one.trans Z.up)); rw [show Z.J*(1/a*(Z.T₁ i).D)= (Z.J*(Z.T₁ i).D)/a from (by ring)]; apply (div_le_iff₀ (zero_lt_one.trans_le ha.tall)).2; exact hx.trans (hs.trans_eq (mul_comm ..))
-- price TS at month. Join arbitrary additional Stock expenses.after-L
abbrev standing (x W:ℝ):Prop:= ∀ i: Venus Gn, FilmW Θ Uv Gn Y f _ _ Z.ε (Z.T₁ i) E b L x W
lemma bundles (p:ℝ→ℝ)(t:ℝ) (h:Rate su L t p)(hp:∀ᶠ x in atTop,0≤ p x) : ∃ (μ:ℝ→ℝ) (r:ℝ), Rate su L r μ ∧ ∀ᶠ x in atTop, p x ≤ μ x ∧ 0 ≤ μ x ∧ ∀ V≥μ x, standing Θ Uv Gn Y f E b L Z x V:=by
    have ht:∀ I:Finset (Venus Gn),∃ (μ:ℝ→ℝ)(r:ℝ),Rate su L r μ ∧ ∀ᶠ x in atTop, p x ≤ μ x ∧ 0 ≤ μ x ∧ ∀ i∈I,∀ V≥ μ x, FilmW Θ Uv Gn Y f _ _ Z.ε (Z.T₁ i) E b L x V:=by
       intro I; induction I using Finset.induction_on with
       | empty=> exact ⟨p,t,h,hp.mono fun i hi=>⟨le_rfl,hi,fun v hv=>False.elim ((notMem_empty _ ) hv)⟩⟩
       | insert i I hx ih=> obtain ⟨μ,t,hT,H⟩:=ih; obtain ⟨w,z,hZ,hW⟩:=berth Θ Uv Gn Y f _ _ Z.ε (Z.T₁ i) E b L; refine ⟨_,max z t, ((hZ.weaken (le_max_left ..)).add (hT.weaken (le_max_right ..))),?_⟩; filter_upwards [H,hW] with x hx hy; have h1:μ x ≤ w x+μ x:= le_add_of_nonneg_left hy.1; exact ⟨hx.1.trans h1,hx.2.1.trans h1,fun j h v hr=> (mem_insert.mp h).elim (fun h=> h ▸ hy.2 v ((le_add_of_nonneg_right hx.2.1).trans hr)) (fun h=> hx.2.2 j h v (h1.trans hr))⟩
    obtain ⟨μ,t,hT,h⟩:= ht Finset.univ; exact ⟨μ,t,hT,h.mono fun i hi=>⟨hi.1,hi.2.1,fun y hy j=> hi.2.2 j (mem_univ j) y hy⟩⟩
end Nacre
end Tribute
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.Nacre.adjusts
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.Nacre.bundles
