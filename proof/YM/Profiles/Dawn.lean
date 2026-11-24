import YM.Profiles.Venation
import YM.Profiles.Holler
import YM.VStages.FullRun
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
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
open Glint Jasper
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
open Massive (Sequence Scheme)
variable (E:RiseBook P₀) {O:Paved P₀ A X x} {Ht:Uptax P₀ A E x} (LL:HaarBudget su) {M₃:ℝ}
local notation "Φw"=>key P₀ A E

/-!
# One unequal-mass SU(3)-6 trajectory, in the coupling-and-spinor weight scheme,
with exact asymptotic slope, growing strides and mass-offset signal (positive & distinct)

Not the continuum theorem. See `tundra` for the existence result relating this
to the target `YM.Massive` quantities (the component `Sequence.searching`)
including tying the mass-offset signal to the Mark expansion and pressure assertions
(`Epitome`, `StormT` there). Statement for eventual βRef regime, no further
limit in reference β along the path.
-/
variable (ν:ℝ)
-- pay any supplementary gate plus D masses from commitments. Startup tolerance funding paid at time >=, applied during actual trajectory. Expose all post schedule for simultaneous rank purchases from Source kernels. Geometry beta.beta.min large; exposure constants paid before L.
open Tribute Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp
-- default schedule.Sc purchase
namespace Blazar
open Lobby.LifeT Lobby Counter Counter.Economies
variable (Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0:ℕ)(d:ℕ) (ξ:Fluke Θ Uv d)(Ξ:PreLoan Θ Uv i0 P₀ d ξ)
set_option quotPrecheck false
variable (e:ℝ)(he:0<e)(hX:∀ i:ℕ,Counter.Cave (A.spacing i) (clockQ P₀ A x i) θ)
variable (hw:∀ᶠ m in atTop, Blazar.Wins P₀ Θ Uv i0 d ξ Ξ (A.node m) (A.spacing m))
local notation "σ"=> luster P₀ A Θ Uv d ξ x Pt
local notation "φ"=> FWealth P₀ A Θ Uv d ξ (Pt:=Pt) (x:=x)
local notation "vΓ"=> (d:ℝ)/2
local notation "Q"=> A.measure
local notation "G"=> gross P₀ A Θ Uv i0 d ξ Ξ
include hX
variable (C:ℝ)
noncomputable def dawnF (i:ℕ)(S:ℝ):= S*Real.exp ((d:ℝ)/2*A.measure i+gross P₀ A Θ Uv i0 d ξ Ξ i)*(salary P₀ A (x:=x) i)⁻¹
local notation "k!"=>dawnF P₀ A Θ Uv i0 d ξ Ξ (x:=x)
lemma proofL (i:ℕ) (z:Massive.UV.Label d)(hf: (φ i z) ≤ C*Real.exp (vΓ* Q i+G i)): (σ i z)⁻¹ ≤ k! i C:=by
    have h: 0 < salary P₀ A (x:=x) i:= (hX i).shape.1
    change (salary P₀ A (x:=x) i / FWealth P₀ A Θ Uv d ξ (Pt:=Pt) (x:=x) i z)⁻¹ ≤ _; rw [inv_div,div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hf (inv_pos.mpr h).le
include he hw
lemma painted (S:ℝ)(hS:0 ≤ S): ∀ᶠ i:ℕ in atTop, dawnF P₀ A Θ Uv i0 d ξ Ξ (x:=x) i S ≤ S * Real.exp ((vΓ + e)*Q i):=by
     have ha:=half_pos he
     filter_upwards [ahead P₀ A Θ Uv i0 d ξ Ξ (e/2) ha hw,lunar P₀ A (e/2) ha hX] with i hp hm; unfold dawnF
     apply le_trans (mul_le_mul_of_nonneg_left hm (show 0≤ S*Real.exp ((d:ℝ)/2*A.measure i+gross P₀ A Θ Uv i0 d ξ Ξ i) from mul_nonneg hS (Real.exp_nonneg _))); rw [mul_assoc,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hS; linarith only [hp]
-- combine costs. output envelope includes Evec of x root.
local notation "b₀"=> maturity P₀ A hX
lemma cog (k:ℕ)(c:ℝ)(hc:0 ≤ c):∀ᶠ j:ℕ in atTop, let l:= maturity P₀ A hX j k; dawnF P₀ A Θ Uv i0 d ξ Ξ (x:=x) l c * Real.exp ((Track.scale A x l)^(1/2:ℝ)) ≤ c * Real.exp ((vΓ+e)*Q j):=by
     let g:= vΓ; have hg:0≤g:=by unfold g; positivity
     let a:=e/4; have ha:0<a:=by unfold a; positivity
     let u:=(e-2*a)/(g+2*a); have hp:0<g+2*a:=by positivity
     have hP:0<e-2*a:=by unfold a; linarith
     have hu:0<u:=div_pos hP hp
     filter_upwards [(Economies.canyonJ P₀ A hX k).eventually (painted P₀ A Θ Uv i0 d ξ Ξ a ha hX hw c hc), (Economies.canyonJ P₀ A hX k).eventually (Economies.futureBudget (x:=x) P₀ A a ha), Economies.levelGain P₀ A hX u hu k] with j h₁ h₂ ht l; refine le_trans (mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg _)) ?_; rw [mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hc; apply Real.exp_monotone
     have hv: A.measure l ≤ (1+u)*A.measure j:=ht; have hh:(g+2*a)*(1+u)=g+e:=by unfold u; field_simp; ring
     apply le_trans (add_le_add_right h₂ _); exact le_trans (le_of_eq (by change (g+a)*Q l+a*Q l=(g+2*a)*Q l; ring)) ((mul_le_mul_of_nonneg_left hv hp.le).trans_eq (by rw [←mul_assoc,hh])) -- signature order
end Blazar
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Blazar.cog
