import YM.Massive.Spire.Rebase
import YM.Massive.Beacon.Wake
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
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
namespace Stratum.Spire
open Rails
namespace Cairn
open Finset Grass NormedSpace MeasureTheory High PrismT
open Lunar Ring0 Stew.Project Sq
variable {s Θ W' u₀ v₀ tol α3 ν' σ η':ℝ}{χ:Chi}{R₀:ParcelR}{U V:SunR R₀}{τ:Policy Q T'.top N}
variable (P₀:Plan j)
set_option quotPrecheck false
local notation "λ₀"=> run S.L x
local notation "Tq"=> T'.top.clip
local notation "D₀"=> FieldB R₀ V c (haloK S.L x) P₀ S.land
local notation "δ'"=> A+(N:ℝ)*γ
variable {β b v Λ κ A3 H':ℝ}{Δ:PlaqAxes}
variable (F₀:Flavor N)(X:Voice f N)(Z:Gem c N (LayerQ c)) (B: Badge P₀ τ R P o χ T U b (run S.L x) (1/8) β μ z)
local notation "X!"=> red X.P X.K U P₀ S.wing R T.up T'.top.clip (haloK S.L λ₀) β b 0
local notation "u'"=> roofK S.L τ.t κ x

set_option linter.unusedVariables false
/-- Normalize on the actual Fort using the chosen evening calibration and our four-box
slack. Does not require the next face-height be at this step's stride. -/
lemma sojourn (hp: Stowable P₀ τ B Z V F₀ A γ Λ α3 ν' κ tol A3)
    (ht:0<s)(hL:T.low=Tq)(hH:T.high=Tq)(hX:Enn R F₀ S.L λ₀ τ.t (1/8) (duo X.P X.K))(hb: |β+δ'|+1≤W')(hm:EveningR c P T.down Tq S.L x τ.t Λ W' F₀ Δ u' u₀ v₀ H' tol) (D:ℝ)(hD:D ≤3*u'):
    ∃ (Y:Voice c N)(w m ξ p:ℝ),
       let Z':= quoteF c Y P₀ S.land Tq T.down P V (haloK S.L x) (β+δ'+p) m
       let Y':= vest c N w (fort S K h N β (s • (X!))) -- proof binder hm
       0<w∧w≤4∧|w-1|≤2*tol+tol^2∧ |p|≤2 ∧ ForceMass b (roofK S.L τ.t κ λ₀) m D ∧
            Enn P F₀ S.L x τ.t (1/8) (duo Y.P Y.K)∧0<ξ∧Y'=ξ • Z' ∧
            (∀ U, advance S K h (s • (X!)) β U=gBody c w (Y' U)) ∧
            1/4 ≤ Stew.Project.unitF true c (D₀ 1) ∧ NormG D₀ F₀ Y' P T.down Tq V.Z.page Δ u₀ v₀ H' (β+δ'+p) m :=by
  obtain ⟨p,Γ,-,-,-,-,-,-,⟨K₀⟩⟩:=hp.ride X.ι X.β (duo X.P X.K) hX
  let G:=K₀.toReliefR
  let t:= G.pQ
  letI:= G.cnt
  let F:=Classical.choice (Tree.select (S.visit K h).ratio S.odd)
  let d:= Collection.vac (Reggae.stock (charm G.R4 Z F₀)) (perfume c (PhysicalNext.Repeat.Song.weighty B.Pq χ F) t)
  let D':= sparksE T P₀ X F₀ B Z G; let m':= mCoeff G.R4 Z F₀; let a:=powerU G.R4 Z F₀; let r':=betaP G.R4 Z F₀
  let U':= park S h P₀ U.X U.Y (haloK S.L λ₀) b; let R':=Real.exp (Real.log (U' 1).det.re)^N*pot c d
  obtain ⟨hG,ha,ha2,hr,hF,hm',hu,hR,hJ⟩:= releaseFirst T P₀ X F₀ B Z G hH F
  have ht':|β+δ'+r'|≤ W':= ((abs_add_le ..).trans (add_le_add_right hr _)).trans hb
  obtain ⟨D₁,M₁,W₁,p₁,hP,hM,hW,hA,hν,hc,hΩ,hZ,hz,hN⟩:= hm.immigrates D' D₀ ⟨Z,hu⟩ hG (β+δ'+r') m' V.Z.page hm' ht'
  let FV:=bio P D' T.down Tq D₀ V.Z.page (β+δ'+r') m'; let GV:=bio P D₁ T.down Tq D₀ V.Z.page (β+δ'+r'+p₁) M₁
  obtain ⟨h1,h2⟩:=canonX a W₁ s R' ha hν (X!) FV GV (funext hZ) hJ
  refine ⟨D₁,W₁*a,M₁,s*R',r'+p₁,mul_pos hν ha,(mul_le_mul hc ha2 ha.le (by norm_num)).trans (by norm_num),?band,?r,?mass,hP,mul_pos ht hR,?_ ,?_,hz,?_⟩
  case band =>
     have ha:|a-1| ≤ tol:= K₀.crown.near
     have hs :0 ≤ tol:= (abs_nonneg _).trans hW
     rw [show W₁*a-1=(W₁-1)+(a-1)+(W₁-1)*(a-1) by ring]
     apply (abs_add_le ..).trans; rw [abs_mul]; exact (add_le_add ((abs_add_le ..).trans (add_le_add hW ha)) (mul_le_mul hW ha (abs_nonneg _) hs)).trans_eq (by ring)
  case r => exact (abs_add_le ..).trans ((add_le_add hr hΩ).trans (by norm_num))
  case mass =>
     have hx := K₀.crown.fourP
     change ForceMass b _ m' (4*_) at hx
     obtain ⟨ht,hc⟩:=abs_lt.mp hM
     exact ⟨fun h=> by linarith only [hx.1 h,hD,hc],fun h=> by linarith only [hx.2 h,hD,ht]⟩
  · rw [← add_assoc]; exact h1
  · rw [h1]; exact h2
  rw [← add_assoc,h1]; exact oasisP F₀ hN (mul_pos ht hR)
end Cairn
end Stratum.Spire
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.Spire.Cairn.sojourn
