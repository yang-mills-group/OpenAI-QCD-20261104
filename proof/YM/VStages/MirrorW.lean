import YM.VStages.SightW
import YM.VStages.TotemW
import YM.VStages.Through
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
namespace Affair
open Function High PrismT MeasureTheory Sq Grass Stew.Project
set_option quotPrecheck false
variable {Pt:ℕ→BudgetPoint} {Δ:PlaqAxes} (B: SparkMesh) (T: Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
local notation "q₀"=> clockQ P₀ A x i
local notation "Y₁"=> T.W.state (i+1)
local notation "Y₀"=> T.W.state i
local notation "ϕi"=> stepper P₀ A X B T i
local notation "Lₜ"=> A.spacing i
local notation "CK"=> fun i:ℕ=> A.ring (B.n k) i
local notation "Kq"=> K
local notation "Cₚ"=> (P.stage (A.level i)).clip

abbrev Lodge :Prop:= ∀ i≤n,∀ β:ℝ,Hails P₀ A X B T i β →ArcTime A x i β
structure Tavern (κ:ℝ) (Z:Sheltered P₀ A X B T k Pt Δ)(V U W:ℕ→ℝ)(F: ∀ i,Pixel (A.ring (B.n k) i) N): Prop where
  window (i:ℕ)(hi:i≤n): Hails P₀ A X B T i (V i) ∧ ArcTime A x i (V i) ∧ 1 ≤ V i ∧ |U i| ≤ MassBox P₀ A x i ∧ SupportH P₀ A X B T Pt i k (F i) (V i) (U i)
  bare : F n= CodeG _ N (V n) (U n)
  finish : V 0=x ∧ U 0=MassBox P₀ A x 0* κ
  relay (i:ℕ)(h:i<n): LinkT P₀ A X B T Z i (V i) (V (i+1)) (U i) (W i) (F i) (F (i+1))
variable {κ:ℝ}
variable (hp: entire P₀ A x Pt)(hc:Calm P₀ A X x)
variable (hy: Lodge P₀ A X B T)
include hp hc hy
lemma mirror (hK:|κ|<1):∃ V U W F, Tavern P₀ A X B T κ Z V U W F:=by
    have h (i:ℕ)(hi:i≤n) : ∃ D V U F T',WithMap P₀ A X B T Z i D V U F T':=by
        induction hi using Nat.decreasingInduction with
        | self=> obtain ⟨V,U,F,h⟩:= anchors P₀ A X B T Z hp hc hy; exact ⟨_,V,U,F,id,h⟩
        | of_succ i hi ih=> obtain ⟨D,V,M,F,U,h⟩:= ih; exact rests P₀ A X B T Z hp hc hy hi V M F h
    obtain ⟨D,V,U,F,P,H⟩:= h 0 (by omega)
    obtain ⟨y,hp',hV⟩:= Massive.Shooting.fiber hK P H.live.born H.live.chir; have hQ:y∈D:=by
          by_contra ht; obtain ⟨i,hx⟩:= H.live.goals y ht; unfold Sq.ray at hx; cases i <;> simp [hp',hV,hK.ne] at hx
    choose! w hw using fun i hi=> H.freight y hQ i (by omega) hi
    refine ⟨fun i=> V i y, fun i=> U i y,w,fun i=> F i y,?_ ,H.original y hQ,?_,fun i hi=>hw i hi⟩
    · intro i hi; obtain ⟨hv,hζ,h⟩:= H.budgets y hQ i (by omega) hi; have ht:=hy _ hi _ hv
      have hW: 2 ≤ A.scale x i:=by rw [← Spire.Client.fall (seat P₀ A i) (A.scale x i)]; exact (hc.kind i).low
      exact ⟨hv,ht,by linarith only [ht.1,hW],hζ,h⟩
    obtain ⟨hv,hν⟩:= H.live.site y hQ; rw [hp',mul_zero,add_zero] at hv; exact ⟨by rw [hv]; simp [centre,central],by rwa [hV] at hν⟩

omit hp hc hy
structure SummitBox (Pt:ℕ→BudgetPoint):Prop where
     exits : entire P₀ A x Pt
     charges : Calm P₀ A X x
     caps : Lodge P₀ A X B T
lemma box (P:ℕ→BudgetPoint)(h : Lodge P₀ A X B T)(hP:entire P₀ A x P)(hC:Calm P₀ A X x) (K:PlaqAxes)(ht:0<tol): ∀ᶠ k in atTop,∃ Z : Sheltered P₀ A X B T k P K,
      (SummitBox P₀ A X B T P) ∧ ∀ κ:ℝ,|κ|<1→ ∃ V U W F, Tavern P₀ A X B T κ Z V U W F:=by
   filter_upwards [lanterns P₀ A X hC B T hP K ht] with k hk; obtain ⟨S⟩:=hk; exact ⟨S,⟨hP,hC,h⟩,fun κ H=> mirror P₀ A X B T S hP hC h H⟩
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
