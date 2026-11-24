import YM.VMarker.Mottle
import YM.VStages.ExposureY
import YM.VStages.Yarn
import YM.VStages.RegisterY
import YM.VStages.Wardpost
import YM.VStages.Foster
import YM.VStages.PonderY
import YM.VStages.VistaW
import YM.Massive.Aperture.Calendar
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
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
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow N) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

include he
lemma mural_port (Z₀:ℂ→ Pixel (A.ring (B.n k) (i+1)) N)(s:ℝ)(φ:ℝ)(D:Code (A.ring (B.n k) (i+1)) N)(hv:Mural P₀ A X B T V U E Pt k M₀ (i+1) (Struck.Library.grow (dial P₀ A x (i+1)) Z₀) D φ s): PutFrom P₀ A X B T V U E Pt k M₀ i (Struck.Library.grow (dial P₀ A x i) Z₀) D φ s:=by
    have h:= Suburb.terminal P₀ A (i+1) x; rw [notch,start_clock] at h; have h0:=(scaleRay_eq P₀ A (realY P₀ A X E he) i).symm
    obtain ⟨hm,hq,hw,ht,hb,hF,hC,hf⟩:= hv; unfold PutFrom; refine ⟨hm,fun b=>(Spire.Moraine.ident h Z₀ b h0).symm.trans (hq b),Spire.Moraine.diary h D F₀ hw, Spire.Moraine.wider Z₀ h0 D _ _ ht,(fun i=> (by rw [← Spire.pitch_at h]; exact hb i)),hF,(by rw [← Spire.chip_at h]; exact hC),Spire.Moraine.annual h D hf⟩
omit he
-- intrinsic R-spectrum branch lifting. All payments on intervals `[j,cut]` done
structure DomeVoice (Pt:ℕ→BudgetPoint)(i:ℕ)(r:ℝ) where
   Λ :∀ j:ℕ,i≤j→j ≤ n→ Code (A.ring (B.n k) j) N
   δ : ℕ→ℝ
   stored (j:ℕ) (h:i≤j)(hz:j ≤ n): Mural P₀ A X B T V U E Pt k M₀ j (HatWalk P₀ A B Y M₀.tip r x j) (Λ j h hz) (δ j) (r*creditsY P₀ A B M₀ Y x j)
   link (j:ℕ)(h:i≤j)(hz:j<n):Mottle P₀ A X B T V U W E j k Pt (Λ (j+1) (h.trans (Nat.le_succ _)) hz) (Λ j h hz.le) (δ (j+1))
-- assembled witness for arbitrary charged Book.Prep margins. Painting interval condition used above Sails to pay. Start choice at UV.C.
variable (r:ℝ)(hΓ:Shot P₀ A X B T V U E M₀ Y Pt r M₃)
include hΓ
lemma launchD :Nonempty (DomeVoice P₀ A X B T V U W E M₀ Y Pt n r):= by
    obtain ⟨h,hS⟩:= hΓ.leg n le_rfl
    obtain ⟨hq,hX,Yv,he,hZ,hA,φ,hφ,hC,hΨ⟩:=h
    let X (j:ℕ)(h:n≤j)(h':j ≤ n): Code (A.ring (B.n k) j) N:= (le_antisymm h h') ▸ Yv
    refine ⟨X,(fun _=>φ),fun j hp hv=>?_,fun j h hz=>by omega⟩
    have h : j=n:= le_antisymm hv hp; subst j; exact show Harness Yv φ .. from ⟨hq,hX,he,hZ,hA,hφ,hC,hΨ⟩
variable (ht:2*tol+tol^2≤1/2)(hN:2≤ N)(hθ:(∑ b,M₀.tip b)=0)(hs:StampBook P₀ A X E B k n x)
include he hh hp hX ht hN hθ hs
variable (hi:i<n)
lemma upRoute (hi:i<n)(X' : DomeVoice P₀ A X B T V U W E M₀ Y Pt (i+1) r):Nonempty (DomeVoice P₀ A X B T V U W E M₀ Y Pt i r):=by
    let G:= Fz r (i+1); let F':= Library.grow (dial P₀ A x i) G; let H:=HatWalk P₀ A B Y M₀.tip r x i; let s:=creditsY P₀ A B M₀ Y x (i+1); let B₀:=X'.Λ (i+1) le_rfl hi; let q:=clockQ P₀ A x i; let L:=A.spacing i
    have hg:F' 0= F (i+1):=by unfold F' Library.grow; rw [mul_zero]; exact neutral P₀ A X B T V W F Y hh hi _ _
    have hu:H= Bank.LeapY (stepper P₀ A X B T i) Kz (A.next (B.n k) i) F' (V (i+1)) (W i):=by unfold H HatWalk; rw [hops P₀ A X B T V W F Y hh M₀.tip r hi]; rfl
    have hC:= hΓ.leg (i+1) hi; let ψ:=X'.δ
    obtain ⟨D,s₁,hD,hB⟩:= motting P₀ A X B T Z V U W F hp hX E he M₀ B₀ F' H (r*s) hi ht hg hu hs (ψ (i+1)) (mural_port P₀ A X B T V U E M₀ he G _ _ B₀ (X'.stored (i+1) le_rfl hi)) hC.2 (pinnedY P₀ A X B T V W F M₀ Y hh r hi.le hN hθ)
    have h0: hear L H θ q M₀.head=r*creditsY P₀ A B M₀ Y x i:= pricing P₀ A X B T V W F M₀ Y hh r hi.le
    let Ψ j (h:i ≤ j) (hx:j≤n): Code (A.ring (B.n k) j) N := if hv:i=j then hv ▸ D else X'.Λ j (by omega) hx
    let δ j:= if i=j then s₁ else ψ j
    have hΨ (j:ℕ)(h:i<j)(hv:j≤n): Ψ j h.le hv=X'.Λ j h hv ∧ δ j=X'.δ j:= ⟨dif_neg h.ne,if_neg h.ne⟩
    refine ⟨Ψ,δ,fun j h hz=>?_,fun j h hz=>?_⟩
    · by_cases hQ:i=j
      · subst j; rw [show Ψ i h hi.le=D from dif_pos rfl, show δ i=s₁ from if_pos rfl,← h0]; exact hD
      have hv : i<j:=lt_of_le_of_ne h hQ; rw [(hΨ j hv hz).1,(hΨ j hv hz).2]; exact X'.stored j hv hz
    have hg:= hΨ (j+1) (Nat.lt_add_one i|>.trans_le (by omega)) hz; rw [hg.1,hg.2]; by_cases h₀:i=j; · subst j; rw [show Ψ i h hi.le=D from dif_pos rfl]; exact hB
    have hq:=lt_of_le_of_ne h h₀; rw [(hΨ j hq hz.le).1]; exact X'.link j hq hz
lemma domeRoute (i:ℕ)(h:i≤n): Nonempty (DomeVoice P₀ A X B T V U W E M₀ Y Pt i r):=by
    induction h using Nat.decreasingInduction with
    | self=> exact launchD P₀ A X B T V U W E M₀ Y r hΓ
    | of_succ i hi ih=> obtain ⟨D⟩:= ih; exact upRoute P₀ A X B T Z V U W F hp hX E M₀ he Y hh r hΓ ht hN hθ hs hi D
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.domeRoute
