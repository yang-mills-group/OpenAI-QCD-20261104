import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Stiffness.Limit
import YM.Massive.Tuner.Common
import YM.Massive.RG.History
import YM.Massive.Pressure.Major
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)


/-!
# Send a cutoff/reference tower on fixed-stride path into an actual Run in the prescribed scheme

Along with all growing-step density/mass estimates on this SAME run before and after blocking.
Existence component, not the desired passage to progressive strides for exact slopes and field
budgets.
-/

open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open YM.Massive.Reading (planeProbe)

def fixed (O:Patch) (K:KernelChoices) (hk:O.Branches K su) : Scheme := {
    J := fun _=> O.J
    choices := K
    step := fun _=> Pike O 0
    admissible := fun _=> hk }
variable (hw: O.Branches T'.bind su) {L' : HaarBudget su}

theorem ratio (hk : O.Branches K su) (m): (fixed O K hk).ratio m=O.L^m:=by
   induction m with
   | zero=> rw [pow_zero,Massive.Scheme.ratio]
   | succ m ih=> rw [Massive.Scheme.ratio,ih,pow_succ]; rfl

theorem expand (i m:ℕ) (hp:i+m=n) : towerQ O B n i k=(fixed O T'.bind hw).side (B.n k) m := by
     unfold towerQ Massive.Scheme.side; rw [feetM,ratio, show n-i=m from (by omega)] -- hp issues

private lemma flight (h: f.val=c.val*O.L.val) (i:ℕ)(X:Pixel f N)(Y:Pixel c N) (hw:0<w) (hY:∀ U,advance (Pike O i) K h X β U=gBody c w (Y U)) : transfer (Pike O 0) K h β w (Cove.light _ ∘ X)= Cove.light _ ∘ Y:=by
  funext p; change Massive.rescale w (advance (Pike O i) K h X β p)=_; rw [hY]; change (Cove.light _ (wearK c N w (wearK c N w⁻¹ (Y p))))=_; rw [wit _ w w⁻¹ (mul_inv_cancel₀ hw.ne')]; rfl

def switch (n : ℕ) (V : ℕ→ℝ) (i : ℕ) := V (n-i)
def alter (n : ℕ) (V : ℕ→ℝ) (i : ℕ) := switch n V (i+1)

/-- Fixed-stride run, same terminal mass for all flavors. -/
def fly (V U Wv:ℕ→ℝ)(n k N:ℕ) : Massive.Run (fixed O T'.bind hw) n (B.n k) N := (fixed O T'.bind hw).run (B.n k) (switch n V) (alter n Wv) (fun _=> U 0) n

variable {K' θcw : ℝ}
variable (hG: Regular L' θcw A K' T' Q B b' x κ τ' g P' X Y D W' k V U Wv A0)
include hG
lemma escrow (he:Even (B.n k).val)(hn:4 ≤ (B.n k).val): (fly B hw V U Wv n k N).Actual:=by
   have h:= hG.mass 0 (by omega)
   unfold fly; exact Massive.Scheme.strict _ _ _ _ (fun m _=> zero_lt_one.trans_le (hG.beta (n-m) (by omega))) (fun m hm=> (hG.vocals (n-(m+1)) (by omega)).1) he hn (fun i=>show U 0+4 ≠0 from ne_of_gt (by linarith only [(abs_le.mp h).1]))

-- relation carries via casting the side only.
def transit {c f:Side} (h : c=f) (X : Density c N): Density f N := h ▸ X
lemma charter (i : ℕ) (hi: i≤n) : ∀ m:ℕ, i+m=n → ∀ (h:towerQ O B n i k=(fixed O T'.bind hw).side (B.n k) m), (fly B hw V U Wv n k N).density m = transit h (Cove.light _ ∘ A0 i):=by
  let S:=fixed O T'.bind hw; let R:=S.run (B.n k) (switch n V) (alter n Wv) (fun _ : Flavor N=> U 0) n; let Y:=S.wilson (B.n k) (switch n V) (fun _ : Flavor N=>U 0) n
  induction i with
  | zero=>
       intro m hm hC; simp at hm; subst m
       have he : R.density n= ⇑Y.density:=by change ⇑(S.toStop (B.n k) (switch n V) (alter n Wv) n n Y.density)=_; rw [Massive.Scheme.entrance]; rfl
       change R.density _ =_; rw [he]; unfold Y; rw [show (Cove.light _ ∘ A0 0)= primalD (towerQ O B n 0 k) N (V 0) (U 0) from funext hG.begin];
       suffices M:∀ f:Side,∀ (h:towerQ O B n 0 k=f), ((⟨V 0,0,fun _=>U 0⟩:Regulator f N).density).toFun= transit h (primalD _ N (V 0) (U 0)) by
           unfold Massive.Scheme.wilson switch; change (Massive.Regulator.density _).toFun=_; convert M _ hC using 2; simp
       intro f h; subst f; rfl
  | succ i ih=>
       intro m hm hC; have he: i+(m+1)=n:=by omega
       obtain ⟨hv,hu,hH,hz⟩:=hG.vocals i hi; have hh: R.density (m+1)= _:=ih (by omega) (m+1) he (expand B hw _ _ he (k:=k))
       have hp : R.density m= transfer (Pike O 0) T'.bind _ (switch n V (m+1)) (alter n Wv m) (R.density (m+1)) := Massive.Run.Carried.eqn (S.carried (B.n k) _ _ Y.density (fun _=> U 0)) (m:=m) (by omega) (by omega) -- binder
       rw [show fly B hw V U Wv n k N=R from rfl,hp, hh]; unfold alter switch; rw [show n-(m+1)=i from (by omega)]
       suffices H: ∀ f c : Side,∀ (ht' : f.val=c.val*O.L.val)(h:towerQ O B n i k=f) (h':towerQ O B n (i+1) k=c), transfer (Pike O 0) T'.bind ht' (V i) (Wv i) (transit h (Cove.light _ ∘ A0 i))=transit h' (Cove.light _ ∘ A0 (i+1)) by exact H _ _ _ _ _ -- auto
       intro f c p he he'; subst f c; exact flight p i _ _ hv hz
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.charter
