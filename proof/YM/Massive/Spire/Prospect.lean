import YM.Massive.Stratum.Mesh
import YM.Massive.Spire.Thatch
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
/-! # Launch parameter store

Capture all post-cost permission for the flights in this mixed tower, before
selecting physical volume and before distance from the top of any finite tower.
This does not assert all-∞ scaling estimates on the resulting mixed towers:
the asymptotic estimates here only concern activation of each step (no cut-off
assertion on observable scaling).
-/
variable (R:Rock j)
-- Can purchase further region data for any sufficiently expensive stop.
structure Client (j:ℕ)(R:Rock j)(N:ℕ)(F₀: Flavor N)(χ:Chi) where
    good : 4≤j
    guide : ConnectedActivityE6.Target su R.Z
    A3 :ℝ
    a3 :ℝ
    a4 :ℝ
    fee : 0≤A3
    soft : 0<a3
    h :ℝ
    hH :0<h
    κ :ℝ
    pos :0<κ
    θ :ℝ
    lead :0<θ
    U :ℝ
    V :ℝ
    bound :ℕ -- size requirement in addition to Rock & Epoch
    permit : ∀ tol:ℝ,0<tol→∀ S:Flight j j,S.patch.Branches R.Z.bind su→ bound ≤ S.L.val →∀ (M σ Λ α:ℝ),0<M→ 1 ≤ Λ →0<α→∀ (p:ParcelR),p.Rates R.Z.η→∃ (W C μ:ℝ)(o:Target.Order su W)(l k' n' m:ℕ)(τ:Policy guide R.Z.top N), Billing τ μ a3 a4 ∧ τ.t=θ ∧ (∀ᶠ x:ℝ in atTop,Tall S.patch guide.halo l k' n' m x) ∧∀ᶠ x in atTop, ScreenE τ (passportM j good) S F₀ p R.Z.top.width R.η R.v x R.Z.C Λ R.Z.η (1/8) σ R.signal R.D h κ l k' n' m χ o α M μ C (betaFare S.L R.D) U V tol A3

lemma clients (hj:4 ≤ j)(F₀:Flavor N)(χ:Chi): Nonempty (Client j R N F₀ χ):=by
   have H:=R.lawful
   obtain ⟨a,b,c,t,K,τ,Z,X,Q,n,ha,hb,ht,hK,hτ,h⟩:= legibleH χ F₀ R.Z H.fixedP H.bound H.budget H.clip R.Z.top.width R.v R.D R.signal rfl H.cap H.clearR H.orderEq hj
   exact ⟨⟨hj,Q,a,b,c,ha,hb,t,ht,K,hK,τ,hτ,X,Z,n,fun v hv S hp hm M σ Λ α h₁ h₂ h₃=> h v hv S hp hm R.η M σ Λ α H.flour h₁ h₂ h₃⟩⟩
namespace Client
open Mist YM.Massive.Stratum
variable {R}{F₀:Flavor N}{χ:Chi} (P₀:Client j R N F₀ χ)
local notation "Gₚ"=>passportM j P₀.good
abbrev Vows (t:ℝ)(N:ℕ)(L:Side)(p:ParcelR):= |betaFare L t|+N*|p.b|+1
-- all payable existential
variable (tol:ℝ)
structure Book (S:Flight j j)(Θ σ Λ:ℝ)(P:ParcelR) where
   policy : Policy P₀.guide R.Z.top N
   W :ℝ
   C :ℝ
   μ :ℝ
   o: Target.Order su W
   k0 :ℕ
   k1 :ℕ
   k2 :ℕ
   k3 :ℕ
   bill : Billing policy μ P₀.a3 P₀.a4
   theta : policy.t=P₀.θ
   survey :∀ᶠ x in atTop,Tall S.patch P₀.guide.halo k0 k1 k2 k3 x
   screen :∀ᶠ x in atTop, ScreenE policy (passportM j P₀.good) S F₀ P R.Z.top.width R.η R.v x R.Z.C Λ R.Z.η (1/8) σ R.signal R.D P₀.h P₀.κ k0 k1 k2 k3 χ o (Vows R.D N S.L P) Θ μ C (betaFare S.L R.D) P₀.U P₀.V tol P₀.A3
lemma booking (hp:0<tol)(S:Flight j j)(hs:S.patch.Branches R.Z.bind su)(hz:P₀.bound ≤ S.L.val)(Θ σ Λ:ℝ)(hΘ:0 < Θ)(hΛ:1 ≤ Λ) (P:ParcelR)(hr:P.Rates R.Z.η): Nonempty (Book P₀ tol S Θ σ Λ P):=by
   obtain ⟨W,C,μ,o,j,K,M,Y,w,h₁,h₂,h₃,h₄⟩:= P₀.permit tol hp S hs hz Θ σ Λ (Vows R.D N S.L P) hΘ hΛ (by unfold Vows; positivity) P hr; exact ⟨⟨w,W,C,μ,o,j,K,M,Y,h₁,h₂,h₃,h₄⟩⟩
variable {P₀ tol}
-- arbitrary post-L budget spending, before announcing the actual period and coupling.
abbrev ceilingL (X Y:Town): ℝ:=max (loop X) (loop Y)
def fallback (L:Side)(p:ℝ):= p-su.slopeConstant*Real.log L.val
lemma fall (L:Side)(p:ℝ): run L (fallback L p)=p:=sub_add_cancel p _
structure Book.Alive {Λ tol Θ σ:ℝ}{L:ParcelR}(P₀:Client j R N F₀ χ)(S:Flight j j)(B:Book P₀ tol S Θ σ Λ L) (x:ℝ):Prop where
   structureM:Tall S.patch P₀.guide.halo B.k0 B.k1 B.k2 B.k3 (run S.L x)
   productive:ScreenE B.policy (passportM j P₀.good) S F₀ L R.Z.top.width R.η R.v x R.Z.C Λ R.Z.η (1/8) σ R.signal R.D P₀.h P₀.κ B.k0 B.k1 B.k2 B.k3 χ B.o (Vows R.D N S.L L) Θ B.μ B.C (betaFare S.L R.D) P₀.U P₀.V tol P₀.A3
variable (P₀ tol)
lemma Book.earns {S:Flight j j}{Λ Θ σ:ℝ}{P:ParcelR}(B:Book P₀ tol S Θ σ Λ P):∀ᶠ x in atTop, Book.Alive P₀ S B x:=by
    filter_upwards [(Work.E09.betaF_growth su S.L).eventually B.survey,B.screen] with x hx h; exact ⟨hx,h⟩

abbrev Promises := ∀ (S:Flight j j)(Θ σ Λ:ℝ)(P:ParcelR)(_ : Book P₀ tol S Θ σ Λ P) (_:ℝ), Prop
-- actual schedule aspirations.
variable (A:AtlasH R (passportM j P₀.good) P₀.guide.table)
abbrev stance (i:ℕ) : ℝ := ceilingL (A.towns (i+1)) (A.towns i)
abbrev SlotH (i:ℕ):=Book P₀ tol (A.path i) (A.cost i) (A.gap i) (stance P₀ A i) (A.marine i)
def tote (f: Promises P₀ tol)(Y:∀ i, SlotH P₀ tol A i) (x:ℝ): Prop:=∀ i:ℕ,let s:=A.path i; let y:=fallback s.L (A.scale x i); Book.Alive P₀ s (Y i) y ∧ f _ _ _ _ _ (Y i) y
-- need can require bigger S.L constraint than this.
lemma sifting (hw:0<tol)(K:ℕ)(hK:P₀.bound ≤ K)(hf:∀ E:Patch,E.Branches R.Z.bind su)(f:Promises P₀ tol)(ht: ∀ (S:Flight j j) (Θ σ Λ:ℝ) (P:ParcelR),K ≤ S.L.val → S.patch.Branches R.Z.bind su → P.Rates R.Z.η→∀ Y:Book P₀ tol S Θ σ Λ P,0<σ→1 ≤ Θ →1≤Λ→∀ᶠ x:ℝ in atTop,f S Θ σ Λ P Y x):
    ∃ (A:AtlasH R (passportM j P₀.good) P₀.guide.table) (B:ℝ) (Y:∀ i:ℕ, SlotH P₀ tol A i), (∀ i,K≤(A.length i).val) ∧ Paid A B ∧ ∀ᶠ x in atTop,tote P₀ tol A f Y x:=by
   have e (S:Flight j j)(X Y:Town)(σ Θ:ℝ)(P:ParcelR)(hS:K ≤ S.L.val)(hD: Dispatch R (passportM j P₀.good) S X Y P₀.guide.table σ Θ P):∃ A:ℝ,∃ g:Book P₀ tol S Θ σ (ceilingL X Y) P,∀ x≥A,
       let t:= fallback S.L x; Book.Alive P₀ S g t∧ f _ _ _ _ _ g t:=by
           let H:= hD.applaud.rates; have he :1 ≤ ceilingL X Y:= (ridge X).trans (le_max_left ..)
           obtain ⟨Z⟩:= booking P₀ tol hw S (hf S.patch) (hK.trans hS) Θ σ _ (by have h:= hD.roofF; linarith) he P H
           have hz:Tendsto (fallback S.L) atTop atTop:= tendsto_atTop_add_const_right _ (-(_ * _:ℝ)) tendsto_id -- check
           obtain ⟨x,hx⟩:= eventually_atTop.mp (hz.eventually ((Z.earns P₀ tol).and (ht S Θ σ _ P hS (hf S.patch) H Z hD.grain hD.roofF he)))
           exact ⟨x,Z,hx⟩
   choose! need hN using e
   obtain ⟨A,D,hA,hD,H⟩:= well K R (passportM j P₀.good) P₀.guide.table P₀.good P₀.guide.table_exists hf need
   choose F hF using fun i=> hN _ _ _ _ _ _ (hA i) (A.boat i)
   refine ⟨A,D,F,hA,hD,?_⟩; filter_upwards [scheduled A need _ H] with x hx i; exact hF i _ (hx i)
end Client
end Stratum.Spire
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.Spire.Client.sifting
