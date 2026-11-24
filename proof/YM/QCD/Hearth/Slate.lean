import YM.QCD.Glass.Celebrate
import YM.QCD.Hearth.Read
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
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ: Policy Q T'.top N}
variable (F₀: Flavor N) {M':ℕ→SparkMesh}
variable {E:ℕ→SunR Ω}{X:ℕ→ℝ}{T:ℕ→Towers J.L}
structure CanonPan (T':Teller su) (Q:ConnectedActivityE6.Target su T')(J:Patch)(F₀: Flavor N)(a d D:ℝ):Prop where
    songs :∃ (V:ℕ→Bed)(T:ℕ→ Towers J.L) (σ γ δ v η:ℝ)(Ω:ParcelR) (s κ:ℝ) (τ:Policy Q T'.top N), 0<η ∧ 0<κ∧ 0<τ.t∧1 ≤ v∧ 0≤ s ∧ Soil T'.bind T'.top.clip J T'.η η T'.C V T∧ ReadyR Ω (passportM J.J J.order_cut) J T'.bind T'.top.clip a d T'.η T'.C T'.C ∧∃ l:ℕ,∀ᶠ x in atTop, ∃ B:SparkMesh,Even (B.n 0).val ∧ B.n 0=sFirst J.L l (run J.L x) ∧∀ n,∃ (S:ℕ→SparkMesh)(g:PulseRide T'.bind T'.top.clip J a d S n)(U:ℕ→SunR Ω)(Y:ℕ→ℝ) (P:ℕ→BudgetPoint), Invoice g Q.table V T σ γ δ D v ∧∀ k:ℕ,Storyboard n k T' B F₀ g P U Y κ x τ.t D s (⟨(0,1),by decide⟩:PlaqAxes)
lemma heraP (h:T'.top.clip.direct≤1)(hp:T'.top.supportExponent=2)(hx₀:T'.top.width=a)(hd:d ≤T'.top.paths)(he:PressR J T' Q F₀ χ a d D): CanonPan T' Q J F₀ a d D:=by
   constructor
   obtain ⟨V,T,Y,σ,γ,δ,v,η,W',κ,H,W,z,μ,Z,A',o,τ,hv,hη,hh,hR,hW,hκ,hH,ht,l,hG⟩:= he.value
   let β:PlaqAxes:= ⟨(0,1),by decide⟩; obtain ⟨r,hr⟩:= eventually_atTop.mp (High.PrismT.coverE F₀ β T'.top Z (roofsK J.L κ τ.t) hp τ.t ht) -- args
   refine ⟨V,T,σ,γ,δ,v,η,Y,W',κ,τ,hη,hκ,ht,hv,hW,hh,hR,l,?_⟩; filter_upwards [hG,fruitful (L:=J.L) F₀ h hκ ht,eventually_ge_atTop r] with x hx hy hr'
   obtain ⟨B,hB,hX,hC,he⟩:= hx; refine ⟨B,hB,hX,fun n=>?_⟩; obtain ⟨S,g,U,Y,hg,hE⟩:= he n; obtain ⟨P,hP⟩:= readsX _ F₀ g hE (⟨(0,1),by decide⟩:PlaqAxes) hy hg hp hx₀ hd hC (fun y k=> hr y (hr'.trans k))
   exact ⟨S,g,U,_,P,hg,hP⟩ -- metav.
variable (χ:Chi)
include χ
lemma starlit (h:N≤8)(K:KernelChoices)(hj:4 ≤ j):∃ (T': Teller su), T'.bind=K ∧ T'.top.supportExponent=2 ∧ T'.top.clip.direct≤1∧∃ (Q:ConnectedActivityE6.Target su T')(s t D:ℝ)(m:ℕ), s=T'.top.width ∧t ≤T'.top.paths∧ 0 ≤ D∧512 ≤ m ∧∀ J:Patch,J.J=j→ J.Branches K su→ m ≤J.L.val→ 2*(D+3) ≤ subG N*Real.log J.L.val∧ CanonPan T' Q J F₀ s t D:=by
    obtain ⟨T,hk,hδ,hV,Q,s,t,D,m,h0,h1,h2,h3,h4⟩:= canopyPanel F₀ χ hj K h
    subst K; exact ⟨T,rfl,hδ,hV,Q,s,t,D,m,h0,h1,h2,h3,fun J hv hp hx=>let hh:= h4 J hv hp hx; ⟨hh.1, heraP F₀ hV hδ h0.symm h1 hh.2⟩⟩
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.starlit
