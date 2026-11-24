import YM.Massive.Aperture.Calendar
import YM.QCD.Corn.Garbs
import YM.Massive.RG.History
/-! # Evolution of even densities with a linear traveler.
The family over external flavor perturbation is analytic in amplitude (even globally
because we are on a finite torus). Need covariance & positivity not destroyed by projection from the two algebras.
These are additional results on the existing actual transfer in use for all the marker expansions.
-/
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Kin
open Aperture Bank Conductor Conductor.Quant MeasureTheory Sway OrbitG
variable (S K h β N w)
variable (hk: S.patch.Branches K su)
abbrev Wheel (W: Matrix (Flavor N) (Flavor N) ℂ)(c:Side):= sways (Sway.flute (Lat.Row c) W)
abbrev Lanes (n:Side)(N:ℕ):= ContinuousMap (Grid n) (EvenA n N)
-- Norm not required but linear (continuous input). Must ensure Body Stem φ economy.Price.Z analog → K cost.S.Future.I
abbrev hopped (V:Pixel f N):= vest c N w (fort S K h N β V)
lemma add_birth (Q X:Pixel f N) : can S h N (Q+X)= can S h N Q + can S h N X:=by
    funext i; change Kit.sheath 1 _ _= Kit.sheath 1 _ _+Kit.sheath 1 _ _; unfold Kit.sheath; rw [Pi.add_apply, map_add,map_add,add_mul,map_add,smul_add]
set_option quotPrecheck false
local notation "Φ!"=> S.visit K h
variable (X Y:Lanes f N)
include hk
set_option maxHeartbeats 900000
lemma honor (V:Grid c): Integrable (fun U=> (Φ!).density β U V • can S h N X U) (prior su f):= StepData.push_slice ((Φ!).isKernel hk β) V _ ((Rain.tenderL S h X X.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
def travel : Lanes f N →ₗ[ℂ] Lanes c N where
  toFun X:= ⟨hopped N w S K h β X, Continuous.comp ((wearK c N w).toLinearMap.continuous_of_finiteDimensional) ((levit c N).continuous.comp (Rain.living S h X K hk X.continuous β))⟩ -- #check order
  map_add' X Y:=by apply ContinuousMap.ext; intro V; change wearK c N w (levit c N (advance S K h _ β V))= wearK c N w (levit c N _)+wearK c N w (levit c N _); rw [advance, show (can S h N ⇑(X+Y)) = _ from add_birth N S h X Y, StepData.push_add ( (Φ!).isKernel hk β ) _ _ ( (Rain.tenderL _ _ _ X.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ( (Rain.tenderL _ _ _ Y.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),Pi.add_apply,map_add,map_add]
  map_smul' z X:= ContinuousMap.ext (fun i=> congr_fun (fireZ ⇑X z (K:=K) (β:=β) (S:=S) (v:=w) (h:=h)) i)
lemma pureShift (V:Grid c): Cove.light _ (fort S K h N β X V)=advance S K h ⇑X β V:=by
    let g: Grid c→Fields c N:= advance S K h X β; let U:=(levit c N (g V)); let p: Fields c N→L[ℝ] Fields c N:= (Grass.grade).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; let F U:= (Φ!).density β U V • can S h N X U
    have hG:Plus (g V):=by
       change p (∫ V,F V ∂prior su f)=_; rw [← p.integral_comp_comm (honor N S K h β hk X V)]; refine integral_congr_ae (ae_of_all _ fun U=>?_); dsimp only; rw [map_smul]; change _ • Grass.grade (Kit.sheath 1 _ _)=_; rw [← Massive.Transfer.sheath_grade,show Grass.grade _=Cove.light _ _ from (bright (X U))];rfl -- namespace
    let E:EvenA c N:= ⟨g V,hG⟩; exact congr_arg (Cove.light _) (callH E)
lemma actual (X:Lanes f N) : Cove.light _ ∘ ⇑(travel N w S K h β hk X)= Massive.transfer S K h β w (Cove.light _ ∘ X):= by
    funext i 
    change Cove.light _ (wearK c N w (fort S K h N β X i))=_; change changeVars _ (Cove.light _ _)=_; rw [pureShift N S K h β hk]; rfl
-- symmetry, compare
variable (W: Matrix (Flavor N) (Flavor N) ℂ)(hW:W∈unitary _)
def crew (A:Pixel f N)(C:Pixel f N):Prop:=∀ i:Grid f,Wheel N W f (A i)=C i -- binder order.
omit hk
variable (hx: crew N W X Y)
include hW
lemma cover_tide (V:Grid f)(hx:∀ U:Grid f, Wheel N W f (X U)=Y U) : Kit.disguise (flute (Lat.Row c) W) (can S h N X V)=can S h N Y V:=by
    let T:= ater S h (F:=N) V; let M:=flute (Lat.Row c) W; let D:=flute (Lat.Row f) W; have hp:D∈unitary _:=Sway.unit_f hW
    have hv : M*T*star D=T:=by rw [show M*T=T*D from (Sway.column _ _),Matrix.mul_assoc, (show _ from hp.2), Matrix.mul_one];
    have he:= Kit.compat hp (Sway.unit_f hW) 1 T (Cove.light _ (X V)); rw [hv] at he; exact he.trans (congr_arg (Kit.sheath _ T) (congr_arg Subtype.val (hx V)))
include hk hW
lemma compass (hp:crew N W X Y): crew N W (travel N w S K h β hk X) (travel N w S K h β hk Y):=by
    intro V; change sways _ (wearK c N w (fort S K h N β X V))= _; rw [purity]; apply congr_arg (wearK c N w); apply Subtype.ext; change disguise _ (Cove.light _ (fort S K h N β X V))=Cove.light _ (fort S K h N β Y V); rw [pureShift N S K h β hk,pureShift N S K h β hk];
    let A:=disguise (flute (Lat.Row c) W); let Z:Fields c N →L[ℝ] Fields c N:= A.toLinearMap.toContinuousLinearMap.restrictScalars ℝ
    let F U:=(Φ!).density β U V • can S h N X U; change Z (∫ U,F U ∂prior su f)=_; rw [← Z.integral_comp_comm (honor N S K h β hk X V)]; refine integral_congr_ae (ae_of_all _ fun i=>?_); dsimp only; rw [map_smul]; exact congr_arg ((Φ!).density β i V • ·) (cover_tide N S h X Y W hW i hp)
end Kin
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Kin.pureShift
#print axioms YM.QCD.Acre.Rails.Kin.actual
#print axioms YM.QCD.Acre.Rails.Kin.compass
