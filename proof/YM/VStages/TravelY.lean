import YM.VStages.Flung
import YM.VStages.TunesY
import YM.Massive.Kindred.Carry
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
variable {c f C F L:Side} {J:Patch} {j k k0 n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k0}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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



local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Kin
open Aperture Bank Conductor Conductor.Quant MeasureTheory Sway OrbitG
variable (S K h β N w)
variable (hk: S.patch.Branches K su)
abbrev hoppedQ (V:Pixel f N):= vest c N w (fortQ S K h N β V)
lemma add_birthQ (Q X:Pixel f N) : canQ S h N (Q+X)= canQ S h N Q + canQ S h N X:=by
    funext i; change Kit.sheath 1 _ _= Kit.sheath 1 _ _+Kit.sheath 1 _ _; unfold Kit.sheath; rw [Pi.add_apply, map_add,map_add,add_mul,map_add,smul_add]
set_option quotPrecheck false
local notation "Φ!"=> S.visit K h
variable (X Y:Lanes f N)
include hk
set_option maxHeartbeats 900000
lemma honorQ (V:Grid c): Integrable (fun U=> (Φ!).density β U V • canQ S h N X U) (prior su f):= StepData.push_slice ((Φ!).isKernel hk β) V _ ((Rain.tenderLQ S h X X.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
def travelQ : Lanes f N →ₗ[ℂ] Lanes c N where
  toFun X:= ⟨hoppedQ N w S K h β X, Continuous.comp ((wearK c N w).toLinearMap.continuous_of_finiteDimensional) ((levit c N).continuous.comp (Rain.livingQ S h X K hk X.continuous β))⟩ -- #check order
  map_add' X Y:=by apply ContinuousMap.ext; intro V; change wearK c N w (levit c N (advanceF S K h _ β V))= wearK c N w (levit c N _)+wearK c N w (levit c N _); rw [advanceF, show (canQ S h N ⇑(X+Y)) = _ from add_birthQ N S h X Y, StepData.push_add ( (Φ!).isKernel hk β ) _ _ ( (Rain.tenderLQ _ _ _ X.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ( (Rain.tenderLQ _ _ _ Y.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),Pi.add_apply,map_add,map_add]
  map_smul' z X:= ContinuousMap.ext (fun i=> congr_fun (fireZY ⇑X z (K:=K) (β:=β) (S:=S) (v:=w) (h:=h)) i)
lemma pureShiftQ (V:Grid c): Cove.light _ (fortQ S K h N β X V)=advanceF S K h ⇑X β V:=by
    let g: Grid c→Fields c N:= advanceF S K h X β; let U:=(levit c N (g V)); let p: Fields c N→L[ℝ] Fields c N:= (Grass.grade).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; let F U:= (Φ!).density β U V • canQ S h N X U
    have hG:Plus (g V):=by
       change p (∫ V,F V ∂prior su f)=_; rw [← p.integral_comp_comm (honorQ N S K h β hk X V)]; refine integral_congr_ae (ae_of_all _ fun U=>?_); dsimp only; rw [map_smul]; change _ • Grass.grade (Kit.sheath 1 _ _)=_; rw [← Massive.Transfer.sheath_grade,show Grass.grade _=Cove.light _ _ from (bright (X U))];rfl -- namespace
    let E:EvenA c N:= ⟨g V,hG⟩; exact congr_arg (Cove.light _) (callH E)
lemma actualQ (X:Lanes f N) : Cove.light _ ∘ ⇑(travelQ N w S K h β hk X)= Massive.transfer S K h β w (Cove.light _ ∘ X):= by
    funext i 
    change Cove.light _ (wearK c N w (fortQ S K h N β X i))=_; change changeVars _ (Cove.light _ _)=_; rw [pureShiftQ N S K h β hk]; rfl
-- symmetry, compare
variable (W: Matrix (Flavor N) (Flavor N) ℂ)(hW:W∈unitary _)
omit hk
variable (hx: crew N W X Y)
include hW
lemma cover_tideQ (V:Grid f)(hx:∀ U:Grid f, Wheel N W f (X U)=Y U) : Kit.disguise (flute (Lat.Row c) W) (canQ S h N X V)=canQ S h N Y V:=by
    let T:= ater S h (F:=N) V; let M:=flute (Lat.Row c) W; let D:=flute (Lat.Row f) W; have hp:D∈unitary _:=Sway.unit_f hW
    have hv : M*T*star D=T:=by rw [show M*T=T*D from (Sway.column _ _),Matrix.mul_assoc, (show _ from hp.2), Matrix.mul_one];
    have he:= Kit.compat hp (Sway.unit_f hW) 1 T (Cove.light _ (X V)); rw [hv] at he; exact he.trans (congr_arg (Kit.sheath _ T) (congr_arg Subtype.val (hx V)))
include hk hW
lemma compassQ (hp:crew N W X Y): crew N W (travelQ N w S K h β hk X) (travelQ N w S K h β hk Y):=by
    intro V; change sways _ (wearK c N w (fortQ S K h N β X V))= _; rw [purity]; apply congr_arg (wearK c N w); apply Subtype.ext; change disguise _ (Cove.light _ (fortQ S K h N β X V))=Cove.light _ (fortQ S K h N β Y V); rw [pureShiftQ N S K h β hk,pureShiftQ N S K h β hk];
    let A:=disguise (flute (Lat.Row c) W); let Z:Fields c N →L[ℝ] Fields c N:= A.toLinearMap.toContinuousLinearMap.restrictScalars ℝ
    let F U:=(Φ!).density β U V • canQ S h N X U; change Z (∫ U,F U ∂prior su f)=_; rw [← Z.integral_comp_comm (honorQ N S K h β hk X V)]; refine integral_congr_ae (ae_of_all _ fun i=>?_); dsimp only; rw [map_smul]; exact congr_arg ((Φ!).density β i V • ·) (cover_tideQ N S h X Y W hW i hp)
end Kin
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Kin.pureShiftQ
#print axioms YM.QCD.Acre.Rails.Kin.actualQ
#print axioms YM.QCD.Acre.Rails.Kin.compassQ

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
variable {c f C F L:Side} {J:Patch} {j k k0 n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k0}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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



local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Reference
-- one-step transfer along same stopping parameters. No growth frame of F along unchosen schemes.
variable {A3 tol:ℝ}{E:ℕ→SunR Ω}{Xb:ℕ→ℝ}{Ut:ℕ→Towers J.L}
variable (F₀:Flavor N)(M₀:Arrow N) (B:SparkMesh) {M':ℕ→ SparkMesh} (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E Xb Ut x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{D0 a3 Q₀ ξ:ℝ}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- implicit tol not from above? A3 variables namespace shadow from Bank; outside ended.Bank need declare. see compile.
local notation "xg"=> delay J n i x
local notation "xo"=> delay J n (i+1) x
open Conductor Conductor.Quant High Meridians Ruby High.PrismT Massive.Filament
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*Xb i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)
variable (F:∀ j,ℂ→Pixel (towerQ J B n j k) N)
open Aperture Conductor.Quant
open Kin Sway OrbitG MeasureTheory NormedSpace
variable (X:Lanes f N)
lemma matNext (hK:S.patch.Branches K su) (F:LanternT C N f)(hp:Tied F): Tied ((Kin.travelQ N w S K h β hK).comp F):=⟨fun x L hh=> compassQ N w S K h β hK _ _ L hh (hp.crewT x L hh)⟩ -- arg

end Reference
end Rails
end YM.QCD.Acre
