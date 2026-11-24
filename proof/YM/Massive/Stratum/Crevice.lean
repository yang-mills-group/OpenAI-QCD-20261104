import YM.Massive.Stratum.Elevation
import YM.QCD.Raft.Roads
/-!
# One step's two endpoint parcels, seated in a **common** invoice

Presentations are themselves taken from the exact same underlying tables by
forgetting excess proofs of budget. No need to identify field representations
just from agreeing at the level of these price estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog.Mist
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03 Voyage
open YM.Massive.Stratum Raft Raft.ParcelR
open scoped Matrix Topology ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}

/-- Canonical *endpoint budget*. Other price parameters carried on edges. -/
def rate (T:Ledger):ParcelR:=
    ⟨T.1.1.r,T.1.2.r,T.2.r,T.1.1.bill,T.1.2.bill,T.2.bill,1,0,0⟩

structure Buoy (T:Ledger)(P:ParcelR):Prop where
 firstM:P.r≤T.1.1.r
 firstCap:T.1.1.bill≤P.c
 secondM:P.s≤T.1.2.r
 secondCap:T.1.2.bill≤P.d
 thirdM:P.t≤T.2.r
 thirdCap:T.2.bill≤P.e

def Buoy.keep {T:Ledger}{P:ParcelR} (h:Buoy T P) {η:ℝ}(he:Rates P η)(X:SunR (rate T)): SunR P:=
    ⟨X.X.trims he.hr.le h.firstM h.firstCap, X.Y.trims he.hs.le h.secondM h.secondCap,X.Z.trim h.thirdM h.thirdCap⟩
lemma Buoy.keep_page {T:Ledger}{P:ParcelR} (h:Buoy T P){η:ℝ}(he:Rates P η)(X:SunR (rate T)): (h.keep he X).Z.page=X.Z.page:=rfl
lemma Buoy.keep_power {T:Ledger}{P:ParcelR} (h:Buoy T P){η:ℝ}(he:Rates P η)(X:SunR (rate T)): (h.keep he X).powerG=X.powerG:=rfl

/-- One permit to run at the same parcel, returned as part of the
*pre-coupling (post-stride) budget expenses*. -/
structure Bonded (J:Plan j)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(X Y: Ledger)(P:ParcelR):Prop where
 near:Buoy X P
 far:Buoy Y P
 rates:Rates P η
 sails (V:Back E K j j p u v) (F:Avenue V η Ω Θ) (S:SunR (rate X)):
      ∃ (S':SunR (rate Y)) (α:ℝ),BirthR P J V F (near.keep rates S) (far.keep rates S') α
lemma bonded (J:Plan j)(X Y:Ledger)(he:0<η)(h:Story J J E K p u v η Ω Θ X Y):∃ P:ParcelR,Bonded J E K p u v η Ω Θ X Y P:=by
  obtain ⟨⟨h,hT⟩,b,l,hL,H⟩:=h
  let P:ParcelR:=⟨min X.1.1.r Y.1.1.r,min X.1.2.r Y.1.2.r,min (min X.2.r Y.2.r) (η/2),max X.1.1.bill Y.1.1.bill,max X.1.2.bill Y.1.2.bill,max X.2.bill Y.2.bill,b.r,b.bill,l⟩
  have hx:Buoy X P:= ⟨min_le_left ..,le_max_left ..,min_le_left ..,le_max_left ..,(min_le_left ..).trans (min_le_left ..),le_max_left ..⟩; have hy:Buoy Y P:= ⟨min_le_right ..,le_max_right ..,min_le_right ..,le_max_right ..,(min_le_left ..).trans (min_le_right ..),le_max_right ..⟩
  have hr:Rates P η:=⟨lt_min X.1.1.live Y.1.1.live, lt_min X.1.2.live Y.1.2.live, lt_min (lt_min X.2.live Y.2.live) (by positivity), X.1.1.good.trans hx.firstCap, X.1.2.good.trans hx.secondCap,X.2.good.trans hx.thirdCap,b.live,b.good,hL,min_le_right ..⟩
  refine ⟨P,hx,hy,hr,fun V F S=>?_⟩
  obtain ⟨U₁,h₁⟩:=h V F S.X; obtain ⟨U₂,h₂⟩:=hT V F S.X U₁ S.Y h₁; obtain ⟨α,Z,hα,hZ⟩:= H V F S.X S.Y S.Z
  exact ⟨⟨U₁,U₂,Z⟩,α,h₁,h₂,hα,hZ⟩

lemma blank (X:Ledger): ∃ (T:SunR (rate X)), T.X.lamp=0∧ T.Y.lamp=0∧∀ i,(T.Z.page i).coeff=0:=by
  obtain ⟨P,hP⟩:= virgin 1 X.1.1.live.le X.1.1.good
  obtain ⟨Q,hQ⟩:= virgin 2 X.1.2.live.le X.1.2.good
  obtain ⟨R,hR⟩:= soil X.2.live X.2.good
  exact ⟨⟨P,Q,R⟩,hP,hQ,hR⟩
end YM.QCD.Fog.Mist
#print axioms YM.QCD.Fog.Mist.bonded
