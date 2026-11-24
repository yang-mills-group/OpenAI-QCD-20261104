import YM.QCD.Finch.Tie
import YM.QCD.Fall.Levy
/-! # Outside sign for perturbative growth region after volume-large gauge projection. Lean `legA`. Uses two heights and two clocks. No continuity selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para Metric Set
variable {t s τ u r d ε α η K m m' ν l h b x W A C G v :ℝ}{j k:ℕ}{B:BudgetPoint}
open Jets.Touch Push Push.AbsoluteSums Footprint WilsonStartup Port AnalyticBridge VerifiedReset Time
open Quotes

lemma adlerR (e:Flavor N)(Y:Gem c N I) (T:Gem c N V)(Z:Gem c N J)(F:ℝ→ Gem c N (I⊕J))(Y':F m=weave Y (linen Z m)) (he:Licence B A C l Y) (hp : AnchorT Z B l A G) (hv:512 ≤ b)(hz:0<l)(hh: l^2*m' ≤ ν*h/b)(hf: b/2 ≤ qMass (till Z e 0))(hx:l^2*(d*b) ≥ν*h/8) (hQ: |qMass (till T e 0)|≤ v)(hS:l^2*|qMass (till Y e 0)| ≤ν*h/128)(hm:l^2* |legϑ (F m) T e|≤ K*h)(hΩ:v*K ≤ ν/128)(hc:0<ν)(hJ:0<h)(hl:1/2 ≤ powerU (F m) T e)(hL:0 ≤A): ForceMass m d (mCoeff (F m) T e) (2*m'):=by
    let D:= F m; let s:=powerU D T e; let p:=legϑ D T e; let x:=qMass (till Z e 0); let y:=qMass (till T e 0); let u:=qMass (till Y e 0); have ht :mCoeff (F m) T e=s^2*(m*x+u-p*y):=by unfold mCoeff legA; change s^2*(bandQ (till (F m) e 0)-p*y)=_; rw [Y',tune_add Y _ _ he (sizeζ _ _ hp).law hz hL,map_add,tillζ,map_smul]; change s^2*(u+m*x-p*y)=_; rw [add_comm u _]
    have H:= adjustR hv hz hh hf hx hQ hS hm hΩ hc hJ hl
    rw [ht]; exact ⟨fun h=>by rw [h]; exact h ▸ H.1,fun hb=> (by rw [hb]; exact hb ▸ H.2)⟩ -- rewrite let s p maybe problem.
open Calm
section epoch
variable (S:Stage)


-- recycle payment budget soft.A.P.C.

end epoch
end YM.QCD.Finch
