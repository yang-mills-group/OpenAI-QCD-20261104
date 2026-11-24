import YM.QCD.Finch.Levy
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
abbrev ForceMass (m y d x:ℝ):Prop:= (m=y→ x<d)∧(m=-y→ d< -x)
lemma adler (e:Flavor N)(Y:Gem c N I) (T:Gem c N V)(Z:Gem c N J)(F:ℝ→ Gem c N (I⊕J))(Y':F m=weave Y (linen Z m)) (he:Licence B A C l Y) (hp : AnchorT Z B l A G) (hv:512 ≤ b)(hz:0<l)(hh: l^2*m' ≤ ν*h/b)(hf: b/2 ≤ qMass (till Z e 0))(hx:l^2*(d*b) ≥ν*h/8) (hQ: |qMass (till T e 0)|≤ v)(hS:l^2*|qMass (till Y e 0)| ≤ν*h/128)(hm:l^2* |legϑ (F m) T e|≤ K*h)(hΩ:v*K ≤ ν/128)(hc:0<ν)(hJ:0<h)(hl:1/2 ≤ powerU (F m) T e)(hL:0 ≤A): ForceMass m d (mCoeff (F m) T e) m':=by
    let D:= F m; let s:=powerU D T e; let p:=legϑ D T e; let x:=qMass (till Z e 0); let y:=qMass (till T e 0); let u:=qMass (till Y e 0); have ht :mCoeff (F m) T e=s^2*(m*x+u-p*y):=by unfold mCoeff legA; change s^2*(bandQ (till (F m) e 0)-p*y)=_; rw [Y',tune_add Y _ _ he (sizeζ _ _ hp).law hz hL,map_add,tillζ,map_smul]; change s^2*(u+m*x-p*y)=_; rw [add_comm u _]
    have H:= adjust hv hz hh hf hx hQ hS hm hΩ hc hJ hl
    rw [ht]; exact ⟨fun h=>by rw [h]; exact h ▸ H.1,fun hb=> (by rw [hb]; exact hb ▸ H.2)⟩ -- rewrite let s p maybe problem.
open Calm
section epoch
variable (S:Stage)
structure Guard (K U M ν ε F g z:ℝ):Prop where
    K_p:0<K
    U_p:0<U
    M_p:0<M
    ν_p:0<ν
    epsP:0<ε
    F_p:1≤F -- basis
    z_p :0< z
    z_s : z≤1
    bet : 0<g
    Θg  : ε*2+M*ν*2 ≤ K
    betaN: ε*g*2 ≤ ν/128
    ξN : z*(U*K) ≤ν/128
lemma director (M:ℝ)(hk:0<K)(hu:0<u)(hM:0<M)(hz:1 ≤ A)(hc:0<r):∃ ν ε z:ℝ, Guard K u M ν ε A r z:=by
   let ν:= K/(4*M); let ε:= min (K/4) (ν/(256*r)); let z:=min 1 (ν/(128*(u*K))); have hv :0<ν:=by unfold ν; positivity
   have he:0<ε:= lt_min (by positivity) (by positivity); have hξ:0<z:=lt_min zero_lt_one (by positivity)
   refine ⟨ν,ε,z,hk,hu,hM,hv,he,hz,hξ,min_le_left ..,hc,?_ , ?_,?_⟩
   · have hp : ν*(4*M)=K:= by unfold ν; field_simp; -- edit
     have he' : ε≤ K/4:= min_le_left ..; linarith only [he',hp]
   · have hp:= (le_div_iff₀ (by positivity : 0 < 256*r)).mp (min_le_right (K/4) (ν/(256*r))); change ε*_ ≤_ at hp; linarith only [hp]
   have hp:= (le_div_iff₀ (by positivity : 0<128*(u*K))).mp (min_le_right 1 (ν/(128*(u*K)))); change z*_ ≤_ at hp; linarith only [hp]
-- recycle payment budget soft.A.P.C.
lemma soloCash (S:Stage) (L:Side) (ha:0<A)  (N:ℕ) :∀ᶠ x in atTop,
    let p:=radiusB x; let t:= S.supportExponent+1;let h:=Jets.Touch.chip L x
    ∀ v:ℝ,0 ≤ v→ v≤ A*h→ fan L (1/2) x + payment 1 (4*p+2) 0 1 1 (flowM L x) t 0+ payment 1 (4*p+2) 0 1 1 v t 0 ≤ pra L x/2:=by
   filter_upwards [pivotal L S A ha, (Touch.Seat.your L).eventually_ge_atTop 64] with x h hx p t g v hv hK
   have ht : payment 1 (4*p+2) 0 1 1 v t 0≤ payment 1 (4*p+2) 0 1 1 (A*Jets.Touch.chip L x) t 0:=by
       unfold payment degreeIncome; gcongr
       exact inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
   have he: fan L (1/2) x≤ pra L x/4 := by
       rw [fan, ← Real.sqrt_eq_rpow]; have hh :0 ≤pra L x:= (by linarith); nlinarith [Real.sqrt_nonneg (pra L x),Real.sq_sqrt hh]
   linarith
end epoch
end YM.QCD.Finch
