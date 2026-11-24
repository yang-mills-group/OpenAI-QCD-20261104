import YM.QCD.Fall.Tie
import YM.QCD.Fall.Wait
/-! # Extra room at the input-to-coarser lift. Stronger output box by retaining extra precision in the mass estimate. Cf `Levy` -- this is *only* the mass box estimates. -/
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
variable {t s τ u r d ε α η K :ℝ}{j k:ℕ}{B:BudgetPoint}
open Jets.Touch Push Push.AbsoluteSums Footprint
open Port AnalyticBridge VerifiedReset Time
variable {x ν m U b w E θ ℓ l z:ℝ}
variable {h q V' C g :ℝ}
local notation "P⁔"=> Jets.Touch.chip

variable {W G M D :ℝ}


lemma extendR (hD:x≥512)(_hp:0<l)(hh: l^2*m ≤ ν*g/x) (he:x/2 ≤ h)(hx: l^2*(V'*x) ≥ ν*g/8)(hz:|C|≤ U)(hq: l^2*|b|≤ ν*g/128)(hb:l^2*|q|≤ K*g)(hΩ:U*K≤ ν/128)(hc:0<ν)(hy:0<g)(hk:1/2 ≤ s) :
     let f (μ:ℝ):=s^2*(μ*h+b-q*C); 4*m < f V' ∧ f (-V') < -(4*m) :=by
    intro F; let z:= l^2; have hi:0<(ν*g)/8:=(by positivity); have hv:0<V':=by by_contra! h; have hh' := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg l) (mul_nonpos_of_nonpos_of_nonneg h (by linarith : 0 ≤ x)); linarith only [hi,hx,hh']
    have ha:x>0:=by linarith
    have hJ:0 ≤K*g:= le_trans (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hb
    have h1 : l^2*(V'*h) ≥ ν*g/16:=by nlinarith only [hx, mul_le_mul_of_nonneg_left he hv.le,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hv.le) (sq_nonneg l)]
    have h2 : l^2* |q*C| ≤ ν*g/128:=by rw [abs_mul,← mul_assoc]; apply (mul_le_mul hb hz (abs_nonneg _) hJ).trans; linarith only [mul_le_mul_of_nonneg_right hΩ hy.le]
    let d:=5*ν*g/128; have hd:0<d:=by unfold d; positivity
    have hu': l^2*(4*m) ≤ ν*g /128  := by have h:= le_trans hh ((div_le_div_of_nonneg_left (by positivity) (by norm_num) hD)); linarith only [h]
    let a:= l^2* b; have hB : |a|≤ ν*g/128:=(by rw [show |a|=l^2*|b| from (by unfold a; rw [abs_mul,abs_of_nonneg (sq_nonneg _)])]; exact hq)
    let p:= l^2*(q*C); have hP : |p|≤ν*g/128:=by rw [show |p|=l^2*|q*C| from (by unfold p; rw [abs_mul,abs_of_nonneg (sq_nonneg _)])]; exact h2
    obtain ⟨h₁,h₁'⟩:=abs_le.mp hB; obtain ⟨h₂,h₂'⟩:= abs_le.mp hP
    have hx : d ≤ l^2*(V'*h+b-q*C):=by unfold a p at *; unfold d; linarith only [hi,h1,h₂',h₁]
    have ht : d ≤ l^2*(-(-V'*h+b-q*C)):=by unfold a p at *; unfold d; linarith only [hi,h1,h₁',h₂]
    have hy: l^2*(4*m) < s^2*d :=by apply hu'.trans_lt; have hh: (1/4:ℝ) ≤ s^2:=(by nlinarith only [hk, pow_le_pow_left₀ (by norm_num) hk 2]); exact (show ν*g/128<1/4*d from (by unfold d at *; linarith only [hd])).trans_le (mul_le_mul_of_nonneg_right hh hd.le)
    constructor
    · apply lt_of_mul_lt_mul_left _ (show 0 ≤ l^2 from sq_nonneg _); apply (hy.trans_le (mul_le_mul_of_nonneg_left hx (sq_nonneg _))).trans_le; unfold F; rw [mul_left_comm]
    apply lt_of_mul_lt_mul_left _ (show 0 ≤ l^2 from sq_nonneg _); have he:= hy.trans_le (mul_le_mul_of_nonneg_left ht (sq_nonneg _)); unfold F; linarith only [he]


-- for the actual `till` estimate
variable {m' v A:ℝ}
lemma adlerFour (e:Flavor N)(Y:Gem c N I) (T:Gem c N V)(Z:Gem c N J)(F:ℝ→ Gem c N (I⊕J))(Y':F m=weave Y (linen Z m)) (he:Licence B A C l Y) (hp : AnchorT Z B l A G) (hv:512 ≤ b)(hz:0<l)(hh: l^2*m' ≤ ν*h/b)(hf: b/2 ≤ qMass (till Z e 0))(hx:l^2*(d*b) ≥ν*h/8) (hQ: |qMass (till T e 0)|≤ v)(hS:l^2*|qMass (till Y e 0)| ≤ν*h/128)(hm:l^2* |legϑ (F m) T e|≤ K*h)(hΩ:v*K ≤ ν/128)(hc:0<ν)(hJ:0<h)(hl:1/2 ≤ powerU (F m) T e)(hL:0 ≤A): ForceMass m d (mCoeff (F m) T e) (4*m'):=by
    let D:= F m; let s:=powerU D T e; let p:=legϑ D T e; let x:=qMass (till Z e 0); let y:=qMass (till T e 0); let u:=qMass (till Y e 0); have ht :mCoeff (F m) T e=s^2*(m*x+u-p*y):=by unfold mCoeff legA; change s^2*(bandQ (till (F m) e 0)-p*y)=_; rw [Y',tune_add Y _ _ he (sizeζ _ _ hp).law hz hL,map_add,tillζ,map_smul]; change s^2*(u+m*x-p*y)=_; rw [add_comm u _]
    have H:= extendR hv hz hh hf hx hQ hS hm hΩ hc hJ hl
    rw [ht]; exact ⟨fun h=>by rw [h]; exact h ▸ H.1,fun hb=> (by rw [hb]; exact hb ▸ H.2)⟩ -- rewrite let s p maybe problem.

end YM.QCD.Finch

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
lemma adlerAnd (e:Flavor N)(Y:Gem c N I) (T:Gem c N V)(Z:Gem c N J)(F:ℝ→ Gem c N (I⊕J))(Y':F m=weave Y (linen Z m)) (he:Licence B A C l Y) (hp : AnchorT Z B l A G) (hv:512 ≤ b)(hz:0<l)(hh: l^2*m' ≤ ν*h/b)(hf: b/2 ≤ qMass (till Z e 0))(hx:l^2*(d*b) ≥ν*h/8) (hQ: |qMass (till T e 0)|≤ v)(hS:l^2*|qMass (till Y e 0)| ≤ν*h/128)(hm:l^2* |legϑ (F m) T e|≤ K*h)(hΩ:v*K ≤ ν/128)(hc:0<ν)(hJ:0<h)(hl:1/2 ≤ powerU (F m) T e)(hL:0 ≤A): ForceMass m d (mCoeff (F m) T e) (2*m') ∧ ForceMass m d (mCoeff (F m) T e) (4*m'):=by
    exact ⟨adlerR e Y T Z F Y' he hp hv hz hh hf hx hQ hS hm hΩ hc hJ hl hL,
           adlerFour e Y T Z F Y' he hp hv hz hh hf hx hQ hS hm hΩ hc hJ hl hL⟩
end YM.QCD.Finch
#print axioms YM.QCD.Finch.adlerAnd
