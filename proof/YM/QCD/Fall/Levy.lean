import YM.QCD.Finch.Levy
import YM.QCD.Fall.Wait
/-! # x clocks. L committed. -/
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


-- typo h not declared
lemma adjustR (hD:x≥512)(hp:0<l)(hh: l^2*m ≤ ν*g/x) (he:x/2 ≤ h)(hx: l^2*(V'*x) ≥ ν*g/8)(hz:|C|≤ U)(hq: l^2*|b|≤ ν*g/128)(hb:l^2*|q|≤ K*g)(hΩ:U*K≤ ν/128)(hc:0<ν)(hy:0<g)(hk:1/2 ≤ s) :
     let f (μ:ℝ):=s^2*(μ*h+b-q*C); 2*m < f V' ∧ f (-V') < -(2*m) :=by
    intro F; let z:= l^2; have hi:0<(ν*g)/8:=(by positivity); have hv:0<V':=by by_contra! h; have hh' := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg l) (mul_nonpos_of_nonpos_of_nonneg h (by linarith : 0 ≤ x)); linarith only [hi,hx,hh']
    have ha:x>0:=by linarith
    have hJ:0 ≤K*g:= le_trans (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hb
    have h1 : l^2*(V'*h) ≥ ν*g/16:=by nlinarith only [hx, mul_le_mul_of_nonneg_left he hv.le,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hv.le) (sq_nonneg l)]
    have h2 : l^2* |q*C| ≤ ν*g/128:=by rw [abs_mul,← mul_assoc]; apply (mul_le_mul hb hz (abs_nonneg _) hJ).trans; linarith only [mul_le_mul_of_nonneg_right hΩ hy.le]
    let d:=ν*g/32; have hd:0<d:=by unfold d; positivity
    have hu': l^2*(2*m) ≤ ν*g /256  := by have h:= le_trans hh ((div_le_div_of_nonneg_left (by positivity) (by norm_num) hD)); linarith only [h]
    let a:= l^2* b; have hB : |a|≤ ν*g/128:=(by rw [show |a|=l^2*|b| from (by unfold a; rw [abs_mul,abs_of_nonneg (sq_nonneg _)])]; exact hq)
    let p:= l^2*(q*C); have hP : |p|≤ν*g/128:=by rw [show |p|=l^2*|q*C| from (by unfold p; rw [abs_mul,abs_of_nonneg (sq_nonneg _)])]; exact h2
    obtain ⟨h₁,h₁'⟩:=abs_le.mp hB; obtain ⟨h₂,h₂'⟩:= abs_le.mp hP
    have hx : d ≤ l^2*(V'*h+b-q*C):=by unfold a p at *; unfold d; linarith only [hi,h1,h₂',h₁]
    have ht : d ≤ l^2*(-(-V'*h+b-q*C)):=by unfold a p at *; unfold d; linarith only [hi,h1,h₁',h₂]
    have hy: l^2*(2*m) < s^2*d :=by apply hu'.trans_lt; have hh: (1/4:ℝ) ≤ s^2:=(by nlinarith only [hk, pow_le_pow_left₀ (by norm_num) hk 2]); exact (show ν*g/256<1/4*d from (by unfold d at *; linarith only [hd])).trans_le (mul_le_mul_of_nonneg_right hh hd.le)
    constructor
    · apply lt_of_mul_lt_mul_left _ (show 0 ≤ l^2 from sq_nonneg _); apply (hy.trans_le (mul_le_mul_of_nonneg_left hx (sq_nonneg _))).trans_le; unfold F; rw [mul_left_comm]
    apply lt_of_mul_lt_mul_left _ (show 0 ≤ l^2 from sq_nonneg _); have he:= hy.trans_le (mul_le_mul_of_nonneg_left ht (sq_nonneg _)); unfold F; linarith only [he]

-- sign even if not endpoints exact: yields no overspill quant? target strict.
end YM.QCD.Finch
