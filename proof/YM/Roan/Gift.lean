import YM.Roan.Slow
import YM.Tinus.WoodR
import YM.Roan.Croft
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
set_option quotPrecheck false
variable (u a α ε L Q M B C D θ e x b eΛ g t₀ R:ℝ)
/- purchase rates on unbounded n.Fuel real poly. all receipts post calibration -/
open MassiveQCD.Sample.Basal.Rates
local notation "R₀"=> (Fintype.card (Rings 10):ℝ)
local notation "L4"=> L^4
local notation "L5"=>L^5
local notation "A4" => ((L4*R₀)*(α*u^8))
local notation "A5"=> ((L5*R₀)*(α*u^8))
variable (F:ℕ→ℝ)
local notation "Mτ" x:arg=> roomM u α L F x
variable (hu:0<u)(ha:0 ≤ a)(hα:0 ≤ α)(hL:3≤L)(hF:Fuel F)(hf:∀ᶠ n in atTop,0 ≤ F n)
local notation "τ" L:arg n:arg=> (F n+2*(L*a+1)*Mτ n)
local notation "Xδ" n:arg k:arg L:arg=> L*R₀*(2*costB k n)
local notation "Ψ" L:arg n:arg=> (L*R₀*2)*(τ L n)
local notation "φ" n:arg=> (Ψ L4 n+20*Mτ n)
local notation "Φ5" n:arg=> (A5*Ψ L5 n+ (Ψ L5 n)+ 20*Mτ n)
local macro "pay_road" : tactic => `(tactic| repeat' first | assumption | exact Fuel.cons _|exact Fuel.self | apply Fuel.add|apply Fuel.mul|apply Fuel.pow)
include hu ha hα hL hF hf
variable (hX:Signature C D)
local notation "bM" x:arg =>(2*(D*C*Mτ x)+2)
local notation "Bp" k:arg n:arg=>costB k n
include hX
set_option maxHeartbeats 600000 in
lemma giftX :∀ᶠ k₁:ℕ in atTop,∀ᶠ g:ℕ in atTop,∀ᶠ k₂:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ᶠ n:ℕ in atTop,let e:=costB k₂ n; Pueblo u a α (costB k n) L (Mτ n) (F n) C D (20*costB k n) e (costB k₁ n) (bM n) e (costB g n) e n:=by
      let p:=roomM u α L F; let b:=fun i=> bM i; have hh:Fuel p:=by unfold p roomM; pay_road
      have hx:Fuel b:=by unfold b; pay_road
      have hp:= eventually_fuel (fun _=>(6:ℝ)) (Fuel.cons _) 0 (1/4) (by norm_num)
      let M:=fun i=>D*C*p i
      have hK:= eventually_fuel (fun i=>24*b i*6) (by pay_road) 0 (1/4) (by norm_num)
      filter_upwards [hp,hK] with k₁ hx₁ hp
      have hG:=eventually_fuel (fun i=>2* (6*(2*M i))) (by unfold M; pay_road) k₁ (1/2) (by norm_num)
      have hxG:= eventually_fuel (fun _=>(1:ℝ)) (Fuel.cons 1) 0 1 zero_lt_one
      filter_upwards [hG,hxG] with g hv hQ
      have hl:= eventually_fuel (fun _=>(D*C+2)) (Fuel.cons _) k₁ 1 zero_lt_one; have hA:= eventually_fuel (fun i=>100*b i*(D*C+1)) (by pay_road) g 1 zero_lt_one; have hZ:= eventually_fuel (fun i=>2*(M i)+D*C+3+(1+6:ℝ)) (by unfold M; pay_road) k₁ (1/2) (by norm_num)
      filter_upwards [hl,hA,hZ,hxG] with k₂ heK hAK heT h3
      apply (shapeT u a α L F hu ha hα hL hF hf k₂).mono; intro k hk
      filter_upwards [hk,hx₁,hp,hv,hQ,heK,hAK,heT,eventually_gt_atTop 0,h3] with n hn hk₁ hp hG h1 he hA hz hN hR
      let e:=costB k₂ n; let x:=costB k₁ n; let q:=costB g n; have hC:=hX.pos; have hD:=hX.ng; have hhK:0<p n:= hn.m_ng; have hq:0<x:=by unfold x costB; positivity
      have hE:0< e:=by unfold e costB; positivity
      have hΩ:0 < q:=by unfold q costB; positivity
      let B:= b n; have hB:1 ≤B:=by unfold B b; have hp:M n>0:= mul_pos (by positivity) hhK; change 1 ≤2*M n+2; linarith only [hp]
      have hP:e ≤1:=by simpa [e,costB] using hR.le
      refine ⟨hE,hX,hn,hE,hB,?_,?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩
      · unfold B b at hB; exact add_le_add_right (hP.trans (by norm_num:(1:ℝ)≤2)) _ -- wait add_le_add_right h _ converts _+e right yes.
      · change D*C*e+e+e≤x; rw[show D*C*e+e+e=e*(D*C+2) from by ring]; exact (mul_le_mul_of_nonneg_left (le_abs_self _) hE.le).trans (he.le.trans_eq (mul_one _))
      · rw[mul_comm 6]; exact (mul_le_mul_of_nonneg_left (le_abs_self _) hq.le).trans (hk₁.le.trans_eq (by unfold costB; simp))
      · change 6*x*(24*B) ≤ _; rw [show 6*x*(24*B)=x*(24*B*6) from by ring]; exact (mul_le_mul_of_nonneg_left (le_abs_self _) hq.le).trans (hp.le.trans_eq (by unfold costB; simp))
      · change 100*B*(D*C*e+e) ≤ q; rw [show _ *(D*C*e+e)= e*(100*B*(D*C+1)) from by ring]; exact (mul_le_mul_of_nonneg_left (le_abs_self _) hE.le).trans (hA.le.trans_eq (mul_one _))
      · simp only [abs_one,costB,pow_zero,one_div_one,one_ne_zero,not_false_eq_true,mul_one] at h1; exact h1.le
      · change 2*e*M n+D*C*e+3*e+2*(6*(2*M n)*q)+ (1+6)*e ≤ x; have he:e*(2*M n+D*C+3+(1+6)) ≤ x*(1/2):=(mul_le_mul_of_nonneg_left (le_abs_self _) hE.le).trans hz.le; have h:q* (2*(6*(2*M n))) ≤ x*(1/2):=(mul_le_mul_of_nonneg_left (le_abs_self _) hΩ.le).trans hG.le; nlinarith only [h,he]
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.giftX
