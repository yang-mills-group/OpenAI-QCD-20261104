import YM.Roan.Realm
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
noncomputable abbrev costB (k n:ℕ):ℝ:=1/(n:ℝ)^k
-- post.K budget eventually beats positive pure. no cold η=0 during recurrence. real.M.
lemma eventually_fuel (g:ℕ→ℝ)(h:Fuel g)(q:ℕ)(p:ℝ)(hp:0<p): ∀ᶠ k:ℕ in atTop,∀ᶠ n:ℕ in atTop, costB k n * |g n| < costB q n * p:=by
       obtain ⟨K,d,hK,hD⟩:= h.gains
       let H:= K* (2:ℝ)^d
       filter_upwards [eventually_gt_atTop (d+q)] with k hk; filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (H/p),eventually_ge_atTop (1:ℕ)] with n hx hp'; let x:ℝ:=n; have he:1 ≤ x:=Nat.one_le_cast.mpr hp'; have h0:0<x:=zero_lt_one.trans_le he; have h1:0<x^k:=pow_pos h0 _; have h2:0<x^q:=pow_pos h0 _
       have hr: |g n| ≤ H*x^d:=((hD _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show x+1 ≤ 2*x from (by linarith only [he])) d) hK).trans_eq (by unfold H; rw [mul_pow]; ring)))
       have hm:H < x*p:=(div_lt_iff₀ hp).mp hx
       change (1/x^k) * |g n| < (1/x^q)*p -- fix
       rw [div_mul_eq_mul_div,div_mul_eq_mul_div,one_mul,one_mul]; apply (_root_.div_lt_div_iff₀ h1 h2).2
       refine lt_of_lt_of_le (mul_lt_mul_of_pos_right (hr.trans_lt (mul_lt_mul_of_pos_right hm (pow_pos h0 _))) h2) ?_
       calc (x*p*x^d)*x^q= p*x^(d+q+1):=by rw[pow_add,pow_add]; ring
            _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (by omega)) hp.le
lemma invC (k:ℕ):Fuel (fun n=>(costB k n)⁻¹):=by
          simp_rw [costB,one_div,inv_inv]; exact Fuel.pow _ Fuel.self k
-- choose M remedy for north = baseline 2B+3 n*l*...B; south with extras ∼poly n. spending
local notation "R₀"=> (Fintype.card (Rings 10):ℝ)
local notation "L4"=> L^4
local notation "L5"=>L^5
local notation "A4" => ((L4*R₀)*(α*u^8))
local notation "A5"=> ((L5*R₀)*(α*u^8))
variable (F:ℕ→ℝ)
noncomputable def roomM (n:ℕ):ℝ:=1+(F n+F n+3*((n:ℝ)*(A4*(F n))))
local notation "Mτ" x:arg=> roomM u α L F x
variable (hu:0<u)(ha:0 ≤ a)(hα:0 ≤ α)(hL:3≤L)(hF:Fuel F)(hf:∀ᶠ n in atTop,0 ≤ F n)
local notation "τ" L:arg n:arg=> (F n+2*(L*a+1)*Mτ n)
local notation "Xδ" n:arg k:arg L:arg=> L*R₀*(2*costB k n)
local notation "Ψ" L:arg n:arg=> (L*R₀*2)*(τ L n)
local notation "φ" n:arg=> (Ψ L4 n+20*Mτ n)
local notation "Φ5" n:arg=> (A5*Ψ L5 n+ (Ψ L5 n)+ 20*Mτ n)
local macro "pay_road" : tactic => `(tactic| repeat' first | assumption | exact Fuel.cons _|exact Fuel.self | apply Fuel.add|apply Fuel.mul|apply Fuel.pow)
include hu ha hα hL hF hf
lemma shapeT (E:ℕ):∀ᶠ k:ℕ in atTop,∀ᶠ n:ℕ in atTop, FundX u a α (costB k n) L4 L5 (Mτ n) (F n) (20*costB k n) (costB E n) n:=by
       have hL4:0<L4:=pow_pos (by linarith only [hL]) _; have hL5:0<L5:=pow_pos (by linarith only [hL]) _
       have h:Fuel (roomM u α L F):=by unfold roomM; pay_road
       let g₁:=fun i:ℕ=>(i:ℝ)* (φ i); let G₁(i:ℕ):ℝ:= g₁ i+3*i*(A4*g₁ i+ Ψ L4 i); let g₂:=fun i:ℕ=> (i:ℝ)*(Φ5 i); let G₂(i):ℝ:=Ψ L5 i+ 3*g₂ i
       have ht:Fuel g₁:=by unfold g₁; pay_road
       have he:Fuel G₁:=by unfold G₁; pay_road
       have hv:Fuel g₂:=by unfold g₂; pay_road
       have hp:Fuel G₂:=by unfold G₂; pay_road
       filter_upwards [eventually_fuel g₁ ht E 1 zero_lt_one,eventually_fuel g₂ hv E 1 zero_lt_one,eventually_fuel G₁ he 0 1 zero_lt_one,eventually_fuel G₂ hp 0 1 zero_lt_one] with k ha₂ h₁ h₂ h₃
       filter_upwards [hf,ha₂,h₁,h₂,h₃] with n hG ha₂ ht hx hp
       let z:=costB k n; have hz:0 ≤ z:=div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _); have hG₁:z*G₁ n<1:= (mul_le_mul_of_nonneg_left (le_abs_self _) hz).trans_lt (by simpa [z,costB] using hx); have hG₂:z*G₂ n<1:= (mul_le_mul_of_nonneg_left (le_abs_self _) hz).trans_lt (by simpa [z,costB] using hp)
       let B:=F n; have hD:0 ≤ A4:= by positivity
       have hQ:Mτ n = 1+(B+B+3*((n:ℝ)*(A4*B))):=rfl; have hh:F n ≤ F n + F n + 3*((n:ℝ)*(A4*F n)):= (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right (by positivity)); have hm:(Mτ n)>0:=by rw[hQ]; exact add_pos_of_pos_of_nonneg zero_lt_one (hG.trans hh)
       refine ⟨hm,mul_nonneg (by norm_num) hz,hG,?_ ,?_ ,?_ ,?_⟩
       · have hA:= add_lt_add_left hG₁ (B+B+3*((n:ℝ)*(A4*B))); apply (_:_ = z*G₁ n+(B+B+3*((n:ℝ)*(A4*B)))) |>.le.trans_lt hA; unfold G₁ g₁ B z; ring
       · apply (_:_ = z*g₁ n) |>.le.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hz).trans (ha₂.le.trans_eq (mul_one _))); unfold z g₁; ring
       · apply (_: _ = z*G₂ n+F n) |>.le.trans_lt ((add_lt_add_left hG₂ (F n)).trans_le _)
         · unfold G₂ g₂ z; ring
         exact add_le_add_right hh _
       apply (_:_=z*g₂ n) |>.le.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hz).trans (ht.le.trans_eq (mul_one _))); unfold z g₂; ring
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.shapeT
