import YM.Massive.Filament.Flyby
import YM.Massive.Lantern.Light
import YM.QCD.Disc.Echo
/-!
# Radius plate schedule.

Across the costs in real stencils K charters retain enough per-flag δ
powers e^(M(tau)^{1/3}). Thus true bolts α countably many at enhancement radius can shrink
to a (repeating-positive) radius at EACH step, with Cauchy cost ∝x² absorbed uniformly. No differentiable
extension across *support* boundaries.

`ρ=4-1/x`, declared at the coarse coordinate x. Later width from `run L x`. This
radius discipline only for mark reading (all signs permit).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Pressure ConnectedActivityE6 Jets.Touch
open Massive.Filament Ruby Fused
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h t a A R C D W r:ℝ}{s z:ℂ} {ι α ν : Type}
variable (L:Side)(hL: 1 < L.val)
namespace Rotary
def chartR(x:ℝ):ℝ:=4-x⁻¹
def Spring (L:Side)(x:ℝ):ℝ:= chartR x / chartR (betaF su x L)
def Rcap (L:Side)(x:ℝ):ℝ:= (Spring L x +1)/2
def lamp (L:Side):ℝ:= su.slopeConstant*Real.log L.val
include hL
lemma bright : 0< lamp L:= mul_pos (Gauge.slopeConstant_pos simple) (Real.log_pos (by exact_mod_cast hL))
lemma spring (x:ℝ) (hx:1 ≤ x) :2< chartR x ∧ 0< Spring L x∧ 1/2 ≤ Spring L x∧ Spring L x< Rcap L x∧ Rcap L x<1 ∧ 1+x ≤ 1+betaF su x L := by
   let z:= chartR x; let y:= betaF su x L; have h:= zero_lt_one.trans_le hx; have hy: y=x+lamp L:= rfl; have hz:= bright L hL; have hp:x< y:=by linarith
   have hg : 3 ≤ z:=by have hb:x⁻¹ ≤1⁻¹:= inv_anti₀ zero_lt_one hx; rw [inv_one] at hb; unfold z chartR; linarith
   have hv:z< chartR y:= sub_lt_sub_left ((inv_lt_inv₀ (h.trans hp) h).2 hp) _
   have hh:0<chartR y:= by linarith
   have he: 0< Spring L x:=div_pos (by linarith : 0<z) hh
   have hk: Spring L x <1:=(div_lt_one hh).2 hv; unfold Rcap; refine ⟨(by linarith : 2<z),he,?_,by linarith,by linarith,add_le_add_right hp.le _⟩
   have hW₀: chartR y ≤4:=sub_le_self _ (inv_nonneg.mpr (h.trans hp).le); exact (le_div_iff₀ hh).2 (by linarith only [hg,hW₀])
lemma deluxe (x:ℝ)(hx:1≤x):
    (1-Spring L x/Rcap L x)⁻¹ ≤ (16*(betaF su x L)^2)*(lamp L)⁻¹:=by
     let y:=betaF su x L; let W:=lamp L; have h := bright L hL; have he:y=x+W:= rfl; have ht:x<y:=by unfold W at he; linarith
     obtain ⟨hZ,hK,h₁,hC,hB,-⟩:=spring L hL x hx; let q:=Spring L x; let r:=Rcap L x; change q<r at hC; change r<1 at hB
     have hp':0<x:= zero_lt_one.trans_le hx; have hv := hp'.trans ht
     have hδ: chartR y-chartR x=W/(x*y):= by unfold chartR; field_simp [hp'.ne',hv.ne']; linarith only [he]
     have hS :0< chartR y:= by have h':0<W/(x*y):= div_pos h (mul_pos hp' hv); linarith
     have hr:0<r:= hK.trans hC
     have ht₀: chartR y ≤4 := sub_le_self _ (inv_nonneg.mpr hv.le)
     have hℓ: r*(1-q/r) * chartR y=(chartR y-chartR x)/2:=by
         have hV:q*chartR y=chartR x:=div_mul_cancel₀ _ hS.ne'; field_simp; unfold r Rcap; change ((q+1)/2-q)*chartR y*2=_; linarith only [hV]
     have hΩ: (1-q/r)⁻¹ = 2 * r * chartR y * x*y / W:=by
         let u:=1-q/r; have hh:0<u:=sub_pos.mpr ((div_lt_one hr).mpr hC); change u⁻¹=_; rw [← one_div, div_eq_div_iff (ne_of_gt hh) (ne_of_gt h)]
         rw [hδ] at hℓ; change r*u*_=_ at hℓ; field_simp at hℓ; linarith only [hℓ]
     change (1-q/r)⁻¹≤_; rw [hΩ]; rw [← div_eq_mul_inv]; apply div_le_div_of_nonneg_right _ h.le
     have he₁ :2*r*chartR y≤8:= calc _ ≤ 2*(1:ℝ)*4 := by gcongr
                                      _ =8:=by norm_num
     change 2*r*chartR y*x*y ≤ 16*y^2; nlinarith only [sq_nonneg y,mul_le_mul_of_nonneg_right (mul_le_mul he₁ ht.le hp'.le (by norm_num : (0:ℝ)≤8)) hv.le]
variable {g:ℝ→ℝ}
-- any fixed initial family K calibration w budget; g witness buy eventually dependent AFTER/post L. At any cutoff side
lemma eventual_receives (hg: Rate su L t (fun i=>(g i)⁻¹)):∀ᶠ x in atTop,0<g x →∀ (s:ℂ),
     2*luster 1 2 s ≤ (‖s‖^2*g x)*taxK L x 1 ∧ beamPay 1 (Rcap L x) (Spring L x) s ≤ (‖s‖^3*g x)*taxK L x 1:=by
     let f i:= 32*(16*(betaF su i L)^2*(lamp L)⁻¹)
     have h :Rate su L (1*↑(2:ℕ)) f:=(Rate.hat.pow 2).mul_left 16|>.mul_right (lamp L)⁻¹|>.mul_left 32
     filter_upwards [eventually_ge_atTop (1:ℝ),upperTax L 1 zero_lt_one _ _ (h.mul hg),upperTax L 1 zero_lt_one _ _ (hg.mul_left 16)] with x hx hA hB hg s; have hτ:=deluxe L hL x hx
     have hv: f x ≤ g x * taxK L x 1:=by apply (mul_inv_le_iff₀ hg).1 at hA; linarith only [hA]
     have hD:(16:ℝ)≤ g x *taxK L x 1:=by apply (mul_inv_le_iff₀ hg).1 at hB; linarith only [hB]
     constructor
     · unfold luster; nlinarith only [mul_le_mul_of_nonneg_left hD (sq_nonneg ‖s‖)]
     unfold beamPay luster; unfold f at hv; linarith only [mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left hτ (by norm_num : (0:ℝ) ≤32)) hv) (show 0≤‖s‖^3 from by positivity)]
omit hL
lemma plus (L:Side) (x a b:ℝ): taxK L x (a+b)=taxK L x a*taxK L x b:=by rw [taxK,taxK,taxK,add_mul, Real.exp_add]
include hL
lemma frostG (hg:Rate su L t (fun i=>(g i)⁻¹)):∀ᶠ x in atTop, 0<g x →∀ (c:Side)(N B:ℕ)(ι:Type)(X:ℂ→ℂ→ Rail c N ι)(h A:ℝ)(s:ℂ), Arc X→(∀ z s:ℂ, ‖z‖<1→‖s‖<1→ Quits (X z s) B 1 (taxK L x 4) A h) → Safe s → Quits (faint X 1 (Spring L x) s) B (‖s‖^2*g x) (taxK L x 3) A h ∧ Quits (tail X (Spring L x) s) B (‖s‖^3*g x) (taxK L x 3) A h:=by
   filter_upwards [eventual_receives L hL hg,eventually_ge_atTop (1:ℝ)] with x HX hξ hg c N B I X v A s hp hB hs
   obtain ⟨-,h₁,-,h₂,h₃,-⟩:= spring L hL x hξ; obtain ⟨hX,hY⟩:= hp.hawk X hB (Real.exp_pos _) hs h₁.le h₂ h₃
   rw [show (4:ℝ)=3+1 from (by norm_num),plus] at hX hY; have hP:= mul_nonneg zero_le_one (fan_pos L (1/3) x).le; have hZ:=HX hg s; exact ⟨watt_press _ _ (Real.exp_pos _) (Real.exp_pos _) (Real.one_le_exp hP) hX hZ.1,watt_press _ _ (Real.exp_pos _) (Real.exp_pos _) (Real.one_le_exp hP) hY hZ.2⟩
end Rotary
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.Rotary.frostG
