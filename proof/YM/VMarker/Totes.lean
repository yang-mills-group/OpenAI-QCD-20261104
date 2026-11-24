import YM.VMarker.Limbs
import YM.MassiveQCD.Plate.Prize
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k B N:ℕ}{h θ φ b t C τ ε v w d₁ z x δ A:ℝ}{U I J:Type}[Fintype I]
namespace Film
variable (p:I→Site c)(a:ℝ)(S:Set (Finset I))(Y:Cove.Hat c)
local notation "Z"=> coverNumber B Y.place
open Pressure Orbit Jets.Touch ConnectedActivityE6
variable (L:Side)(M:ℝ)
namespace Surplus
open QCD.Kites Finch Acre Acre.Rails
lemma grantK (a H V:ℝ)(ι:ℕ)(ha:0<a)(_hv:0 ≤ V)(h:H>V)(w:ℝ→ℝ)(hp: Rate su L δ w) (b:ℝ) : ∀ᶠ t:ℝ in atTop, let f:=taxK L t ((H-V)/2)
    ∀ (σ:ℝ)(N:ℕ)(c:Side)(U I:Type)[Fintype I](F: Patron.Rail c (ample N I) U)(A:Set (Finset I))(p:I→ Site c)(q:I→Bool)(β:ℝ)(u:I→ℝ), Fires p ι → (∀ i∈A,Spaced p i (radiusB (run L t))) → Pill F β σ (radiusB (run L t)) (b+2*a) (taxK L t H) → (∀ i U,Well N p σ q (F.warp i U)) → (∀ i, |u i|≤ |w (run L t)|) → 0<σ → Film.Stock N (Film.publication N p q F A σ) (radiusB (run L t)) (taxK L t V) b σ f⁻¹ u:=by -- remove m unused
   let C:= ((H-V)/2:ℝ); have hC:0<C:= by unfold C; linarith
   let D t:=Film.allowance ι (radiusB t) a (|w t|); let e':=max δ 0; have he:Rate su L e' D:=by
      have hx:Rate su L δ fun t=> |w t|:=fun V h=> (hp V h).mono (fun i h=>  le_trans (abs_abs (w i)|>.le) h); let K t:=(radiusB t+radiusB t+1:ℝ); have hk:Rate su L 0 K:= (Rate.radius_price.add Rate.radius_price).add (Rate.const 1)
      have hf:Rate su L δ fun i=>|w i| *(K i)^4*ι/a:=by simpa only [div_eq_mul_inv,zero_mul,add_zero] using (((hx.mul (hk.pow 4)).mul_right (ι:ℝ)).mul_right a⁻¹)
      exact Rate.add (hf.weaken (le_max_left ..)) ((Rate.const 1).weaken (le_max_right ..))
   filter_upwards [(Work.E09.betaF_growth su L).eventually (upperTax L (C/2) (by linarith) D e' he), (Work.E09.betaF_growth su L).eventually (Cupola.exsteam L ha ι hp), Finch.dim L (1/3)] with i hi hW hzF
   intro x σ N c U I _ F A p q B u hx ht hf hV he hh
   let p' := taxK L i V; let q':= taxK L i H; have hp':0<p':= Real.exp_pos _; have hq':0<q':=Real.exp_pos _; have hx₀:0<x:=Real.exp_pos _
   have hhH: x*p'*x=q':=by unfold x p' q' taxK; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
   have hi2:D (run L i) ≤ x:=by
      have h0: C/2*fan L (1/3) (run L i) ≤ C*fan L (1/3) i:=by have h:=mul_le_mul_of_nonneg_left hzF hC.le; linarith only [h]
      exact hi.trans (Real.exp_monotone h0)
   refine Film.budgeting p a A q F σ hf hh hV u he (abs_nonneg _) (inv_pos.mpr hx₀).le hp' (Real.exp_monotone (mul_le_mul_of_nonneg_right h.le (fan_pos ..).le)) fun j=>?_ -- x binder? let f
   apply (div_le_iff₀ hq').mpr; calc
      _ ≤ x*p' := mul_le_mul_of_nonneg_right ((Film.totalFuel p a A (F.addr j) ι hx ht ha (abs_nonneg _) (hW c I p (F.addr j).place hx)).trans hi2) hp'.le
      _ = x⁻¹*q' := by rw [←hhH]; field_simp -- ring
end Surplus
end Film
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Film.Surplus.grantK
