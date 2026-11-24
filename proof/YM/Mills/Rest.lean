import YM.VMarker.Totes
import YM.Mills.Spoors
/-! # Recover reusable K reserves at value aperture without assuming *anything* about separations beyond occupancy per centre. -/
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
lemma rate_pay (H:ℕ)(hv:0≤b)(hx:Fires p H)(hp:b*(B+B+1:ℝ)^4*(H:ℝ) ≤ 2*a) :
  (∑ i∈ seats p S Y,b^i.card * Real.exp (-(2*a)*Z)) ≤ 1:=by
     let u:= Cupola.barn p Y.place; let Q i:= b^(i:Finset I).card; let r:=Real.exp (-(2*a)*Z); have h:0≤r:=(Real.exp_pos _).le
     have he: seats p S Y ⊆ powerset u:=by
        intro i hi; obtain ⟨_,_,hv⟩:=(mem_filter.mp hi).2; exact mem_powerset.mpr (fun j hj=> (inside ..).2 (hv (mem_image_of_mem _ hj)))
     have hz: (u.card:ℝ) ≤ Z*(B+B+1:ℝ)^4*H:= by exact_mod_cast (barncard p _ H B hx)
     have hF:b*u.card ≤ 2*a*Z:=by nlinarith only [mul_le_mul_of_nonneg_left hz hv,mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α:=ℝ) (Z))]
     rw [← sum_mul]; apply (mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg he (fun i _ _=> by positivity)) h).trans
     have hk:(∑ i∈ powerset u,b^i.card)=∏ j∈u,(b+1):=by
        have h:= Finset.prod_add (fun _=>b) (fun _=>1) u; simpa using h.symm
     rw [hk,prod_const]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ b+1) (Real.add_one_le_exp _) _) h).trans
     rw [←Real.exp_nat_mul, ← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith only [hF])
lemma ready_low (a d m n:ℝ)(ι:ℕ)(ha:0<a)(hb:n < m):∀ᶠ t:ℝ in atTop,∀ (σ:ℝ)(N:ℕ)(c:Side)(U I:Type)[Fintype I](F: Patron.Rail c (ample N I) U)(A:Set (Finset I))(p:I→ Site c)(q:I→Bool)(β:ℝ)(u:I→ℝ), Fires p ι → Pill F β σ (radiusB (run L t)) (d+2*a) (taxK L t m) → (∀ i U,Well N p σ q (F.warp i U)) → (∀ i, |u i| ≤ fan L (-1) (run L t)) → 0 <σ → Film.Stock N (Film.publication N p q F A σ) (radiusB (run L t)) (taxK L t n) d σ ((taxK L t (m-n))⁻¹) u:=by
   let H t:= (radiusB t+radiusB t+1:ℝ); have h: Jets.Touch.Seat L 0 H:= (Seat.radius.comb Seat.radius).comb (Seat.numbers 1); have ht: Jets.Touch.Seat L (-1) (fun t=> fan L (-1) t * (H t)^4*ι):= ((Seat.keeps.ponies (h.powered 4)|>.times _).above (by linarith))
   filter_upwards [(Work.E09.betaF_growth su L).eventually (ht.shrinks (by norm_num) (show 0 < 2*a by positivity))] with t ht σ N c U I _ F A p q β u hp hv he h hs
   let P μ:= taxK L t μ; let v:=fan L (-1) (run L t); have hX:0≤v:=(fan_pos ..).le; have hw: P n≤ P m:= Real.exp_monotone (mul_le_mul_of_nonneg_right hb.le (fan_pos ..).le)
   refine Film.budgeting p a A q F σ hv hs he u h hX (inv_pos.mpr (Real.exp_pos _)).le (Real.exp_pos _) hw fun i=>?_ -- ℝ.
   have hx : (P n/P m)= (P (m-n))⁻¹:=by unfold P taxK; rw [← Real.exp_sub, ← Real.exp_neg]; apply congr_arg; ring
   apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (rate_pay p a A (F.addr i) ι hX hp ((le_abs_self _).trans ht)) (Real.exp_pos _).le) (Real.exp_pos _).le)
   rw [one_mul]; exact le_of_eq hx
end Surplus
end Film
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Film.Surplus.ready_low
