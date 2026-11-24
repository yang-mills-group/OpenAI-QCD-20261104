import YM.MassiveQCD.Mayer.Products
/-! # Ordered derivatives budget outward
 `Sen` is the actual weighted Bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c} {t p q a s r:ℝ} {k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
-- stop-price products only for fixed height with Lie masks. ";1" carries cost
variable {V:BudgetPoint}{f g:Grid c → EvenA c N}
lemma valueSeat (ht:0<t)(hh:Woven o B V t f a)(hv:Woven o B V t g p): Woven o B V t (f*g) (2^V.order*(a*p)):=by
    refine ⟨fun U W h=>congr_arg₂ (·*·) (hh.room U W h) (hv.room U W h), fun U=>?_,fun U hx=>(hh.use U hx).mul (hv.use U hx),fun U hx l hl hh'=>?_,Measurable.mul hh.Borel hv.Borel,mul_nonneg (by positivity) (mul_nonneg hh.travel hv.travel)⟩
    · unfold Gated; rw [Pi.mul_apply,map_mul]; exact Subalgebra.mul_mem _ (hh.gated _) (hv.gated _)
    apply (left_mul_tax ht.le (hh.use U hx) (hv.use U hx) (hh.pole _ hx) (hv.pole _ hx) l hl hh').trans; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (mul_nonneg hh.travel hv.travel)
-- height input enough real.Measure caller.Spin
lemma complexTone (h:Woven o B V t f p)(z:ℂ) : Woven o B V t (z • f) (‖z‖ * p):=by
    let M := (z • (ContinuousLinearMap.id ℂ Z)).restrictScalars ℝ
    refine ⟨fun i j hi=> congr_arg (z • ·) (h.room i j hi), fun i=>?_ , fun i hi=> M.contDiff.contDiffAt.comp 0 (h.use i hi),?_, measurable_const.smul h.Borel,mul_nonneg (norm_nonneg _) h.travel⟩
    · unfold Gated; rw [Pi.smul_apply,map_smul]; exact Subalgebra.smul_mem _ (h.gated _) _
    intro i hi l hl he; change Q (leftDerivs (M ∘ f) _ i)≤_; rw [Push.Local.left_linear M l (h.use i hi) hl]; change visc (lens o) t (z • (leftDerivs f _ i).val)≤_; exact (vc_scale ..).trans_le (mul_le_mul_of_nonneg_left (h.pole _ hi l hl he) (norm_nonneg _))
lemma payPower (ht:0<t)(J:ℕ)(h:Woven o B V t f p): Woven o B V t (f^(J+1)) ((2^V.order*p)^J*p):=by
    induction J with
    | zero=> rw [Nat.zero_add,pow_zero,pow_one,one_mul]; exact h
    | succ j ih=> rw [pow_succ f]; apply (valueSeat ht ih h).stretches (Subset.refl _) (le_of_eq ?_); rw [pow_succ _ j]; ring
end YM.QCD.Stew.Phased

#print axioms YM.QCD.Stew.Phased.valueSeat
#print axioms YM.QCD.Stew.Phased.payPower
#print axioms YM.QCD.Stew.Phased.complexTone
