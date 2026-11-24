import YM.Massive.Filament.Algebra
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Fused Cauchy bound at simultaneous label prices.

Per-flag budgets do not give, a priori, an absolutely summable bound uniform
in disk parameters. Make no estimate of the global sup from a single Hit
choice; instead one scalar holomorphic combination tests *all costs in a station's finite payroll*.
No integration over smooth views; will apply under cash whose flags are measurable not continuous.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Filament
open Function Filter Complex Metric Finset
open scoped BigOperators Topology ContDiff Classical
variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {P:ι→ℂ→ℂ→E}{a:ι→ℝ}{S:Finset ι}{C R:ℝ}{z s:ℂ}
open Fused
lemma emerald [CompleteSpace E] (hp:∀ i,Fused (P i)) (ha:0≤a)
 (hb:∀ (z s:ℂ), ‖z‖<1→‖s‖<1→∑ i∈S,a i*‖P i z s‖≤ C)(hr:0<R)(hz:R < 1)(hs:Safe s)(n:ℕ)(hn:n≠0): ∑ i∈ S,a i*‖bead n (fun z=> P i z s)‖ ≤ luster C (peso n) s/R^n:=by
   let x i:= bead n (fun z=> P i z s); choose A hA he using (fun i=> exists_dual_vector'' ℂ (x i))
   let B (i:ι): E →L[ℂ] ℂ:= (a i : ℂ) • A i; let Q i z t:= B i (P i z t); let H z t:= ∑ i∈ S,Q i z t
   have hP i : Fused (Q i):= (hp i).compose (B i) (B i).contDiff
   have hH : Fused H:= Fused.sigma Q S fun i _=> hP i
   have hv (z t:ℂ)(he:‖z‖<1)(hx:‖t‖<1): ‖H z t‖≤ C:=by
       refine (norm_sum_le S _).trans ((sum_le_sum (fun i _=>?_)).trans (hb z t he hx))
       change ‖(a i:ℂ) • A i (P i z t)‖≤_; rw [norm_smul,norm_real,Real.norm_of_nonneg (ha i)]; refine mul_le_mul_of_nonneg_left ((A i).le_opNorm _|>.trans (mul_le_of_le_one_left (norm_nonneg _) (hA i))) (ha i)
   refine le_trans (b:=‖bead n (fun z=> H z s)‖) ?_ (hH.benefits _ hv hs hr hz hn)
   have hj i: bead n (fun z=>Q i z s)=↑(a i*‖x i‖):=by
      change bead n (B i ∘ fun z=> P i z s)=_
      rw [handset n (B i) (p:=fun z=>P i z s) ((hp i).wire _ (withinL hs)) zero_lt_one]; change (a i:ℂ)*A i (x i)=_
      rw [he]; push_cast; rfl
   have hw: bead n (fun z=>H z s)= ↑(∑ i∈ S,a i*‖x i‖):=by
      refine (bead_fin n (B:=S) (f:=fun i z=> Q i z s) (fun i _=> (hP i).wire _ (withinL hs)) zero_lt_one).trans ?_; rw [ofReal_sum]; exact sum_congr rfl fun i hi=> hj i
   rw [hw,norm_real, Real.norm_of_nonneg (sum_nonneg fun i _=>mul_nonneg (ha i) (norm_nonneg _))]
-- Simpler practical variant for payrolls: no need cbounds!
lemma almost_sup {u:F→ℝ}(y:F)(h:∀ x,0 ≤ u x)(ht:BddAbove (Set.range u)) : ∃ z,∀ x, u x ≤ 2*u z:=by
   letI:Nonempty F:=⟨y⟩; let v:= ⨆ x,u x; by_cases hh:v ≤0
   · exact ⟨y,fun x=> ((le_ciSup ht x).trans hh).trans (mul_nonneg (by norm_num) (h _))⟩
   obtain ⟨i,hi⟩:= exists_lt_of_lt_ciSup (α:=ℝ) (show v/2 < v from (by linarith only [lt_of_not_ge hh]))
   exact ⟨i,fun j=> (le_ciSup ht j).trans (by linarith only [hi])⟩
end YM.Massive.Filament
#print axioms YM.Massive.Filament.emerald
