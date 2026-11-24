import YM.MassiveQCD.Plate.Sight
import YM.QCD.Brick.Flurry
/-! # Recenter ANY list payload through-order; per seam leg cost. Location on torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Stew Kites
open scoped Topology BigOperators ContDiff Classical Matrix
variable {c:Side} {N:ℕ}
variable {O:BudgetPoint}{f:Grid c→ Fields c N}{i j:Site c}{d k m:ℕ}{Z:Support c}{v t q u w p r:ℝ}
-- copied core scaling: no wasted smoothness
private lemma translate {d : ℝ} (hh : (separation i j:ℝ) ≤ d) {A : Directions su c} (h : O.dirBound j A) :
    O.dirBound i ((((1+d)^O.power)⁻¹:ℝ) • A) := by
  have hd : 0 ≤ d := (Nat.cast_nonneg _).trans hh
  intro p; let t := (1+d)^O.power; have hp : 0 < t := by unfold t; positivity
  change ‖t⁻¹ • A p‖ ≤ _
  rw [norm_smul_of_nonneg (inv_pos.mpr hp).le,inv_mul_le_iff₀ hp]
  refine (h p).trans ?_
  rw [mul_left_comm, show t=(1+d)^O.power from rfl,←mul_pow]; have hb := O.threshold_pos; gcongr
  have he : (separation p.1 j:ℝ) ≤ separation p.1 i + (separation i j:ℝ) := by exact_mod_cast separation_triangle p.1 i j
  nlinarith [Nat.cast_nonneg (α:=ℝ) (separation p.1 i)]
private lemma left_turn {F:Type} [NormedAddCommGroup F][NormedSpace ℝ F] (u : Config su c → F) (v : List (Directions su c)) (a : ℝ) (U : Config su c) :
    leftDerivs u (v.map fun A => a • A) U = a^v.length • leftDerivs u v U := by
  induction v generalizing U with
  | nil => simp [leftDerivs]
  | cons x v ih =>
    simp only [List.map_cons,leftDerivs,ih, deriv_fun_const_smul_field]
    have hi (t : ℝ) : t • a • x = (a*t) • x := by rw [smul_smul, mul_comm]
    simp_rw [hi]
    let G (t : ℝ) := leftDerivs u v (increment U (t • x))
    change a^v.length • deriv (fun t => G (a*t)) 0 = _
    rw [deriv_comp_mul_left, mul_zero, smul_smul,List.length_cons,pow_succ]
open QCD.Brick
lemma wonder (X:Fields c N)(t a:ℝ)(k:ℕ)(i:Site c): view i k (a • X) t= ‖a‖*view i k X t:=by unfold view; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [show coef i (a • X)=a • coef i X from map_smul ((coef i).restrictScalars ℝ) .., norm_smul,mul_left_comm] -- coef CLM? 
noncomputable abbrev reFee (d k:ℕ)(O:BudgetPoint):ℝ:= (1+(d:ℝ))^(k+O.power*O.order)
lemma reticule (h: Sight Z i 2 O t f v)(ht:0 ≤ t) (he:separation i j ≤ d): Sight Z j 2 O t f (reFee d 2 O *v):=by
   let r:=1+(d:ℝ); have hr:1≤r:= le_add_of_nonneg_right (Nat.cast_nonneg _); let p:= r^O.power; have hp:1≤p:= one_le_pow₀ hr; have hx:=zero_lt_one.trans_le hp
   refine {h with pole:=fun U hu l hl hA=>?_, travels:=mul_nonneg (by unfold reFee; positivity) h.travels}; let q:=l.map (fun A=>p⁻¹ • A); have hf:q.length=l.length:= List.length_map ..; have hQ : q.map (fun A=>p • A)=l:= by simp [q,hx.ne', Function.comp_def]
   rw [← hQ,left_turn,wonder]; rw [Real.norm_of_nonneg (pow_nonneg hx.le _)]; let u:=view i 2 (leftDerivs f q U) t; let v':=view j 2 (leftDerivs f q U) t; have hZ: u ≤ v:= h.pole U hu q (hf.trans_le hl) fun i hi=> by obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi; exact translate (Nat.cast_le.mpr he) (hA _ hj)
   unfold reFee; rw [pow_add,pow_mul]; have hΩ: u≥0:= view_nn _ _ _ ht; have h₁:v' ≤ r^2 *u:= by
       have hξ:= trails j i (leftDerivs f q U) ht; rw [← viewSen _ _ _ ht,← viewSen _ _ _ ht] at hξ
       apply hξ.trans; unfold r; gcongr
   apply le_trans (b:= r^2*(p^O.order*v)) _ (by unfold r p; rw [mul_assoc])
   apply le_trans (mul_le_mul_of_nonneg_left h₁ (pow_nonneg hx.le _)); rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hp (hf.trans_le hl)) hZ hΩ (pow_nonneg hx.le _)) (sq_nonneg _)
open Push.Local
lemma wearsW (h:Sight Z i k O t f v) (ht:0 ≤ u)(hv:0< p) (hp:u*p≤ t) : Sight Z i k O p (engine u (Keys c N) ∘ f) v:=by
   let χ: Fields c N→L[ℝ] Fields c N:= ((engine u (Keys c N)).toLinearMap.toContinuousLinearMap).restrictScalars ℝ
   refine ⟨fun i j he=>congr_arg χ (h.room i j he),fun i=>hopeful N u _ _ (h.gate i),fun U hu=> χ.contDiff.contDiffAt.comp 0 (h.use U hu),?_,χ.continuous.measurable.comp h.borel,h.travels⟩
   intro U hu l hvA hP; change view i k (leftDerivs (χ ∘ f) l U) p ≤ v; rw [show leftDerivs _ l U= χ _ from left_linear χ l (h.use U hu) hvA]; change view _ _ (engine u _ _) _ ≤ _; rw [changeView _ _ _ hv.le ht]; exact (birthView _ _ _ (mul_nonneg ht hv.le) hp).trans (h.pole U hu l hvA hP)
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.reticule
