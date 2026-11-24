import YM.Oriole.Dunn
import YM.Oriole.Tree
/-! Close both tape measures at common budgets. produce unequivocal coefficients,
period independent bills for warm reporters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open Function Finset Filter UV Lattice Wilson QCD QCD.Grass Poised Poised.Stative Module Poised.Display Poised.Plans Poised.Plans.Stamp.Stair Lat
open scoped Matrix Matrix.Norms.L2Operator BigOperators ContDiff Topology Classical TensorProduct
variable (a b:Flavor 6)(g:Bool){n m:ℕ}{s δ v η B Z ε Γ:ℝ}
local notation "F"=> flame a b g 8 (by decide)
local notation "L"=> arbor a b g
local notation "Q" => Lat.wave (claw g 0)
variable (t:Bool)(x y z: Label 8)
local notation "p"=> one_jet t 0
local notation "q"=> one_jet (!t) 0
-- geometry8 relation on all charged lanes.
lemma z_P : geometry 8 (F).val =0:=by
      change geometry 8 (bilinear _ _ _ _ _) = 0; rw[← j_stard]; unfold fieldB; simp_rw [map_sum]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; let m:SpinMode 8:= ((0,i),a); let n:SpinMode 8:= ((0,j),b); let z:ℂ:=Lat.wave (pulp g) i j
      have hP:geometry 8 (jcoat (Matrix.single m n 1))=0:=by
           obtain ⟨h,hP⟩:=soldF m n; have he: spinWeight m.1.1+spinWeight n.1.1 ≠8:=by change spinWeight (0:Multi 8)+_≠_; change spinWeight (0:Multi 8)+spinWeight (0:Multi 8)≠_; rw[cost_root]; norm_num
           rcases hP with hP|hP
           · rw[←hP,geometry_basis,if_neg (h.symm ▸ he)]
           apply neg_injective; rw [neg_zero,← map_neg, ← hP,geometry_basis,if_neg (h.symm ▸ he)]
      change geometry 8 (jcoat (Matrix.single m n z))=_; rw [show Matrix.single m n z=z • Matrix.single m n (1:ℂ) from by ext i j; rw [Matrix.single_apply, Matrix.smul_apply,Matrix.single_apply]; split <;> simp,map_smul,map_smul,hP,smul_zero]
abbrev Style (p' q' r:ℂ):Label 8:=p' • flame a b g 8 (by decide)+q' • L true+r • L false
local notation "S0"=> Style a b g
noncomputable def tariff (a b:Flavor 6)(t:Bool):ℝ:= ∑ i:Rings 8,‖qp a b (one_jet t 0) (one_jet (!t) 0) (juncoat (UV.gen i.val))‖
local notation "τ"=> tariff a b
-- note private tribunes from Dunn. mirror.
lemma budgetC (t:ℂ) (i:ℕ): laps i (t • x)=‖t‖ * laps i x :=by
     unfold laps; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p' _=>?_ ; split; next h=> change ‖Poised.Stative.coord _ (t • x.val)‖=_; rw [map_smul,norm_smul]
     next _=>rw [mul_zero]
lemma moneyA (α β γ:ℂ) : laps 6 (Style a b g α β γ)=‖α‖ * laps 6 F:=podium ..
lemma inv8 (x:ℕ)(hp : geometry 8 z.val=0): laps 8 z=0:=by
    refine sum_eq_zero fun i _=>?_ ; split; next h=> have hx:=geo_basis i.val z.val 8; rw[if_pos h,hp,map_zero] at hx; rw [←hx,norm_zero]
    next _=> rfl
lemma moneyB (α β γ:ℂ): laps 8 (Style a b g α β γ)≤ laps 8 (L true)*‖β‖+ laps 8 (L false)*‖γ‖:=by
     apply (lap_plus ..).trans; apply le_trans (add_le_add_left (lap_plus ..) _); rw [budgetC,budgetC,budgetC]; rw [inv8 (F) 0 (z_P ..)]; simp [mul_comm]
lemma tariffs : 0≤ tariff a b t:=sum_nonneg fun _ _=>norm_nonneg _
set_option maxHeartbeats 460000 in
lemma mission (α β γ:ℂ) : ‖(if t then β else γ)‖ ≤ tariff a b t * laps 8 (Style a b g α β γ) :=by
     let T':=qp a b p q; let V:= Style a b g α β γ; have ht:T' (juncoat (geometry 8 V.val)) = (if t then β else γ) • Q:=by
           suffices h:T' (juncoat (geometry 8 V.val))=T' (juncoat V.val) from h.trans (Casing ..)
           change T' (juncoat (geometry 8 (α • (F).val+ β • (L true).val+γ • (L false).val))) = T' (juncoat (α • (F).val+ β • (L true).val+γ • (L false).val)); simp_rw [map_add,map_smul,outside, z_P, map_zero,smul_zero,zero_add]; rw [show T' (juncoat (F).val)=0 from ?_,smul_zero,zero_add]; change T' (juncoat (bilinear _ _ _ _ _))= _; rw[← j_stard,j_coat]; ext i j; cases t <;> simp [T',qp,Oriole.prism,fieldK,one_jet,highV]
     have hk:‖Q‖=1:= primeU Q (W_unit _ (claw_unit ..)); have hQ: ‖T' (juncoat (geometry 8 V.val))‖= ‖(if t then β else γ)‖:=by rw[ht,norm_smul,hk,mul_one]
     rw [←hQ]; conv_lhs=> rw[← quiet V.val ((label_law _).mp V.prop|>.1)]
     change ‖T' (juncoat (geometry 8 (∑ i:Rings 8,Poised.Stative.coord i V.val • UV.gen i.val)))‖≤ _; simp_rw [map_sum,map_smul,geometry_basis]; refine (norm_sum_le ..).trans ?_; unfold laps; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; split; next h=> rw[norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_right (single_le_sum (s:=univ) (f:=fun i:Rings 8=>‖T' (juncoat (UV.gen i.val))‖) (fun _ _=>norm_nonneg _) (mem_univ i)) (norm_nonneg _)
     next _=> rw [map_zero,map_zero,smul_zero,norm_zero,mul_zero]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.mission
#print axioms YM.Massive.Oriole.moneyB
