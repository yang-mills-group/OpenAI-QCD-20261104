import YM.QCD.Lunar.Stout
/-! # Fermi canonical global Moment. native. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
namespace Project
open Revolve Flume Quarry
variable (c)
open Entr Port AnalyticBridge.VerifiedReset
variable {o x:Site c}{t u δ β ε K A B v':ℝ}{p:BudgetPoint} {I:Type}
lemma ex (i:Bool)(x y:Site c): ‖stone c i x y‖≤ (c.val:ℝ):=by
    unfold stone; rw [norm_mul,Finch.shineH,one_mul]; split
    · rw [Complex.norm_intCast]; obtain ⟨hl,hr⟩:= lift_centers (y-x) 0
      have h : |Entr.crest (y-x)| ≤ (c.val:ℤ) :=by unfold crest; rw [abs_le]; omega
      exact_mod_cast h
    rw [norm_one]; exact_mod_cast c.pos
lemma hour (i:Finset (Keys c N))(ht:i.card=2)(h:0 ≤t)(v:EvenA c N)(o:Site c): t^2*‖coef i v.val‖≤ Sen o t v:=by
    unfold Sen plank; rw [pricesD _ h]; refine le_trans ?_ (Finset.single_le_sum (f:=fun j=>starch (lens o) t j *‖coef j v.val‖) (a:=i) (fun i _=> mul_nonneg (starch_pos _ h _) (norm_nonneg _)) (mem_univ _));
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold starch; rw [ht]; exact le_mul_of_one_le_left (sq_nonneg _) (show 1 ≤ (pieD _ _:ℝ) from (Nat.one_le_cast.mpr (one_le_pow₀ (Nat.le_add_right ..)))) -- arg
lemma cash (j:Bool)(i: Flavor N)(s u:Pinor)(A:EvenA c N)(p':Site c)(h:0 < t)(hv:Sen p' t A ≤ v'): ‖μDir c j (meter i A) s u‖≤ (c.val:ℝ)^9*(v'/t^2):=by
    let H (x:Site c):Modes c N:=((x,(s,0)),i); let d(x:Site c):Modes c N:=((x,(u,0)),i); let W (x:Site c) y:=stone c j x y* (gold (cell (meter i A) x y) s u)
    have he :(μDir c j (meter i A)) s u= ∑ x, ∑ y,W x y:=by change ((∑ x,∑ y, _): Spike) _ _=_; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]; rfl
    have hF(x y):t^2*‖gold (cell (meter i A) x y) s u‖≤ v':=by
         change t^2*‖bit (H x) (d y)*coef (tag (H x) (d y)) A.val‖≤_; rw [norm_mul]; have hx: ‖bit (H x) (d y)‖=1:=by obtain h|h :=bitS (H x) (d y)<;> simp [h]
         rw [hx,one_mul]; exact (hour c _ (by simp [tag]) h.le A p').trans hv
    have hQ(i k):‖W i k‖≤ (c.val:ℝ) * (v'/t^2):=by unfold W; rw [norm_mul]; exact mul_le_mul (ex c j i k) ((le_div_iff₀ (sq_pos_of_pos h)).mpr ((mul_comm _ _).le.trans (hF i k))) (norm_nonneg _) (by positivity)
    rw [he]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>hQ i j)).trans_eq ?_);
    simp only [sum_const,nsmul_eq_mul, card_univ, site_card,Nat.cast_pow]; ring
-- Flag ledger ∑ differs via cap.Natural CLM picture
variable {E:Gem c N I}
noncomputable def bb (j: Bool): Spike→L[ℝ]ℝ:= if j then sparkL else LinearMap.toContinuousLinearMap { toFun:= fun v=>(v (0,0) (0,0)).re,map_add':=fun v z=>by rfl,map_smul':=fun z v=>by change _= z*_ ; simp [Complex.smul_re, smul_eq_mul] }
noncomputable def valueB (j:Bool): (SampleX→Spike)→L[ℝ]ℝ:= if j then bandW else bandQ
noncomputable def labelB (j:Bool)(c:Side): Sheet c→L[ℝ]ℝ :=(bb j).comp ((μDir c j).restrictScalars ℝ)
noncomputable def unitF (j:Bool)(c:Side): Sheet c →L[ℝ]ℝ:= (Fintype.card (Site c):ℝ)⁻¹ • labelB j c
lemma chargeB (j:Bool)(R:SampleX→Spike): valueB j R= bb j (localW j R):=by cases j; rfl; rfl
lemma μlink (b:Flavor N)(j:Bool)(V₀:E.Gather)(i:I)(he: Nonwrapping (E.addr i).support (E.addr i).site): labelB j c (meter b (E.view i 1))= valueB j (lane E b i):=by
    let p:= (E.addr i).site; have hh:lane E b i=shape p (feeF b (E.view i 1)):= funext fun j=>if_pos he
    rw [hh,chargeB]; exact congr_arg (bb j) (uplift c _ _ _ (V₀.role ..) _ he)
omit c
end Project
end YM.QCD.Stew
