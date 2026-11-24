import YM.QCD.Ruby.Full
/-! # whole-polynomial stalk seminorm with weighted diameter. alpha point supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ} {t:ℝ} {o: Site c}
variable {D K V E:Type*} [Fintype D][Fintype K]
-- CLM over ℂ detached at Site. judge same norm at final scaling. weight on footprint, not lag mask.
def pieD (g:D→ℕ)(s:Finset D):ℕ:= (1+s.sup g)^2
def starch (g:D→ℕ)(t:ℝ)(s: Finset D): ℝ := pieD g s* t ^s.card
def bias (g:D→ℕ)(t:ℝ):Alg D→L[ℂ]Alg D:=LinearMap.toContinuousLinearMap { toFun:=fun x=> ∑ s : Finset D,(↑(starch g t s):ℂ) • ((Grass.coef s x) • Grass.mono s), map_add':=fun x y=>by simp_rw [map_add,add_smul,smul_add,sum_add_distrib],map_smul':=fun k x=>by simp_rw [map_smul (coef _),smul_sum]; refine sum_congr rfl fun i _=>?_ ; change _ • ((k*Grass.coef i x) •_)=_; rw [mul_smul,smul_comm]; rfl }
def visc (g:D→ℕ)(t:ℝ) (x:Alg D):ℝ:= ‖bias g t x‖
variable (g:D→ℕ)
lemma tile (t:ℝ)(s:Finset D)(x:Alg D): coef s (bias g t x)=(↑(starch g t s):ℂ)*coef s x:=by
   change coef s (∑ i:Finset D, (↑(starch g t i):ℂ) • (Grass.coef i x • Grass.mono i))= _; rw [map_sum,sum_eq_single s]
   · rw [map_smul,map_smul, Grass.read,smul_eq_mul,smul_eq_mul,mul_one] -- order
   · intro i _ hi; rw [map_smul,map_smul,read_other _ _ hi.symm, smul_zero,smul_zero]
   simp
lemma pricesD (h:0≤t) (x: Alg D): visc g t x=∑ s :Finset D, starch g t s * ‖coef s x‖:=by
   unfold visc; rw [Grass.norm_def]; exact sum_congr rfl fun i _=> by rw [tile, norm_mul, Complex.norm_real,Real.norm_of_nonneg (by unfold starch; positivity)]
lemma starch_pos (h:0≤t)(v:Finset D):0 ≤ starch g t v:=by unfold starch; positivity
lemma starch_mono {u :ℝ}(h:0 ≤ t)(hp: t ≤u)(b:Finset D): starch g t b ≤ starch g u b:= by unfold starch; gcongr -- inspect
lemma future {u:ℝ}(h:0 ≤ t)(hp:t ≤ u)(x:Alg D): visc g t x ≤ visc g u x:=by rw [pricesD g h,pricesD g (h.trans hp)]; exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (starch_mono g h hp i) (norm_nonneg _)
lemma sturdy (i:Finset D)(ht:0≤t): visc g t (mono i)=starch g t i:=by
   rw [pricesD g ht,sum_eq_single i]
   · rw [Grass.read,norm_one,mul_one]
   · intro j _ he; rw [read_other _ _ he,norm_zero,mul_zero]
   simp
lemma shot (x:Alg D)(t:ℝ)(h:0<t): load (fun _=>t) x≤ visc g t x:=by
   rw [Creek.dry _ (fun _=>h),pricesD g h.le]; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold starch; rw [Finset.prod_const]; exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr (one_le_pow₀ (by omega))) -- fix
lemma plots_mul (i j:Finset D) (ht:0 ≤ t): visc g t (mono i*mono j) ≤ starch g t i*starch g t j:=by
  by_cases hi:Disjoint i j; swap; · rw [Grass.mono_mul_zero _ _ hi,visc,map_zero,norm_zero]; exact mul_nonneg (starch_pos g ht _) (starch_pos g ht _)
  let s:=i.disjUnion j hi; have hp : visc g t (mono i*mono j)=starch g t s:=by
     rcases Grass.mono_mul_sign i j hi with h|h
     · rw [h]; exact sturdy g s ht
     rw [h,visc,map_neg,norm_neg]; exact sturdy g s ht
  rw [hp]; unfold starch; rw [show s.card=i.card+j.card from Finset.card_disjUnion ..,pow_add]; rw [show (pieD g i:ℝ)* _*((pieD g j:ℝ)*_)=((pieD g i:ℝ)*(pieD g j:ℝ))*(t^i.card*t^j.card) from ?_]
  · apply mul_le_mul_of_nonneg_right _ (by positivity); rw [←Nat.cast_mul]; apply Nat.cast_le.mpr; unfold s pieD; rw [Finset.disjUnion_eq_union,sup_union, ← mul_pow]; apply Nat.pow_le_pow_left; change (1+max (i.sup g) (j.sup g))≤_; rcases le_total (i.sup g) (j.sup g) with h|h
    · rw [max_eq_right h]; exact Nat.le_mul_of_pos_left _ (by omega)
    rw [max_eq_left h]; exact Nat.le_mul_of_pos_right _ (by omega)
  ring
lemma vc_scale (x: Alg D)(a:ℂ): visc g t (a • x) = ‖a‖ * visc g t x:=by unfold visc; rw [map_smul,norm_smul]
lemma vc_sum (X:E →Alg D)(s:Finset E): visc g t (∑ i∈s,X i)≤∑ i∈s,visc g t (X i):=by unfold visc; rw [map_sum]; exact norm_sum_le ..
lemma roams (ht:0≤ t)(x y:Alg D): visc g t (x*y) ≤ visc g t x*visc g t y:=by
   conv_lhs=>rw [← write x,← write y, Finset.mul_sum]
   simp_rw [sum_mul]
   apply le_trans (vc_sum ..); rw [pricesD g ht x, pricesD g ht y, Finset.mul_sum]
   apply sum_le_sum; intro j hj; rw [Finset.sum_mul]; apply le_trans (vc_sum ..); refine sum_le_sum fun i hi=> ?_; rw [smul_mul_assoc, mul_smul_comm,vc_scale, vc_scale]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (plots_mul g i j ht) (norm_nonneg _)) (norm_nonneg _)); exact le_of_eq (by ring)
def lens (o : Site c) (i:Keys c N):ℕ:= separation (locationP i) o
abbrev plank (o:Site c)(r:ℝ):=visc (lens (N:=N) o) r
def Sen (o:Site c)(r:ℝ)(x:EvenA c N):ℝ:= plank o r x.val
def needle (o:Site c)(N:ℕ)(r:ℝ): EvenA c N→L[ℂ] Alg (Keys c N):=(bias (lens o) r).comp (LinearMap.toContinuousLinearMap (Cove.light _).toLinearMap)
lemma measures (t:ℝ)(x:EvenA c N): ‖needle o N t x‖=Sen o t x:=rfl
end YM.QCD.Stew
