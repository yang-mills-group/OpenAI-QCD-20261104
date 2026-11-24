import YM.Play.Dukes
import YM.QCD.Cove.Quid
/-! An auxiliary capped charge on step amplitudes. Counts only indicated physical spin letters (not the observer copies), with a ceiling.
 Keeps same finite exterior space & direction readouts. No assumptions on spin-sector sign. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open Grass Cove Creek NormedSpace Finset Function Filter Anomaly
open scoped Topology BigOperators ContDiff Matrix Classical
variable {A B T:Type*}[Fintype A][Fintype B]
variable (C:Finset A)(b:ℝ)(n:ℕ)
noncomputable def premium (i:Finset A):ℝ:= b^ (min n (i∩C).card)
noncomputable def surge:Alg A →ₗ[ℂ] Alg A:= ∑ i:Finset A,(coef i).smulRight ((premium C b n i:ℂ) • mono i)
lemma boom (x:Alg A) : surge C b n x= ∑ i:Finset A, coef i x • ((premium C b n i:ℂ) • mono i):=by simp only [surge, LinearMap.sum_apply,LinearMap.smulRight_apply]
lemma boomM (i:Finset A): surge C b n (mono i)=(premium C b n i:ℂ) • mono i:=by rw [boom,sum_eq_single i,Grass.read,one_smul]; intro j _ hj; rw [read_other _ _ hj,zero_smul]; simp
lemma premNN {i:Finset A}(h:1≤b):0 ≤ premium C b n i := pow_nonneg (zero_le_one.trans h) _
lemma prem_le (h:1 ≤ b) (i:Finset A): premium C b n i ≤ b^n:=pow_le_pow_right₀ h (min_le_left ..)
lemma prem_prod (h:1 ≤ b) (i j:Finset A): premium C b n (i∪j) ≤ premium C b n i*premium C b n j:=by
   unfold premium; rw [← pow_add]; apply pow_le_pow_right₀ h; have hx := card_union_le (i∩ C) (j∩C); rw [union_inter_distrib_right]; omega -- name
variable (f:A→ℝ)
noncomputable def repay (x:Alg A):ℝ:= Creek.load f (surge C b n x)
lemma repay_pos {x:Alg A} : 0 ≤ repay C b n f x:= load_nn ..
lemma repayM (h:1 ≤ b)(i:Finset A): repay C b n f (mono i)= premium C b n i *load f (mono i):=by unfold repay; rw [boomM,load_scale,Complex.norm_real,Real.norm_of_nonneg (premNN C b n h)]
lemma repayL (c:ℂ)(x:Alg A): repay C b n f (c • x)= ‖c‖*repay C b n f x:=by unfold repay; rw [map_smul,load_scale]
lemma repayR (c:ℝ)(x:Alg A): repay C b n f (c • x)= ‖c‖*repay C b n f x:=by rw [← Complex.coe_smul,repayL,Complex.norm_real] -- theorem?
lemma repay_nil : repay C b n f 0=0:=by unfold repay; rw [map_zero,QCD.Cove.load_zero] -- inside YM.QCD
lemma repay_one: repay C b n f 1=1:=by rw [repay,show (1:Alg A)=mono ∅ from mono_empty.symm,boomM]; simp only [premium,empty_inter,card_empty,Nat.zero_min, Nat.min_zero,pow_zero,Complex.ofReal_one,one_smul,mono_empty, Cove.load_one]
lemma repayN (x:Alg A): repay C b n f (-x)= repay C b n f x:=by simp only [repay,load,map_neg,wscale,norm_neg] -- edit
lemma repay_sum (s:Finset T)(p:T→Alg A): repay C b n f (∑ i∈s,p i)≤∑ i∈s, repay C b n f (p i):=by unfold repay; rw [map_sum]; exact load_sum ..
lemma ticket_mono (i:Finset A)(h:∀j,0<f j): load f (mono i)=∏ j∈i,f j:=by
   rw [dry f h,sum_eq_single i, Grass.read,norm_one,mul_one]; intro j _ hj; rw [read_other _ _ hj,norm_zero,mul_zero]; simp
variable (hb:1 ≤ b)(hp:∀ i, 0<f i)
include hb hp
lemma sheet (x:Alg A): repay C b n f x=∑ i:Finset A,premium C b n i*‖coef i x‖* load f (mono i):=by
   unfold repay; rw [dry f hp]; apply sum_congr rfl; intro i _; rw [ticket_mono f i hp,boom,map_sum,sum_eq_single i,map_smul,map_smul,Grass.read,smul_eq_mul,smul_eq_mul,mul_one,norm_mul,Complex.norm_real,Real.norm_of_nonneg (premNN C b n hb)]; ring; intro j _ hj; rw [map_smul,map_smul,read_other _ _ (Ne.symm hj),smul_zero,smul_zero]; simp
lemma sheetB (x:Alg A): repay C b n f x=∑ i:Finset A,‖coef i x‖*repay C b n f (mono i):=by rw [sheet _ _ _ _ hb hp]; apply sum_congr rfl; intro i _; rw [repayM _ _ _ _ hb]; ring
lemma stamp (x:Alg A): repay C b n f x ≤ b^n*load f x:=by
   rw [sheet _ _ _ _ hb hp,dry f hp x,mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [←ticket_mono f _ hp]; nth_rw 2 [mul_comm _ ‖coef i x‖]; rw [←mul_assoc]; exact mul_le_mul (mul_le_mul_of_nonneg_right (prem_le C b n hb _) (norm_nonneg _)) le_rfl (load_nn ..) (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (norm_nonneg _))
lemma minor (x:Alg A): load f x≤repay C b n f x:=by
   rw [sheet _ _ _ _ hb hp,dry f hp x]; refine sum_le_sum fun i _=>?_; rw [←ticket_mono f _ hp,mul_comm]; apply mul_le_mul_of_nonneg_right _ (load_nn ..); exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hb)
lemma salute (i j:Finset A): repay C b n f (mono i*mono j)≤ repay C b n f (mono i)*repay C b n f (mono j):=by
   by_cases hv : Disjoint i j; swap
   · rw [mono_mul_zero _ _ hv,repay_nil]; exact mul_nonneg (repay_pos ..) (repay_pos ..)
   have hl: repay C b n f (mono (i∪j))≤ _:=calc
     repay C b n f (mono (i∪j))= premium C b n (i∪j)*(load f (mono i)*load f (mono j)):=by rw [repayM _ _ _ _ hb]; simp_rw [ticket_mono f _ hp]; rw [prod_union hv]
     _ ≤ premium C b n i*premium C b n j* (load f (mono i)*load f (mono j)):=mul_le_mul_of_nonneg_right (prem_prod C b n hb i j) (mul_nonneg (load_nn ..) (load_nn ..))
     _ = repay C b n f (mono i)*repay C b n f (mono j):=by simp_rw [repayM _ _ _ _ hb]; ring
   have hV:= mono_mul_sign _ _ hv; rw [disjUnion_eq_union] at hV; rcases hV with h|h; · rwa [h]
   rwa [h, repayN]
lemma repay_prod (x y:Alg A): repay C b n f (x*y)≤ repay C b n f x * repay C b n f y:=by
    let m (s: Finset A)(x:Alg A):= coef s x • mono s
    let Q:= repay C b n f
    calc
     Q (x*y)=Q (∑ s:Finset A,∑ t:Finset A, m s x*m t y):=by
            unfold m
            conv_lhs => rw [← write x,← write y]
            simp_rw [sum_mul,mul_sum] -- loop etc edit
     _ ≤ ∑ s:Finset A, ∑ t:Finset A,Q (m s x*m t y):= (repay_sum ..).trans (sum_le_sum fun i _=> repay_sum ..)
     _ ≤ ∑ s:Finset A,∑ t:Finset A,Q (m s x)*Q (m t y):=sum_le_sum fun i _=>sum_le_sum fun j _=>by
           dsimp only [m,Q]; rw [smul_mul_assoc,mul_smul_comm]; simp only [repayL]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (salute C b n f hb hp i j) (norm_nonneg _)) (norm_nonneg _)).trans_eq ?_; ring
     _ = Q x*Q y:=by
         simp_rw [← mul_sum,←sum_mul]; congr 1 <;> (simp_rw [m,Q,repayL]; exact Eq.symm (sheetB _ _ _ _ hb hp ..))
lemma funded (s:Finset T)(p:T→Patio A)(q:T→ℝ)(hv:∀ i∈s, repay C b n f (light _ (p i)) ≤ q i): repay C b n f (light _ (∏ i∈s,p i)) ≤ ∏ i∈s,q i:=by
   induction s using Finset.induction_on with
   | empty=> rw [prod_empty,prod_empty,map_one,repay_one]
   | insert i s hi ih=> rw [prod_insert hi,prod_insert hi,map_mul]; have he:=hv i (mem_insert_self ..); exact (repay_prod C b n f hb hp ..).trans (mul_le_mul he (ih fun j hj=> hv j (mem_insert_of_mem hj)) (repay_pos ..) ((repay_pos ..).trans he))
omit hp hb
@[fun_prop] lemma repContinu : Continuous (repay C b n f):= (Creek.payload f).comp ((surge C b n).continuous_of_finiteDimensional)
include hp hb
lemma spicy (x:Patio A)(z:ℝ)(h:repay C b n f (light _ x) ≤ z): repay C b n f (light _ (NormedSpace.exp x-1)) ≤ Real.exp z-1:=by
  rw [map_sub,map_one,light_exp]; let X:= light A x; let T (n:ℕ): Alg A:= (n.factorial:ℂ)⁻¹ • X^n; let Z (n:ℕ):=(n.factorial:ℝ)⁻¹*z^n
  have hz:0≤z:=(repay_pos ..).trans h; have ht : HasSum T (NormedSpace.exp X):=exp_series_hasSum_exp' X
  have hp' : HasSum Z (Real.exp z):=by rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (𝕂:=ℝ) z
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show T 0=1 by simp [T]] at ht
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show Z 0=1 by simp [Z]] at hp'
  have he i : repay C b n f (T i)≤Z i := by
    have hv j:repay C b n f (X^j)≤z^j:=by induction j with
      | zero=> simp [repay_one]
      | succ j ih=> rw [pow_succ,pow_succ]; exact (repay_prod C b n f hb hp ..).trans (mul_le_mul ih h (repay_pos ..) (pow_nonneg hz _))
    dsimp only [T,Z]; rw [repayL]; simpa using mul_le_mul_of_nonneg_left (hv i) (by positivity : 0 ≤ (i.factorial:ℝ)⁻¹)
  exact le_of_tendsto_of_tendsto' ((repContinu C b n f).continuousAt.tendsto.comp ht) (hp') (fun s:Finset ℕ=> (repay_sum C b n f s (fun i=> T (i+1))).trans (sum_le_sum fun k _=>he _))
end YM.QCD.Mural
#print axioms YM.QCD.Mural.spicy
