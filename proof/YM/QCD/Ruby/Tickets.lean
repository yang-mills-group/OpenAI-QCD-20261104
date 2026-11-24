import YM.QCD.Ruby.Barge
/-! # arithmetic all logs even families. Keep per-notice R budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A R m k σ B' v' ht q':ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
variable (hP : 0 ≤ p)(hQ : 0 ≤ q)
def fair (p:ι→ℝ)(q:β→ℝ)(i:Plot Y X):ℝ:= ∏ j∈ i.val,Sum.elim q (wig p) j
include hP hQ
lemma fairness (i:Plot Y X):0 ≤ fair Y X p q i:= prod_nonneg fun j _=> by rcases j with j|j; exact hQ j; exact wig_nn hP j
lemma found (he:1≤R)(s:Plot Y X): R ^ (oriD (Trail Y X t) s).card*fair Y X p q s ≤ ∏ i∈trip s, money Y X p (taxed (oriD X) q R) i :=by
    let d : Stamp ι β→ ℝ:=Sum.elim (taxed (oriD X) q R) (wig p); have hh (i:Car Y X): money Y X p (taxed (oriD X) q R) i= ∏ j∈i.sleeper,d j:=by unfold money Car.sleeper; rw [prod_disjSum,prod_singleton]; rfl
    let U:=s.1.toLeft; let V:=s.1.toRight; have hz:s.val=U.disjSum V:=by ext i; cases i <;> simp [U,V]
    simp_rw [hh]; rw [← prod_biUnion (f:=d) (isolation s),tracked]; change R ^ (badgeK X s.val).card*fair Y X p q s≤ _; unfold fair badgeK
    rw [hz]; simp only [prod_disjSum,toLeft_disjSum,Sum.elim_inl, Sum.elim_inr,d,taxed,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,mul_assoc]; simp_rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _ =>wig_nn hP _); apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=> hQ i); exact pow_le_pow_right₀ he card_biUnion_le
lemma cashin (i:Plot Y X)(he:1≤R)(x:Site c) (hx:x∈ home (Trail Y X t) i)(hu:0≤a) :
   let m:=money Y X p (taxed (oriD X) q R)
   taxed (oriD (Trail Y X t)) (fair Y X p q) R i*currency B a (home (Trail Y X t) i) ≤ touches (Car.vat (Y:=Y) (X:=X)) B m a x (trip i):=by
    intro m; have hp: Ac.Spark Car.vat (trip i):= regiment i
    have hv : home (Trail Y X t) i= (trip i).biUnion Car.vat:=by
       change i.val.biUnion _=(trip i).biUnion Car.vat; nth_rw 1 [← tracked i]; ext j; simp only [mem_biUnion, Car.vat,scopeK]; grind
    rw [hv,touches, if_pos ⟨hp,hv ▸ hx⟩,prod_mul_distrib]; apply mul_le_mul (found Y X hP hQ he i) _ (Real.exp_pos _).le (prod_nonneg fun _ _=> mul_nonneg (mul_nonneg (by have h_R:=zero_lt_one.trans_le he; positivity) (hQ _)) (prod_nonneg fun _ _=> wig_nn hP _))
    unfold currency; rw [← Real.exp_sum, ← mul_sum, ← Nat.cast_sum]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Ac.cover _ _ hp)) hu)
lemma priceV (he:1≤R)(hC:Ready (Car.vat (Y:=Y) (X:=X)) B (money Y X p (taxed (oriD X) q R)) a m k σ)(hp:0≤a) : Ac.Hit (home (Trail Y X t)) B (taxed (oriD (Trail Y X t)) (fair Y X p q) R) a (m*(1-σ)⁻¹):=by
    intro x
    let u(i:Plot Y X):=trip i
    have hu:Injective u:= fun i j h=>Subtype.ext (by rw [← tracked i,← tracked j,show trip i=trip j from h])
    have hx := budget_pull u hu (touch_tail (Car.vat (Y:=Y) (X:=X)) B hC x 0)
    simp only [Nat.zero_le,pow_zero, mul_one,if_true] at hx
    refine budget_mono hx (fun i=>?_) fun i=> ?_
    · unfold taxed; split; exact mul_nonneg (mul_nonneg (by have hv:=zero_lt_one.trans_le he; positivity) (fairness Y X hP hQ _)) (Real.exp_pos _).le; exact le_rfl
    split; next h=> exact cashin Y X hP hQ i he x h hp
    next _=> exact hx.1 _
-- input specifies integer flag uplift with Soft log payments. finite dim powers & norms. 
variable (h: ∀ i V, ‖token c N w (Y.mean i V)‖ ≤ p i) (hp : ∀ i V, ‖token c N w (X.warp i V)‖ ≤ q i)
include h hp
lemma haloP (i:Plot Y X)(V:Grid c):‖token c N w ((Trail Y X t).warp i V)‖ ≤ fair Y X p q i:=by
    change ‖token _ _ _ (payer Y X t V i.val)‖ ≤ _; unfold payer; split
    next hs=> apply le_trans (folkl _ _ _); apply prod_le_prod (fun _ _=>norm_nonneg _); intro j _; rcases j with j|j; · exact hp j V
              exact bought _ _ _ (h _ _)
    next _=> rw [map_zero,norm_zero]; exact fairness Y X hP hQ _
lemma renowned (he:1≤R)(hm:0 < m)(hk:0<k)(hD:0≤a)(hσ:σ<1)(ht: degreePrice B m k ≤σ)
    (hh:Ac.Hit Y.bud B p (a+k+1) A) (hx:Ac.Hit (home X) B ((metal X A)*taxed (oriD X) q R) (a+k) u)(hv:u+u*Animals.ballCost B*A≤ m):
   (∀ i V, ‖token c N w ((Trail Y X t).warp i V)‖ ≤ fair Y X p q i) ∧ Ac.Hit (home (Trail Y X t)) B (taxed (oriD (Trail Y X t)) (fair Y X p q) R) a (m*(1-σ)⁻¹):=by
   refine ⟨haloP Y X hP hQ h hp,?_⟩; have hs:(0:β→ℝ) ≤ taxed (oriD X) q R:=fun j => mul_nonneg (pow_nonneg (zero_le_one.trans he) _) (hQ j); refine priceV Y X (k:=k) hP hQ he ?_ hD; refine ⟨hm,hk,ht,hσ,fun i=> mul_nonneg (hs i.site) (prod_nonneg fun _ _=> wig_nn hP _),fun i=> budget_loosen (toned Y X ?_ hP hs (by linarith) hx hh i) hv⟩
   intro i; refine budget_mono (hh i) (fun j=> ?_) (fun j=> ?_)
   · split; exact mul_nonneg (hP _) (Real.exp_pos _).le; exact le_rfl
   split; next h=> refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hP _); exact mul_le_mul_of_nonneg_right (by linarith : a+k≤a+k+1) (Nat.cast_nonneg _)
   next _=> exact le_rfl
end YM.QCD.Ruby
