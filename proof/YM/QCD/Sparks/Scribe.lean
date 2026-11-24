import YM.QCD.Sparks.Spurn

/-! # choose budgets and rotated inflation afterwards. The intrinsic all-period
prices are independent of the diagnostic levels chosen for Ward. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve RG
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side}{b k:ℕ}{r R a C:ℝ}{I:Type}{K:Typewriter k}

def ranks (k:ℕ):ℝ:= Fintype.card (Fin k→su.ColorIndex)
def orange (k:ℕ)(a C:ℝ):= ranks k*C*Real.exp (a*(6*k))
lemma redraft (h:∀ i, ‖K i‖≤ C*aim r i) (he:0≤C)(hp:0 ≤ a)(q:Rim k)(p:Ryde q):
    (rivet K ⟨q,p⟩).paid a≤ orange k a C*Real.exp (-(r-2*a)*cost q):=by
  let B:=rivet K ⟨q,p⟩
  have ht i : ‖B.coeff i‖≤C*Real.exp (-r*cost q):=by
    unfold B rivet; rw [norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) (by rw [Complex.norm_real]; exact revenue ..)).trans
    have hp:= h (raise q i); rw [aim,cost_raise] at hp; exact hp
  have H : B.price≤ ranks k*(C*Real.exp (-r*cost q)):= (sum_le_sum (fun i _=> ht i)).trans (le_of_eq (by simp [ranks]))
  change Real.exp (a*B.span) * B.price ≤ _
  have hx : (↑B.span : ℝ)≤2*cost q+6*k:=by exact_mod_cast cost_pays q p K
  apply (mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hx hp)) H B.price_nn (Real.exp_pos _).le).trans_eq
  unfold orange; rw [mul_assoc (ranks k*C),← Real.exp_add]; rw [mul_comm (Real.exp _),mul_assoc _,mul_assoc C, ← Real.exp_add] -- inspect
  rw [mul_assoc]; congr 3; ring

def tab (q : Rim k)(a:ℝ):= Real.exp (-a*cost q)
def brochure (q:Tilt k): Rim k× (Fin k→su.ColorIndex) := ((q.1,fun i=> ((q.2 i).1,(q.2 i).2.1)),fun i=>(q.2 i).2.2)
def flyer (k : ℕ): Tilt k≃ (Rim k× (Fin k→su.ColorIndex)) :=⟨brochure,fun p=>raise p.1 p.2,fun _=>rfl,fun _=>rfl⟩
lemma c_inh: Nonempty su.ColorIndex:=by
  -- from simple
  change Nonempty (Fin su.lieDim); rw [Roots.lie_dimension]; infer_instance
lemma cost_can {r:ℝ}(k:ℕ)(hp:0<r): Summable fun x:Rim k=>tab x r:=by
  letI:=c_inh
  let p:= Classical.arbitrary (Fin k→su.ColorIndex)
  have hi (q): tab q r = aim r (raise q p):= rfl
  simp_rw [hi]; exact (aim_supply k hp).comp_injective (i:=fun x=>raise x p) (by intro u v h; exact congr_arg (fun z:Tilt k=>(brochure z).1) h)

def tables (k:ℕ)(a C:ℝ):= orange k a C*(2:ℝ)^(2*k)*(YM.Extra.Iteration.momentPrice (2*k) a)
def sumTab (k:ℕ) (a:ℝ):= ∑' i:Rim k,tab i a
def req (k:ℕ)(a C:ℝ):= tables k a C * sumTab k a
lemma table_pos (h:0≤C)(he:0<a)(k:ℕ):0≤tables k a C:=by unfold tables orange ranks; have ht:=YM.Extra.Iteration.momentPrice_pos (2*k) he; positivity
lemma req_pos (h:0≤C)(he:0<a)(k:ℕ):0≤req k a C:=mul_nonneg (table_pos h he k) (tsum_nonneg fun i:Rim k=>(Real.exp_pos _).le)
lemma standout (h:∀ i, ‖K i‖≤ C*aim r i)(hg : Glow K) (hp : 4*a≤r) (he:0≤C)(ha:0<a):
    Fractal (rivet K) a (req k a C):=by
  let v i (p : Ryde i):=(rivet K ⟨i,p⟩).paid a
  have ht i : ∑ j:Ryde i,v i j ≤ tables k a C*tab i a:=by
    let D:= orange k a C; have hD : 0≤ D:= by unfold D orange ranks; positivity
    apply (sum_le_sum (fun p (_:p∈univ)=> redraft h he ha.le i p)).trans
    rw [sum_const,card_univ,nsmul_eq_mul]; let u:ℝ:= cost i
    have hu : 0≤ u:=by positivity
    have he : ↑(Fintype.card (Ryde i)) ≤ (2*(1+u))^(2*k):= (cost_count i).trans_eq (by unfold u; ring_nf)
    apply (mul_le_mul_of_nonneg_right he (show 0≤ D*_ from mul_nonneg hD (Real.exp_pos _).le)).trans
    rw [mul_pow]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (YM.Extra.Iteration.spendMoment (2*k) ha hu) (show (0:ℝ)≤2^(2*k) by positivity)) (show 0 ≤ D*_ from mul_nonneg hD (Real.exp_pos _).le))
    rw [show _* (D*_) = tables k a C * Real.exp (a*u + -(r-2*a)*u) from ?_]; -- see
    · apply mul_le_mul_of_nonneg_left _ (table_pos ‹0≤C› ha _); apply Real.exp_monotone; change _≤ -a*u; nlinarith
    unfold tables; rw [Real.exp_add]; unfold D u; ring
  have hc := YM.Extra.Iteration.Cost.sigma (F:=fun i:Snug k=> (rivet K i).paid a) (show SumBudget (fun i:Rim k=> tables k a C*tab i a) (req k a C) from YM.Extra.Iteration.Cost.scale ⟨fun i=>(Real.exp_pos _).le, cost_can k ha,le_rfl⟩ _ (table_pos he ha _)) (fun i:Rim k=> show SumBudget (fun j:Ryde i=>v i j) (tables k a C * tab i a) from ⟨fun j=> (Bloom.price_nn ..).trans ((rivet K ⟨i,j⟩).paidUp ha.le),Summable.of_finite, by rw [tsum_fintype]; exact ht i⟩) -- missing F
  exact ⟨ha.le,cash_top _ hg,hc.2.1,hc.2.2⟩
end YM.QCD.Sparks
