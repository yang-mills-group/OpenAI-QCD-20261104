import YM.QCD.Revolve.Kent

/-!
# issuance of canonical signed self-adjoint (gamma) arrays. control after-L
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Function Lattice Wilson Kit Pine Cost Eyrie Quarry Rudder RG Finset Filter Stationary Sparks
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n : Side}{k : ℕ}{I J: Type}{P : I→Bloom k}{V : J→ Bloom k}{r t u b C:ℝ}
lemma thinner (W:Bloom k){r a:ℝ}(hp:a≤r): W.paid a≤ W.paid r:=by unfold Bloom.paid; apply mul_le_mul_of_nonneg_right _ W.price_nn; gcongr
lemma reduction (hP:Fractal P r u)(h:0≤t)(he:t≤r)(hv:u≤C): Fractal P t C:=by
  have hp i:= thinner (P i) he; have hg: Summable fun i=>(P i).paid t:=hP.bills.of_nonneg_of_le (fun i=>(P i).price_nn.trans ((P i).paidUp h)) hp
  exact ⟨h,hP.sect,hg,(hg.tsum_le_tsum hp hP.bills).trans (hP.bill.trans hv)⟩
lemma joins (h:Fractal P r u)(p:Fractal V r C): Fractal (Sum.elim P V) r (u+C):=by
  have hg: HasSum (fun i=>(Sum.elim P V i).paid r) ((∑' i,(P i).paid r)+∑' i,(V i).paid r):= HasSum.sum h.bills.hasSum p.bills.hasSum
  exact ⟨h.degree,fun v=>Sum.rec (fun i=>h.sect i) (fun i=>p.sect i) v,hg.summable,hg.tsum_eq.trans_le (add_le_add h.bill p.bill)⟩
def shape (W: Bloom k)(b:ℂ): Bloom k:= {W with coeff:= b • W.coeff}
lemma shade_p (W: Bloom k)(b v): (shape W b).paid v=‖b‖*W.paid v:=by unfold Bloom.paid Bloom.price shape; simp_rw [Pi.smul_apply,norm_smul,← mul_sum]; change Real.exp _ *_=_; rw [mul_left_comm]; rfl
lemma shade_h (W: Bloom k)(b v): (shape W b).hues v=b • W.hues v:=by unfold Bloom.hues; rw [Finset.smul_sum]; exact sum_congr rfl fun i _=> smul_comm ((↑(∏ j,v j (i j)):ℂ)) b (W.coeff i)
lemma shape_ok (h:Fractal P r C)(b:ℂ): Fractal (fun i=>shape (P i) b) r (‖b‖*C):=by
  refine ⟨h.degree,fun i u v=>?_, ?_,?_⟩
  · rw [shade_h,shade_h,h.sect,Matrix.mul_smul,Matrix.smul_mul]
  · simp_rw [shade_p]; exact h.bills.mul_left _
  simp_rw [shade_p,tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.bill (norm_nonneg _)
lemma shape_keeps (W:Bloom k)(b:ℂ)(t:Site n)(U:Grid n): (shape W b).tonic t U=b • W.tonic t U:=by
  unfold Bloom.tonic; rw [← Matrix.smul_mul, ride_smul]; have hp : (shape W b).taste U = b • W.taste U := funext fun i=> shade_h W b (fun j=> (W.petals j).atSite U i); rw [hp]; rfl
lemma gemini (U: Grid n)(h:Fractal P r u)(e:Fractal V t C): dust (Sum.elim P V) n U=dust P n U + dust V n U:=(HasSum.sum (f:=fun i=>(Sum.elim P V i).tonic 0 U) (h.tonics ..).of_norm.hasSum (e.tonics ..).of_norm.hasSum).tsum_eq
lemma lit (U: Grid n)(b:ℂ):dust (fun i=>shape (P i) b) n U=b • dust P n U:=by unfold dust; simp_rw [shape_keeps]; rw [tsum_const_smul'']
-- construct rotating average
noncomputable section
variable (P)
def leaflet (b : Signed)(i:I):Fin k→Slot:=fun j=>(garment b ((P i).petals j)).choose
def flat (b : Signed)(i:I):Fin k→ℝ:=fun j=>(garment b ((P i).petals j)).choose_spec.choose
def select (b:Signed)(i:I):Bloom k:= quest (P i) b (starTraffic b) (leaflet P b i) (flat P b i)
variable {P}
lemma portion (h: Fractal P r C)(s : Signed): Fractal (select P s) r (Real.exp (r*(2*k)) * C):=by
  have ht i : (select P s i).paid r≤ Real.exp (r*(2*k))*(P i).paid r:= quest_priced r h.degree (fleetLeft s) fun j=> (garment s _).choose_spec.choose_spec
  have hp := h.bills.mul_left (Real.exp (r*(2*k))); have hv:=hp.of_nonneg_of_le (fun i=> (select P s i).price_nn.trans ((select P s i).paidUp h.degree)) ht
  refine ⟨h.degree,fun i=> quest_rot _ _ _ (h.sect i),hv,(hv.tsum_le_tsum ht hp).trans ?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.bill (Real.exp_pos _).le
lemma assigned (h : Fractal P r C)(U: Grid n)(s): dust (select P s) n U=inverted (dust P n) s U:=by
  obtain ⟨L,H⟩:=auraCL (star (scaleA s n)); have hx i:(select P s i).tonic 0 U=L ((P i).tonic 0 (pull s 0 U)):=by
    rw [H]; exact quest_score 0 (fleetLeft s) (gems s n) (fun j=> (garment ..).choose_spec.choose_spec) U
  unfold dust inverted; simp_rw [hx]; rw [← L.map_tsum (h.tonics ..).of_norm,H]

def en (P:I→Bloom k)(i: Signed × I):= select P i.1 i.2
def rockPrice (k:ℕ)(r C:ℝ):=(Fintype.card Signed :ℝ)*Real.exp (r*(2*k)) * C
lemma rocky (h : Fractal P r C): Fractal (en P) r (rockPrice k r C):=by
  let f (i:Signed×I) := (en P i).paid r; have ht (i:Signed): SumBudget (fun j => f (i,j)) (Real.exp (r*(2*k))*C):= by
    have hx:=portion h i; exact ⟨fun j=> (select P i j).price_nn.trans ((select P i j).paidUp h.degree),hx.bills,hx.bill⟩
  have hu:= YM.Extra.Iteration.Cost.product (F:=f) (YM.Extra.Iteration.Cost.finite _ (YM.Extra.Iteration.Cost.nonneg (ht 1))) ht
  exact ⟨h.degree,fun i=> (portion h _).sect _,hu.2.1, hu.2.2.trans_eq (mul_assoc ..).symm⟩

def feast (P:I→Bloom k)(i : Signed×I):Bloom k := shape (en P i) (↑((Fintype.card Signed:ℝ)⁻¹))
lemma invested (h : Fractal P r C): Fractal (feast P) r (Real.exp (r*(2*k))*C):=by
  have he:=shape_ok (rocky h) (↑((Fintype.card Signed:ℝ)⁻¹)); apply reduction he h.degree le_rfl (le_of_eq ?_); simp only [Complex.norm_real,norm_inv, Real.norm_natCast]; unfold rockPrice; field_simp
lemma routed (h : Fractal P r C)(U : Grid n): dust (feast P) n U=hearth (dust P n) U:=by
  unfold feast; rw [lit]; have ht i: Summable (fun j=>(select P i j).tonic 0 U):= ((portion h i).tonics ..).of_norm
  have hx : dust (en P) n U = ∑ i:Signed,inverted (dust P n) i U:=by
    unfold dust; rw [((rocky h).tonics 0 U|>.of_norm).tsum_prod, tsum_fintype]; exact sum_congr rfl fun i _=> assigned h _ _
  rw [hx]; rfl
end
end YM.QCD.Revolve
