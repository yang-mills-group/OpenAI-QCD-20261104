import YM.VStages.Revolves
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
 (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ
variable {H:ℝ} {F:ℕ} {Q:ChangeQ →ℕ}

def delta₀ (F:ℕ):ℝ := betaQ F-su.slopeConstant/2
lemma slope_h (hF:0<delta₀ F): Gauge.slopeConstant su/2<betaQ F:=sub_pos.mp hF
abbrev relP (x:ChangeQ):ℝ:= 1 / ((x.lo:ℝ)+2)
structure Earlier (P:Docket K h s) (F:ℕ)(d:ChangeQ→ℕ):Prop where
    positive: 0 < delta₀ F
    hill (b) (S:Flight b.old b.new)(hv:d b ≤ S.L.val):
        P.slope b ≤ delta₀ F * relP b * Real.log (S.L.val:ℝ)
    metricF (b) (S:Flight b.old b.new)(hv:d b ≤ S.L.val): 3+(F:ℝ) ≤ delta₀ F/2*Real.log (S.L.val:ℝ)
    fee (b) (S:Flight b.old b.new)(hv:d b ≤ S.L.val) : 1 ≤ su.slopeConstant*Real.log (S.L.val:ℝ)

lemma high_bound (d:ChangeQ→ℕ)(F:ℕ) (he:0<delta₀ F): ∃ B:ChangeQ→ℕ, d≤B ∧Earlier P F B:=by
   have h:= Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
   let A(b) := delta₀ F*relP b
   have hp(b):0< A b:=by unfold A relP; positivity
   choose k hk using fun b=> eventually_atTop.1 ((((h.const_mul_atTop (hp b)).eventually_ge_atTop (P.slope b)).and ((h.const_mul_atTop (half_pos he)).eventually_ge_atTop (3+(F:ℝ)))).and ((h.const_mul_atTop (Gauge.slopeConstant_pos QCD.simple)).eventually_ge_atTop 1))
   exact ⟨fun b=> d b+k b,fun b=>by change d b≤ d b+_; omega,he,fun b S hv=>(hk b _ (by omega: k b ≤ S.L.val)).1.1, fun b S hv=> (hk b _ (by omega: k b ≤ S.L.val)).1.2, fun b S hv=> (hk b _ (by omega: k b ≤ S.L.val)).2⟩

variable {P J} {gate:ChangeQ→ℕ} (Y:Track P J p gate)
namespace Track
abbrev net (i:ℕ):= registerG (fun j=>P.slope (Y.node j)) i
def Staked (Y:Track P J p gate)(A:ℝ):Prop:=∀ i, Y.expenses i ≤ (i:ℝ)+A
variable {A x v:ℝ}
variable {T:ℕ→SparkMesh}
lemma sizing (i:ℕ): gate (Y.node i) ≤ (Y.spacing i).val:=by unfold spacing; rw [length_eq,← node_at]; exact Y.room i
variable (he:Earlier P F gate)
include he
lemma lane (i:ℕ): Y.net i≤ delta₀ F/2*Y.measure i:=by
   induction i with
   | zero=> simp [net,origin_cost]
   | succ i ih=>
     have ht := he.hill _ (show Flight (Y.node i).old (Y.node i).new from Y.flight i) (Y.sizing _)
     unfold net; rw [succeeding,Y.era, mul_add]; refine add_le_add ih (ht.trans ?_)
     have hp: relP (Y.node i) ≤ 1/2:=by unfold relP; apply one_div_le_one_div_of_le (by positivity) (by simp)
     exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hp he.positive.le).trans_eq (by ring)) (Real.log_nonneg ((by linarith [Y.per_len i]:1 ≤ ((Y.spacing i).val:ℝ))))
lemma priceF (i:ℕ): (3+F)*(i:ℝ) ≤ delta₀ F/2*Y.measure i ∧ (i:ℝ) ≤ su.slopeConstant * Y.measure i:=by
   induction i with
   | zero=> simp[Y.origin_cost]
   | succ i ih=>
      obtain ⟨h,h'⟩:=ih
      have H:=he.metricF _ (show Flight (Y.node i).old (Y.node i).new from Y.flight i) (Y.sizing _); have H':=he.fee _ (show Flight (Y.node i).old (Y.node i).new from Y.flight i) (Y.sizing _); push_cast; rw [Y.era,mul_add,mul_one,mul_add,mul_add]; exact ⟨add_le_add h H, add_le_add h' H'⟩ -- rw mul_one

lemma minor (ε:ℝ) (hp:0< ε):∀ᶠ i:ℕ in atTop, P.slope (Y.node i) ≤ ε * Real.log ((Y.spacing i).val:ℝ) :=by
   have hh:Tendsto (fun i=>relP (Y.node i)) atTop (𝓝 0):=by
     let t i:ℝ:=Y.level i
     unfold relP
     exact tendsto_const_nhds.div_atTop (show Tendsto (fun i=>t i+2) atTop atTop from Filter.tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp Y.free))
   have ht:Tendsto (fun i=>delta₀ F*relP (Y.node i)) atTop (𝓝 0):=by simpa using hh.const_mul (delta₀ F)
   filter_upwards [ht.eventually (ge_mem_nhds hp)] with i hi
   exact (he.hill _ (show Flight (Y.node i).old (Y.node i).new from Y.flight i) (Y.sizing _)).trans (mul_le_mul_of_nonneg_right hi (Real.log_nonneg ((by linarith [Y.per_len i]:1≤ ((Y.spacing i).val:ℝ)))))
lemma flight_meter (ε:ℝ)(hp:0< ε):∀ᶠ i:ℕ in atTop,Y.net i ≤ ε * Y.measure i:=by
   obtain ⟨n,h⟩:= eventually_atTop.mp (minor Y he _ (half_pos hp))
   let d:= Y.net n-ε/2 * Y.measure n
   have hx i (ht:n ≤ i): Y.net i ≤ d+ε/2* Y.measure i :=by
       induction i,ht using Nat.le_induction with
       | base=> unfold d; rw [sub_add_cancel]
       | succ i ht ih=> unfold net; rw [succeeding,era,mul_add,← add_assoc d]; exact add_le_add ih (h i ht)
   filter_upwards [(Y.long.const_mul_atTop (half_pos hp)).eventually_ge_atTop d,eventually_ge_atTop n] with i hi he
   exact (hx i he).trans (by linarith only [hi])

omit he

abbrev Hub (X:Survey Y T n)(x:ℝ)(F i:ℕ)(p:ℝ): Prop:=|p-central x (X.delta Y F) i| ≤ height_R i
abbrev ArcTime (x:ℝ)(i:ℕ)(p:ℝ): Prop := Y.scale x i/2 ≤ p∧ p≤2*Y.scale x i
lemma checks (h:Staked Y A)(S:Survey Y T n)(R:SparkMesh) (hp:Align Y R T n)(hn:i≤n)(hb:Hub Y S x F i v) :
    |v-(x +betaQ F*Y.measure i)| ≤ Y.net i+ (3+(F:ℝ))*(i:ℝ)+(1+F*(A+A)):=by
   let f:= S.delta Y F; have H:=S.sum_toll Y R hp F hn
   apply le_trans (b:=height_R i+(Y.net i+F*(Y.expenses 0 + Y.expenses i)))
   · rw [show v-(x+_)= (v-central x f i) - (registerG f i+ betaQ F*Y.measure i) from (by unfold central; ring)]
     exact (abs_sub ..).trans (add_le_add hb H)
   have hv:=h 0; simp only [Nat.cast_zero,zero_add] at hv
   unfold height_R; linarith only [mul_le_mul_of_nonneg_left (add_le_add hv (h i)) (by positivity:(0:ℝ)≤F)]

lemma payments (S:Survey Y T n)(X:ℕ→ℝ)(h: X 0=x)(hp:∀ k < i,|X k-X (k+1)-S.delta Y F k| ≤ 2) : Hub Y S x F i (X i):=by
    induction i with
    | zero=> simp[Hub,h,central,height_R]
    | succ i ih=>
       have hx:= hp i (by omega); obtain ⟨h₁,h₂⟩:=abs_le.mp hx
       obtain ⟨h₃,h₄⟩:=abs_le.mp (ih (fun k hk=> hp k (by omega))); unfold Hub central height_R; rw[succeeding]; unfold height_R central at h₃ h₄; push_cast; apply abs_le.mpr; constructor <;> linarith only [h₁,h₂,h₃,h₄]
include he
lemma perimeter (A:ℝ):∀ᶠ x:ℝ in atTop,∀ Y:Track P J p gate,Y.Staked A →∀ (n:ℕ)(S:ℕ→SparkMesh)(V:Survey Y S n)(R:SparkMesh), Align Y R S n→∀ i≤n,∀ t:ℝ,Hub Y V x F i t→ ArcTime Y x i t:=by
   let k:ℝ:= 1+F*(A+A); let u:=su.slopeConstant; let r:=betaQ F
   have ht:0≤ u:=(Gauge.slopeConstant_pos simple).le
   have hh:r≤u:=sub_le_self _ (mul_nonneg (by positivity:(0:ℝ)≤F) (by unfold Pearl.chargeF; positivity))
   filter_upwards [eventually_ge_atTop (2*k),eventually_ge_atTop (0:ℝ)] with x hx hx' Y hy n S V R hp i hi v hv
   obtain ⟨h1,h2⟩:= abs_le.mp (checks Y hy V R hp hi hv)
   have hc:= (Y.priceF he i).1; have hT:= Y.lane he i; have H: Y.net i+(3+(F:ℝ))*i+k ≤ x/2+(r-u/2)*Y.measure i:=by change _≤x/2+delta₀ F*_ ; linarith only [hx,hc,hT]
   change -(Y.net i+(3+_)*_+k) ≤ v-(x+r*_) at h1; change v-(x+r*_) ≤ Y.net i+(3+_)*_+k at h2; change (x+u*_)/2≤v∧v≤2*(x+u*_); constructor
   · linarith only [h1,H]
   linarith only [h2,H,mul_le_mul_of_nonneg_right hh (Y.measure_nn i),mul_nonneg ht (Y.measure_nn i),hx']
lemma slope_all (x ε:ℝ)(h:Staked Y A) (hε:0<ε):∀ᶠ i:ℕ in atTop,∀ (n:ℕ)(S:ℕ→SparkMesh)(V:Survey Y S n)(R:SparkMesh)(p:ℝ),i≤n→Align Y R S n→Hub Y V x F i p → |p/Y.measure i-betaQ F|≤ε:=by
   let d:=3+(F:ℝ); let k:ℝ:=1+F*(A+A)
   filter_upwards [Y.flight_meter he _ (half_pos hε), Y.outlay (k+|x|) d (ε/2) (half_pos hε),eventually_gt_atTop (0:ℕ)] with i hY hU hi n S V R p hn hP hg
   obtain ⟨h₁,h₂⟩:=abs_le.mp (checks Y h V R hP hn hg); have hv:=Y.measure_pos i hi; unfold k d at hU; apply abs_le.mpr; constructor
   · apply le_sub_iff_add_le.mpr; apply (le_div_iff₀ hv).mpr; linarith only [hY,hU,h₁,neg_abs_le x]
   apply sub_le_iff_le_add.mpr; apply (div_le_iff₀ hv).mpr; linarith only [hY,hU,h₂,le_abs_self x]
end Track
namespace Depot
open Track
variable (D:Depot P J p gate)(f: Tag P J p→ℕ)
def finance (f:Tag P J p→ℕ)(k:Tag P J p):ℕ:= f k+ ⌈stamp (J k.node.lo) k.toX⌉₊
local notation "f★"=> finance f
lemma staked (pad:ℕ→ℕ→ℕ) : (D.track f★ pad).Staked (f★ (D.fixed 0)):=by
    intro i; let T:= D.track f★ pad; let V:= T.beam i
    have hp: stamp (J V.node.lo) V.toX ≤ f★ V:= (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_add_left ..))
    exact hp.trans (by exact_mod_cast (show f★ V≤ i+ f★ (D.fixed 0) from (D.funds f★ pad i).2))
lemma solvent {F:ℕ}(he:Earlier P F gate):∀ᶠ x:ℝ in atTop,∀ pad:ℕ→ℕ→ℕ,∀ i:ℕ,let T:=D.track f★ pad; (f (T.beam i):ℝ)≤ T.scale x i:=by
  let k:= f★ (D.fixed 0)
  filter_upwards [eventually_ge_atTop (k:ℝ)] with x hx pad i T
  let q:=T.beam i
  have h:f q ≤ i+k:=le_trans (show f q ≤ f★ q from Nat.le_add_right ..) (D.funds f★ pad i).2
  apply (Nat.cast_le (α:=ℝ).mpr h).trans; unfold scale; push_cast; linarith only [hx,(T.priceF he i).2]
end Depot
#print axioms Track.slope_all
end YM.QCD.Acre.Stratum.MarchQ
