import YM.MassiveQCD.Plate.Strand
import YM.MassiveQCD.Plate.Prize
/-! # Multiple-billing with through-slope under `Woven` and apertures. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew
open ConnectedActivityE6 Blaze King Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c L:Side}{m k B N:ℕ}{s t h a r η σ A θ:ℝ}{P:BudgetPoint}{J D I E:Type}[Fintype I]
local notation "Z"=> Keys c N
namespace Reel
variable (p : I → Site c)(w₀ : I→ℝ)
variable (N)(G: Reel c N I E)
noncomputable def voiceE (m:ℕ)(a:ℝ)(X:ℕ):ℝ:= m.factorial*(Real.exp a / a^m)*(6*(1+X:ℝ))^m
lemma tariffs {X:Support c}(h:0<a) (m :ℕ) : (1+(wag X B:ℝ))^m ≤ voiceE m a B*Real.exp (a*coverNumber B X):=by
    let V:ℝ:= coverNumber B X; let u:=(B:ℝ); have hb:0 ≤ V:= Nat.cast_nonneg _; have hk:0≤u:=Nat.cast_nonneg _
    have hf :1+(wag X B:ℝ) ≤6*(1+u)*(1+V):=by unfold wag; push_cast; change 1+ (V*(4*u+2)+2*u) ≤_; nlinarith only [hk,hb,mul_nonneg hk hb]
    refine (pow_le_pow_left₀ (by positivity) hf m).trans ?_
    rw [mul_pow]; refine le_trans (mul_le_mul_of_nonneg_left (?_ :(1+V)^m ≤(m.factorial:ℝ)*Real.exp (a*(1+V))/a^m) (by positivity)) ?_
    · have hz :0 ≤ a*(1+V):=by positivity
      apply (le_div_iff₀ (pow_pos h m)).mpr; rw [← mul_pow,mul_comm _ a]; rw [mul_comm ((m.factorial:ℕ):ℝ)]; exact (div_le_iff₀ (show 0 < (m.factorial:ℝ) by positivity)).mp (Real.pow_div_factorial_le_exp _ hz m)
    rw [mul_add a,mul_one,Real.exp_add]; exact le_of_eq (by unfold voiceE V u; ring)
-- Type universe function.H restraints

noncomputable def changeFare (f:E→ℝ):= fun i=>(∏ j∈(G.z i), |w₀ j|)*f i
noncomputable def choicePay (f:E→ℝ)(p:E→Prop)(i:E):=if p i then f i else 0
noncomputable def flight {k:ℕ}(m:ℕ)(G: Reel c N I E)(f:E→ℝ) := fun i=> (1+(wag (G.addr i).support k:ℝ))^m*f i
variable (X:Gem c (ample N I) J)(q:I→Bool)(φ r₀:ℝ)(S:Set (Finset I))(D:J→ Finset I)
set_option quotPrecheck false
local notation "S'"=> render N p φ r₀ X D S
lemma fresh_bill (X:Support c)(m:ℕ)(f:ℝ)(h:0<a)(hf:0≤f) : Real.exp (σ*coverNumber B X)*((1+(wag X B:ℝ))^m*f) ≤voiceE m a B*(f* Real.exp ((σ+a)*coverNumber B X)):=by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (tariffs h m) hf) (Real.exp_nonneg _)).trans_eq (by rw [add_mul (σ:ℝ),Real.exp_add]; ring)
lemma fiscal {f:J→ℝ}(hf:∀ i,0≤f i)(h:0<a)(hg:Ac.Hit (fun i=>(X.addr i).support) (radiusB t) f (σ+a) A)(m:ℕ):
    Ac.Hit (fun i=>((S').addr i).support) (radiusB t) (flight N (k:=radiusB t) m (S') (f ∘ Subtype.val)) σ (voiceE m a (radiusB t)*A):=by
   let g:=voiceE m a (radiusB t); intro x; let F i:= if x∈(X.addr i).support then f i*Real.exp ((σ+a)*coverNumber (radiusB t) (X.addr i).support) else 0; refine budget_mono (budget_pull _ (Subtype.val_injective (p:=fun i:J=> D i∈ S ∧ (D i).Nonempty ∧ (D i).image p⊆ (X.addr i).support)) (budget_scale (show 0 ≤ g by unfold g voiceE; positivity) (show SumBudget F A from hg x))) ?_ ?_
   · intro i; unfold flight; split; exact mul_nonneg (mul_nonneg (by positivity) (hf _)) (Real.exp_nonneg _); exact le_rfl
   intro i; unfold flight F; split; next hh=> rw [if_pos (show _ from (show x∈(X.addr i.val).support from hh)),mul_comm _ (Real.exp (σ*_))]; exact fresh_bill _ m _ h (hf _)
   next hh=> rw [if_neg (show x∉(X.addr i.val).support from hh),mul_zero]
lemma for_voices (L:Side)(m:ℕ)(a:ℝ): Rate su L 0 fun t=>voiceE m a (radiusB t):=by
    unfold voiceE; simpa only [zero_mul] using (((((Rate.const (1:ℝ)).add Rate.radius_price).mul_left (6:ℝ)).pow m).mul_left ((m.factorial:ℝ)*(Real.exp a / a^m)))
-- many absorb arbitrary therm credit `g.L^requested`; singular clocks no adjacency.Hex
omit [Fintype I] in
lemma plyprice (t:ℕ) (hz: 8≤ t) (E:Finset I)(i:RegularAddress c)(a z:ℝ)(he:2≤E.card)(h:Spaced p E t)(ht:E.image p⊆ i.support)(ha:0≤a)(hp:∀ i, |w₀ i| ≤ z) (hk : z ≤ Real.exp (a/128*(t:ℝ))):
    (∏ i∈E,|w₀ i|) ≤ Real.exp (-(a/128)*(t:ℝ))*Real.exp (a*coverNumber t i.support):=by
    have hm:(t:ℝ)*E.card≤64*(coverNumber t i.support:ℝ):=by exact_mod_cast (OPE.Log.separatedMarks E p h hz (by omega) he _ ht)
    refine (prod_le_prod (fun i _=> abs_nonneg (w₀ i)) (fun i _=> (hp i).trans hk)).trans ?_
    rw [prod_const,← Real.exp_nat_mul,← Real.exp_add]; have hE:(2:ℝ)≤E.card:=by exact_mod_cast he
    apply Real.exp_monotone; nlinarith only [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) t), mul_le_mul_of_nonneg_left hm ha,mul_le_mul_of_nonneg_left hE (mul_nonneg ha (Nat.cast_nonneg t))]
lemma playfield (p:I→Site c)(_q:I→Bool)(f:E→ℝ) (hf:∀ i,0≤f i)(he:8 ≤ radiusB t)(ha: 0<a)(hp:∀ i,|w₀ i| ≤ Real.exp (a/128*radiusB t))(h: ∀ i,(G.z i).image p ⊆ (G.addr i).support)(hx:∀ i, Spaced p (G.z i) (radiusB t))(hw:Ac.Hit (fun i=>(G.addr i).support) (radiusB t) f (σ+a) A):
    Ac.Hit (fun i=>(G.addr i).support) (radiusB t) (choicePay (changeFare N w₀ G f) (fun i=> 2≤(G.z i).card)) σ (Real.exp (-(a/128)*radiusB t)* A) :=by
   intro x; let V:=Real.exp (-(a/128)*radiusB t); refine budget_mono (budget_scale (show 0≤V from Real.exp_nonneg _) (hw x)) ?_ ?_
   · intro i; split; swap; · exact le_rfl
     unfold choicePay; split; exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=>abs_nonneg _) (hf _)) (Real.exp_nonneg _); rw [zero_mul]
   intro i; dsimp only; split; swap; next _=> rw [mul_zero]
   unfold choicePay changeFare; split; swap; next _=> rw [zero_mul]; exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hf _) (Real.exp_nonneg _))
   next hz=>
     apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (plyprice p w₀ (radiusB t) he (G.z i) (G.addr i) a _ hz (hx i) (h i) ha.le hp le_rfl) (hf i)) (Real.exp_nonneg _)).trans_eq; rw [add_mul (σ:ℝ),Real.exp_add]; ring
lemma playability (L:Side)(pz:ℝ)(f:ℝ→ℝ)(hr:0<a)(hf:Rate su L pz f):∀ᶠ t:ℝ in atTop, |f t| ≤ Real.exp (a/128*radiusB t):=by
    let s:=a/128; have he :0<s:=by unfold s; positivity
    filter_upwards [(hf.mul (Calm.expHigh L he (t:=-pz-1))).below (by linarith) 1 zero_lt_one] with t h
    let H:= radiusB t; rw [abs_mul, abs_of_pos (Real.exp_pos _),neg_mul,Real.exp_neg] at h -- check
    exact (div_le_one₀ (Real.exp_pos _)).1 (by rw [div_eq_mul_inv]; exact h)
end Reel
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Reel.playfield
