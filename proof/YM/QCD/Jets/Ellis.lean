import YM.QCD.Jets.Heat
import YM.Push.ABSOLUTE_SUMS.Fees
/-! # seed rent and kinetics rent converted on ALL intersections -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p γ t τ z γ' s X Y d ν θ o:ℝ}{l tL b b₀ b' B r:ℕ} {L:Ratio c f}
variable {D E J:Type} [Fintype D][Countable E][Countable J]
variable {μ:D→ℝ}{β:E→ℝ}{Q:J→ℝ}{R:Rise f F E J}{M:Fj D E J→ Support c} {O:Send L F D}
-- preL A. A move can buy much larger a2 support, finite horizon exact.
structure Fill (R:Rise f F E J)(β:E→ℝ)(Q:J→ℝ)(v w Y U X:ℝ)(b:ℕ): Prop where
 bud : 0 ≤ v
 cap : 0 ≤Y
 χ : Anchored (fun i=>(R.row i).site) β (fun i=>coverNumber b (R.row i).support) v X
 ε : Ac.Hit (fun i=>(R.front i).place) b (fun i=> Q i*Y^(R.front i).inv.card) w U

lemma anchored_each {ι:Type*}(f:ι→Site c)(w:ι→ℝ)(d:ι→ℕ)(h:Anchored f w d a p)(hv:0≤a)(he:∀ i,0 ≤ w i)(i:ι): w i ≤p:=by
  have ht:= budget_sum (h (f i)) {i}; rw [sum_singleton,if_pos rfl] at ht; apply le_trans _ ht; exact le_mul_of_one_le_right (he _) (Real.one_le_exp (mul_nonneg hv (by positivity)))

lemma leeway (L:Side)(V σ A:ℝ)(l k:ℕ): rem L l k A V σ=rem L l k A 1 σ*V :=by unfold rem payment degreeIncome; ring
lemma rem_nn (L:Side)(V σ A:ℝ)(l k:ℕ)(ht:0≤V)(hp:0<σ):0 ≤ rem L l k A V σ:=by unfold rem payment degreeIncome; have he:0 < 1-Real.exp (-σ):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)); positivity

lemma offers {ι:Type*}{W: ι→Support f}(x':ι→ Site f)(Q:ι→Support c)(K:ι→ℝ)(he:∀ i,x' i∈W i)(hh:∀ i, Q i ⊆enlargement L l b (W i))(h:∀ i,0≤K i) (hq:Anchored x' K (fun i=>coverNumber tL (W i)) a X)(hB:0<b)(hm:tL ≤ 2*b)(hv: reserve a v (conversion L l) w) : Ac.Hit Q b K v (rem L.count l b v X w) := coarsen L l b tL _ _ he _ h hq _ hh hB hm zero_le_one hv 0 K h (fun _=> by simp)

lemma hail (ht:Fill R β Q a ξ Y X p b)(hz:0≤z)(H:Cents R β Q x t)(hv:p ≤1)(hs:∀ i,M i⊆ enlargement L l B (native O R i))(hB:0<B)(hb:b ≤2*B)(hr: reserve a v (conversion L l) w):
 Ac.Hit (fun i:E=> M (Sum.inr (.inl i))) B (fun i=> z*(Real.exp (β i)-1)) v (z*Real.exp 1 * rem L.count l B v p w):=by
   let P i:= (R.row i).support; let Y i:= M (Sum.inr (.inl i))
   have hh: Ac.Hit Y B β v _:= offers (fun i=> (R.row i).site) _ _ (fun i=>(R.row i).anchor) (fun i=> hs _) H.pos ht.χ hB hb hr
   apply Labels.raise_prices _ _ (w:=fun i=>z*Real.exp 1*β i) (fun i=> mul_nonneg hz (sub_nonneg.mpr (Real.one_le_exp (H.pos i)))) (heights_factor _ _ _ _ hh (fun _=>rfl) (mul_nonneg hz (Real.exp_pos _).le))
   intro i; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hz; have he:= (anchored_each _ _ _ ht.χ ht.bud H.pos i).trans hv; have hB:= mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (H.pos i)
   have hβ:=Real.add_one_le_exp (-β i); rw [Real.exp_neg] at hβ; have hC:= mul_le_mul_of_nonneg_right hβ (Real.exp_pos (β i)).le; rw [add_mul,inv_mul_cancel₀ (Real.exp_ne_zero (β i))] at hC; linarith

lemma honors (ht:Fill R β Q a ξ Y X p b)(hz:0≤z)(hν:1≤ν)(hC:1≤τ)(H:Cents R β Q x t)(hw:0≤o)(hs:∀ i,M i⊆enlargement L l B (native O R i))(hB:0<B)(hb:b≤2*B)(hr:reserve ξ v (conversion L l) w)
 (hv : ∀ i:J, z*ν^(R.front i).inv.card* τ^(Cove.kappa (O.trim+1) F*(R.front i).inv.card) ≤ o*Y^(R.front i).inv.card) :
 Ac.Hit (fun i:J=>M (.inr (.inr i))) B (fun i:J=> z*((1:ℝ)*ν^(R.front i).inv.card)*τ^(Cove.kappa (O.trim+1) F*(R.front i).inv.card)*Q i) v (o* rem L.count l B v X w):=by
  let W i:= (R.front i).place; let A i:= (R.front i).inv; let T i:= M (.inr (.inr i)); let V i:=Q i*Y^(A i).card
  have he i:= (R.front i).alive.mono (show A i ⊆ W i from (R.front i).part)
  choose f hf using he
  have hi i:0 ≤ V i:=mul_nonneg (H.non i) (pow_nonneg ht.cap _)
  have hm := offers f T V hf (fun i=> hs _) hi (Labels.anchor_weaker _ _ hi ht.ε f hf) hB hb hr
  apply Labels.raise_prices _ _ (w:=fun i=>o*V i) ?_ (heights_factor _ _ _ _ hm (fun i=>rfl) hw)
  · intro i; simp only [one_mul]; exact (mul_le_mul_of_nonneg_right (hv i) (H.non i)).trans_eq (by dsimp [V,A]; ring)
  intro i; have hu:=H.non i; have hν:=zero_lt_one.trans_le hν; have hC:=zero_lt_one.trans_le hC; positivity

lemma award (ht:Fill R β Q a a Y X p b)(hp: Peak O t x y τ μ)(H:Cents R β Q x t) (H₀:Ac.Hit (fun i=> M (.inl i)) B μ v γ)(hz:0≤z)(hν:1≤ν)(hv:p≤1)(hw:0≤o) (hs:∀ i,M i⊆ enlargement L l B (native O R i))(hB:0<B)(hb:b≤2*B)(hr:reserve a v (conversion L l) w)
 (ht' : ∀ i:J, z*ν^(R.front i).inv.card* τ^(Cove.kappa (O.trim+1) F*(R.front i).inv.card) ≤ o*Y^(R.front i).inv.card) :
 Ac.Hit M B (paidSet O R μ β Q τ z ν 1) v (γ+(z*Real.exp 1*rem L.count l B v p w+o*rem L.count l B v X w)) := by
   have hg:=Labels.together _ _ _ H₀ (Labels.together _ _ _ (hail ht hz H hv hs hB hb hr) (honors ht hz hν hp.post H hw hs hB hb hr ht')); convert hg using 1 <;> funext i <;> rcases i with i|i|i <;> rfl
end YM.QCD.Jets.Touch
