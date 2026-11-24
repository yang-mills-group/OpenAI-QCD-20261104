import YM.QCD.Cove.Brash
import YM.Push.ABSOLUTE_SUMS.Distinct
/-! # rooted whole words census. Grade rewards on at least one inherited parent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj Filter
open Further.ShellBirth49.Fusing Collide Push.AbsoluteSums Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f: Side} {E D J:Type}{F:ℕ}{S:Ratio c f} {b:ℕ}{a y z q h h' u d γ r δ υ t:ℝ} {μ:D→ℝ}{β:E→ℝ}{κ:J→ℝ}
local notation "I"=> Fj D E J
variable (G: Send S F D)(P:Rise f F E J)

-- marks multiplicative pn

def paidSet (μ:D→ℝ)(β:E→ℝ)(κ:J→ℝ)(q z r υ:ℝ): Fj D E J→ℝ := Sum.elim μ (Sum.elim (fun i=> z*(Real.exp (β i)-1)) (fun i=> z*(υ*r^(P.front i).inv.card)*q^(kappa (G.trim+1) F*(P.front i).inv.card)*κ i))
lemma expensesW (s:Finset I)(q z r:ℝ): ∏ i∈s,paidSet G P μ β κ q z r υ i=z^((leftE s).card + (spent s).card)*υ^(spent s).card*r^(invSize P s)*q^(kappa (G.trim+1) F*invSize P s)*priceSet s μ β κ:=by
  conv_lhs=>arg 1; rw [← pinch s]
  let A : I→ℝ:= paidSet G P μ β κ q z r υ
  simp only [pin,prod_disjSum,paidSet,Sum.elim_inr,Sum.elim_inl]; simp only [invSize,priceSet, mul_sum, Finset.prod_mul_distrib, Finset.prod_const,← Finset.prod_pow_eq_pow_sum] -- check lemma & syntax conv
  ring


lemma nightly (s:Finset I)(hs:s.Nonempty)(he:leftE s=∅)(hk:spent s=∅)(U:Grid f): hue G P t s U=0:=by
 unfold hue; split
 next h=>
  change dye G P t s U=_; apply Subtype.ext; change light _ (dye G P t s U)=0; rw [dipping]; unfold made; rw [he,hk,prod_empty,prod_empty,mul_one,map_one,map_one]; have hp:(ops s).Nonempty:=by
    have hv:=pinch s; rw [he,hk] at hv; rw [←hv] at hs; obtain ⟨w,hw⟩:=hs; unfold pin at hw; cases w
    next i=> exact ⟨i,by simpa using hw⟩
    next i=> rcases i with h|h <;> simp at hw
  have hh: axle G U s 1 = 0:=by
    unfold axle; obtain ⟨i,hi⟩:=hp; rw [← noncommProd_erase_mul _ hi]
    rw [ContinuousLinearMap.mul_apply,show bucks G _ U 1=0 from G.fuel U _,map_zero]
  rw [hh,map_zero]
 exact rfl
variable {M:Fj D E J→Support c}
lemma terry (hp:Peak G t h h' q μ)(ht:Cents P β κ h t)(hw:P.Wave t)(H:Ready M b (paidSet G P μ β κ q z r υ) a γ δ d)(hs:0≤a)(hz:1 ≤ z)(hu:1 ≤ r)(he:0 ≤ υ)(j:Site c)(m:ℕ):
    SumBudget (fun s:Finset I=> if spark M s ∧ j∈s.biUnion M ∧ m ≤ s.card-1 then ∏ i∈s,paidSet G P μ β κ q z r υ i *currency b a (M i) else 0) (γ*d^m*(1-d)⁻¹) :=by
  let X:= paidSet G P μ β κ q z r υ; have hv:=touch_tail M b H j m
  refine budget_mono hv (fun i=> ?_) ?_
  · split; exact prod_nonneg fun k _=> mul_nonneg (H.2.2.2.2.1 _) (Real.exp_pos _).le; exact le_rfl
  intro i; split
  next he=> rw [if_pos he.2.2,touches,if_pos ⟨spark_ac M M he.1 (fun _ _ _ _ h=> h), he.2.1⟩]
  next he=> exact hv.1 _

-- actual sup, allows if forced huge. want up to C post. extract parent contributions o

def jewel (M : I→Support c)(μ:D→ℝ)(β:E→ℝ)(κ:J→ℝ)(q:ℝ)(s:Finset I):ℝ:= if spark M s ∧ (leftE s ≠∅ ∨ spent s ≠∅) then q^(kappa (G.trim+1) F*invSize P s)*priceSet s μ β κ else 0
lemma pinches (hp:Peak G t h h' q μ)(ht:Cents P β κ h t)(hw:P.Wave t)(U:Grid f){s : Finset I}(he:spark M s) : load (fun _=>h') (light _ (hue G P t s U)) ≤ jewel G P M μ β κ q s := by
  unfold jewel; split
  · exact summing G P hp s U hw ht
  next hj=>
    push Not at hj
    obtain ⟨h1,h2⟩:=hj he; rw [nightly G P s he.1 h1 h2,map_zero,load_zero]

lemma value_hit (hp:Peak G t h h' q μ)(ht:Cents P β κ h t)(hw:P.Wave t)(H:Ready M b (paidSet G P μ β κ q z r υ) a γ δ d)(hs:0≤a)(hz:1 ≤ z)(hu:1 ≤ r)(he:0 ≤ υ)(j:Site c)(m:ℕ):
    SumBudget (fun s:Finset I=> if j∈s.biUnion M ∧ m ≤ s.card-1 then z*υ^(spent s).card*r^(invSize P s)*jewel G P M μ β κ q s *currency b a (s.biUnion M) else 0) (γ*d^m*(1-d)⁻¹) :=by
  let V:= jewel G P M μ β κ q; have hv (s):0≤ V s:=by
     by_cases he:spark M s; · exact (load_nn ..).trans (pinches G P hp ht hw (1:Grid f) he)
     simp [V,jewel,he]
  have hz':=zero_lt_one.trans_le hz; have hr:=zero_lt_one.trans_le hu
  have hf:=terry G P hp ht hw H hs hz hu he j m
  refine budget_mono hf (fun i=> ?_) fun i=> ?_
  · split; exact mul_nonneg (mul_nonneg (by positivity) (hv i)) (Real.exp_pos _).le; exact le_rfl
  split
  next hi=>
    change z*_^_*r^_*V _*currency _ _ _ ≤_
    by_cases ht: V i=0; · rw [ht,mul_zero,zero_mul]; exact hf.1 _
    have hM: spark M i ∧ (leftE i≠∅∨spent i ≠∅) := by_contra (fun h=> ht (if_neg h))
    have hk : 1≤(leftE i).card+(spent i).card:= hM.2.elim (fun h=> by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h); omega) (fun h=> by have:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h); omega)
    rw [if_pos ⟨hM.1,hi⟩, prod_mul_distrib]; apply mul_le_mul
    · rw [expensesW]; unfold V jewel; rw [if_pos hM, ← mul_assoc]; -- simp multiplication; use explicit calc
      have hv:=hv i; unfold V jewel at hv; rw [if_pos hM] at hv
      rw [mul_assoc (z*_^_*r^_),mul_assoc (z^_*_^_*r^_)]
      apply mul_le_mul_of_nonneg_right _ hv; gcongr; simpa only [pow_one] using pow_le_pow_right₀ hz hk
    · unfold currency; rw [←Real.exp_sum]
      have hy:= Ac.cover M b (spark_ac M M hM.1 (fun _ _ _ _ h=> h)); apply Real.exp_monotone; rw [← mul_sum,← Nat.cast_sum]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy) hs
    · exact (Real.exp_pos _).le
    exact prod_nonneg fun k _=> H.2.2.2.2.1 _
  next=> exact hf.1 _

end YM.QCD.Cove
