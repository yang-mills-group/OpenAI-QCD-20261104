import YM.QCD.Jets.Box
import YM.Push.ABSOLUTE_SUMS.Footprint
/-! # support anchored per pair; convert to any enlarged pack along with row anchors. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y m ε:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

-- anchors split pair contributions over hits. don't need any mark in padding; those Y may =0
lemma body_hits {I:Side}(p:Ratio I f) (L:ℕ)(r l:ℕ) (X : Site f→Support f→ℝ) (W: Support f→Support I)(ht:∀ x, W x ⊆ enlargement p L r x)(h:∀ x s,0≤X x s)(he: ∀ x s,X x s≠0 → x∈s)(hh:reserve v y (conversion p L) ε)(hz:0<r)(hv:l≤2*r)(γ:ℝ) (hx:∀ x,∑ s: Support f,rent v l s*X x s≤γ) : Ac.Hit W r (fun i=>∑ x,X x i) y (payment (p.count.val^4) (extentCost L r) 0 ε 1 γ y (preCost L)):=by
  let P:=Site f ×Support f; let T: Finset P:= univ.filter fun q=>q.1∈q.2
  let u (i:↥T):=i.val; let a i:=(u i).1; let XW i:=X (u i).1 (u i).2; let z i:=(u i).2
  have hu : Anchored a XW (fun i=>coverNumber l (z i)) v γ:=by
    intro x
    apply budget_of_sum _ ; swap; · intro i; split; exact mul_nonneg (h _ _) (Real.exp_pos _).le; exact le_rfl
    intro s
    let F:=s.filter fun i=> a i=x; let Q i:= X x i*Real.exp (v*coverNumber l i)
    rw [← sum_filter]; have hs: Set.InjOn z (F:Set _):=by
       intro i hi j hj H; exact Subtype.ext (Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) H)
    calc
     _ = ∑ i∈F.image z,Q i:=by rw [sum_image hs]; exact sum_congr rfl (fun i hi=>by unfold XW; rw [show (u i).1=x from (mem_filter.mp hi).2])
     _ ≤ ∑ i:Support f,rent v l i * X x i:= by
       apply le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ (F.image z)) (fun i _ _=> mul_nonneg (h x i) (Real.exp_pos _).le)); exact le_of_eq (sum_congr rfl fun i _=> mul_comm ..)
     _ ≤ γ:= hx x
  have hy:= coarsen p L r l z a (fun i=> (mem_filter.mp i.property).2) XW (fun i=>h _ _) hu (W ∘ z) (fun i=> ht _) hz hv zero_le_one hh 0 XW (fun i=>h _ _) (fun i=>by simp)
  intro i; let Z s:= if i∈W s then (∑ x,X x s) * Real.exp (y*coverNumber r (W s)) else 0
  change SumBudget Z _; refine budget_of_sum (fun a=> by unfold Z; split; exact mul_nonneg (sum_nonneg fun x _=> h _ _) (Real.exp_pos _).le; exact le_rfl) ?_
  intro s
  have hr:= budget_sum (hy i) univ
  refine le_trans ?_ hr; let D j:= if i∈ (W ∘ z) j then XW j * Real.exp (y*coverNumber r (W (z j))) else 0; have hp j : 0≤ D j:=by unfold D; split; exact mul_nonneg (h _ _) (Real.exp_pos _).le; exact le_rfl
  calc
   _ ≤ ∑ j:Support f,Z j:=sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun j _ _=>by unfold Z; split; exact mul_nonneg (sum_nonneg fun x _=>h _ _) (Real.exp_pos _).le; exact le_rfl)
   _ = ∑ j:↥T,D j:=by
    symm; change _ = ∑ b:Support f,if i∈W b then _ else _
    let E (i₀:P):= if i∈W i₀.2 then X i₀.1 i₀.2 * Real.exp (y*coverNumber r (W i₀.2)) else 0
    change ∑ j : ↥T,E j.val=_; rw [Finset.sum_coe_sort,sum_filter]
    rw [Fintype.sum_prod_type,sum_comm]; refine sum_congr rfl fun j _=>?_; unfold E; split_ifs with he' -- risky
    · rw [sum_mul]; refine sum_congr rfl fun k _=>?_ ; split
      · rfl
      next hx=> rw [show X k j=0 from by_contra fun hp=>hx (he _ _ hp),zero_mul]
    · simp
   _ ≤ _:= le_rfl

lemma inverse_hits (r mL b:ℕ)(W:Support f→Support c)(he:∀ x:Support f,W x⊆ enlargement S mL b x)(hb:0<b)(hv:l≤ 2*b)(hd: reserve u y (conversion S mL) ε): Ac.Hit W b P.sumX y (payment (G.L.val^4) (extentCost mL b) 0 ε 1 q y (preCost mL)) := by
   let X (x:Site f) (s:Support f):=∑ i:Site f,P.Y x i s; have hg x s:0 ≤X x s:=sum_nonneg fun i _=> (P.X0.crop x i s).1
   refine body_hits S mL b l X W he hg (fun x s h=> ?_) hd hb hv q ?_
   · contrapose! h; exact sum_eq_zero fun i _=> by_contra (fun he=> h (((P.X0.crop x i s).2.1 he).1))
   intro i; unfold X; simp_rw [mul_sum]; rw [sum_comm]; exact P.X0.spends i
end YM.QCD.Jets.Sun
