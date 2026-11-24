import YM.QCD.Jets.Aid
import YM.Push.ABSOLUTE_SUMS.Labels
/-! # rent earned by TRUE support -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
lemma long_hits (r mL b:ℕ)(W:Support f→Support c)(he:∀ x:Support f,W x⊆ enlargement S mL b x)(hb:0<b)(hv:l≤ 2*b)(hh:η≤u)(hd: reserve η w (conversion S mL) ε):
    Ac.Hit W b (P.sumS r) w (payment (G.L.val^4) (extentCost mL b) 0 ε 1 (Real.exp (-(u-η)*fossil r l)*2*q) w (preCost mL)) := by
   let X (x:Site f)(s:Support f):=∑ i:Site c,if s∈satZip x r then P.W x i s + P.B0 i x s else 0
   have hg x s:0 ≤X x s:=sum_nonneg fun i _=> by split; exact add_nonneg (P.Z0.crop x i s).1 (P.V0.crop i x s).1; exact le_rfl
   refine body_hits S mL b l X W he hg (fun x s h=> ?_) hd hb hv _ ?_
   · contrapose! h; apply sum_eq_zero; intro i _; split; · rw [show P.W x i s=0 from by_contra (fun he=> h (((P.Z0.crop x i s).2.1 he).1)), show P.B0 i x s=0 from by_contra fun he=> h (((P.V0.crop i x s).2.1 he).2),zero_add]
     rfl
   intro i
   unfold X; simp_rw [mul_sum]; rw [sum_comm]
   let E:= Real.exp (-(u-η)*fossil r l); let V:=satZip i r
   calc _ ≤ ∑ j:Site c, (E*duel P.W i j u l+E*duel P.B0 j i u l):=by
          apply sum_le_sum; intro k _; have hf:=worthZ P.Z0 i k i η r (Or.inl rfl) hh; have ht:=worthZ P.V0 k i i η r (Or.inr rfl) hh; apply le_trans _ (add_le_add hf ht); rw [← sum_add_distrib]; apply le_of_eq
          rw [← sum_subset (subset_univ (satZip i r)) (fun j _ hj=>by rw [if_neg hj,mul_zero])]; apply sum_congr rfl; intro j hj; rw [if_pos hj, mul_add]
        _ ≤ _:=by
          rw [sum_add_distrib,← mul_sum,←mul_sum]; exact (add_le_add (mul_le_mul_of_nonneg_left (P.Z0.spends i) (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left (P.V0.dues i) (Real.exp_pos _).le)).trans_eq (by ring)

-- hit multiply
lemma heights_factor {I:Type*}(C:ℝ)(Y:I→Support c)(Z:I→ℝ)(T : I→ℝ)(hp: Ac.Hit Y b Z a q)(h : ∀ i,T i=C* Z i)(hc:0≤ C): Ac.Hit Y b T a (C*q):=by
  intro i; convert budget_scale hc (hp i) using 1; funext j; simp_rw [h]; split<;> simp [mul_assoc]

def rem (L:Side) (mL b:ℕ) (w κ ε:ℝ):=payment (L.val^4) (extentCost mL b) 0 ε 1 κ w (preCost mL)
def splitCost (F r mL b l :ℕ)(L : Side) (q u η w ε ξ x y:ℝ):ℝ:=fingers F^2*x⁻¹^2 * rem L mL b w q ε+ (fingers F^2*(y*x⁻¹))*rem L mL b w (Real.exp (-(u-η)*fossil r l)*2*q) ξ
lemma terrace (F r mL b:ℕ)(W: Tr f→Support c) (he:∀ z,W z⊆enlargement S mL b (roomK z))(hx:0<x)(hy:0<y)(hb:0<b)(hv:l≤2*b)(hh:η≤u)(hd:reserve η w (conversion S mL) ξ)(hk:reserve u w (conversion S mL) ε):
   Ac.Hit W b (P.terra F r x y) w (splitCost F r mL b l G.L q u η w ε ξ x y) := by
   let Y z:=W (Sum.inl z); let V z:=W (Sum.inr z)
   have heY : Ac.Hit Y b (fun i=> P.terra F r x y (.inl i)) w (fingers F^2*x⁻¹^2*rem G.L mL b w q ε):= heights_factor _ _ _ _ (inverse_hits P r mL b _ (fun i=> he (.inl i)) hb hv hk) (by intro i; simp only [terra,Sum.elim_inl]; ring) (by positivity)
   have heV : Ac.Hit V b (fun i=> P.terra F r x y (.inr i)) w ((fingers F^2*(y*x⁻¹))*rem G.L mL b w (Real.exp (-(u-η)*fossil r l)*2*q) ξ):= heights_factor _ _ _ _ (long_hits P r mL b _ (fun i=>he (.inr i)) hb hv hh hd) (by intro i; simp only [terra,Sum.elim_inr]; ring) (by positivity)
   have hm:=Labels.together _ _ _ heY heV
   have hh : Sum.elim Y V = W :=funext (fun i=> by cases i <;> rfl)
   rw [hh, show Sum.elim (fun i=> P.terra F r x y (.inl i)) (fun i=> P.terra F r x y (.inr i))= P.terra F r x y from funext (fun i=>by cases i <;> rfl)] at hm
   exact hm
end YM.QCD.Jets.Sun
