import YM.QCD.Jets.Living
import YM.QCD.Fork.Base
/-! # ship bills and terminal geometry -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε α β t:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

lemma terra_zero (s:Support f)(b:ℕ)(F:ℕ) (h:s=∅):terra P F b x y (.inl s)=0∧terra P F b x y (.inr s)=0:=by
    have hQ p (z):P.Y p z s=0:=by_contra fun H=>by have he := ((P.X0.crop p z s).2.1 H).1; simp only [h,notMem_empty] at he
    have hP p (z): P.W p z s=0:=by_contra fun H=> by have he:= ((P.Z0.crop p z s).2.1 H).1; rw [h] at he; exact Finset.notMem_empty _ he
    have hH p(z):P.B0 p z s=0:=by_contra fun H=> by have he:= ((P.V0.crop p z s).2.1 H).1; simp only [h,notMem_empty] at he
    simp only [terra,sumS,sumX, Sum.elim_inl,Sum.elim_inr,hQ,hP,hH, add_zero,ite_self,sum_const_zero,mul_zero,zero_mul, and_self]

lemma foam_at (X:Site f→Site c→Bundle)(Y:Site c→Site f→ Bundle)(x:A)(V: Site c→ℝ)(hy:0≤ V)(K:ℝ)(ht:∑ j,V j≤K):
    ((∀ j,‖X x.1.1 j‖≤V j)→(∑ k:Keys c F, ‖foamB X Y (.inl x) k‖)≤ fingers F*K)∧
      ((∀ j,‖Y j x.1.1‖≤V j)→ (∑ k: Keys c F,‖foamB X Y (.inr x) k‖)≤fingers F*K):=by
    have hv : (∑ j:B, V j.1.1)≤fingers F*K:=(rowsSum c F V).trans_le (mul_le_mul_of_nonneg_left ht (by unfold fingers; positivity))
    constructor
    · intro h; rw [Fintype.sum_sum_type]; simp only [foamLR,norm_zero,sum_const_zero,add_zero]; apply le_trans ?_ hv; refine sum_le_sum fun j _=>?_ ; rw [foamI]; split; · exact (Cost.north ..).trans (h _)
      rw [norm_zero]; exact hy _
    intro h; rw [Fintype.sum_sum_type]; simp only [foamRL,norm_zero,sum_const_zero,zero_add]; apply le_trans ?_ hv; refine sum_le_sum fun j _=>?_ ; rw [foamR]; split; · exact (Cost.north ..).trans (h _)
    rw [norm_zero]; exact hy _
lemma town_cost (b F:ℕ)(K:ℝ) (hs: Fork.Sea G h b δ K q t P.Z P.V 0) (U:Grid f) (i: Keys f F):
   (Healthy t (halo (b+1) {locationP i}) U→ ∑ j, ‖(P.equip F b).shortP U i j‖ ≤ fingers F*K)∧∑ j, ‖(P.equip F b).shortP U i j‖≤ fingers F*q := by
    let X x j:=spoon P.Z x b x j (settled U); let Y j x:=spoon P.V x b j x (settled U); have hm:(P.equip F b).shortP U=foamB X Y:=rfl; rw [hm]
    cases i
    next i=>
      obtain ⟨⟨V,hV,hv,hk⟩,-,Q,hQ,hq,HH⟩:= (hs i.1.1).1; simp only [Fork.meets,pow_zero,one_mul] at hv
      exact ⟨fun he=> (foam_at X Y i V hV K hv).1 (hk U he), (foam_at X Y i Q hQ q hq).1 (HH _ (citizenship f P.positive U))⟩
    next i=>
      obtain ⟨⟨V,hV,hv,hk⟩,-,Q,hQ,hq,HH⟩:= (hs i.1.1).2; simp only [Fork.meets,pow_zero,one_mul] at hv
      exact ⟨fun he=> (foam_at X Y i V hV K hv).2 (hk U he), (foam_at X Y i Q hQ q hq).2 (HH _ (citizenship f P.positive U))⟩
lemma paysAll (F b r mL:ℕ) (K C z z':ℝ)(W:Tr f→Support c) (hs: ∀ u₀, W u₀⊆ enlargement S mL b (roomK u₀))(hx:0<x)(hy:0<y)(hb:0<b)(he:l≤2*b)(hh:η≤u)(hd:reserve η w (conversion S mL) ξ)(he':reserve u w (conversion S mL) ε)
   (H:∀ i,(roomK i).image (S).parent ⊆ W i)(hv: Fork.Sea G h r δ K q t P.Z P.V 0)(hc:1≤C)(hp:y*fingers F*K≤x)(hf:y*fingers F*q≤C*x)(ht:splitCost F r mL b l G.L q u η w ε ξ x y≤1):
   let μ i:= Real.exp 1*terra P F r x y i
   Peak (P.equip F r) t x y C μ ∧ Ac.Hit W b μ w (Real.exp 1*splitCost F r mL b l G.L q u η w ε ξ x y):=by
    intro μ
    have hm:=P.terrace F r mL b W hs hx hy hb he hh hd he'
    refine ⟨⟨hx,hy,hc,fun i U=> ?_,fun i U he=> (mul_le_mul_of_nonneg_left ((town_cost P r F K hv U i).1 he) hy.le).trans (by rwa [← mul_assoc]), fun i U=> (mul_le_mul_of_nonneg_left (town_cost P r F K hv U i).2 hy.le).trans (by rwa [← mul_assoc])⟩, heights_factor _ _ _ _ hm (fun _=>rfl) (Real.exp_pos _).le⟩
    have hB:= licence P (F:=F) _ (citizenship f P.positive U) hx hy r i; apply hB.twice
    by_cases he : (W i).Nonempty; swap
    · have hQ:roomK i=∅:=by apply not_nonempty_iff_eq_empty.mp; intro ht; exact he ((ht.image _).mono (H _))
      cases i
      next i=> exact (terra_zero P i r F hQ).1.trans_le zero_le_one
      next i=> exact (terra_zero P i r F hQ).2.trans_le zero_le_one
    obtain ⟨j,hj⟩:=he; apply le_trans _ ht; have hz:= budget_sum (hm j) {i}; rw [sum_singleton,if_pos hj] at hz; exact (le_mul_of_one_le_right hB.nn (Real.one_le_exp (mul_nonneg he'.1 (by positivity)))).trans hz
end YM.QCD.Jets.Sun
