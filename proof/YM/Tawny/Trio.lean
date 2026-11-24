import YM.Tawny.Fly
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Carnal
variable (i j k l:Axis)(s:Signed)(w:EuPin)(hw:w.Lifts s)
-- triple rank.R signs
noncomputable def trio (i j k:Axis): Spike:= if i=j∨j=k∨k=i then 0 else gamma i*gamma j*gamma k
lemma trio_c : truck (trio i j k)=trio i j k:=by unfold trio; split <;> rename_i h; exact truck_blank; push Not at h; exact truck_triple i j k h.1 h.2.2 h.2.1.symm
include hw
lemma trio_t : conjug w (trio i j k)=(((signT s i:ℂ)*(signT s j:ℂ))*(signT s k:ℂ)) • trio (s.perm i) (s.perm j) (s.perm k):=by unfold trio; simp only[s.perm.injective.eq_iff]; split; simp [conjug]; rename_i h; rw [L_up,L_up,E_sigma s w hw,E_sigma s w hw, E_sigma s w hw]; simp only [Matrix.smul_mul, Matrix.mul_smul,smul_smul]; apply congr_arg (· • _); ring
omit hw
lemma zeroS (p q:Multi d)(h:spinWeight p+spinWeight q ≤ d): solstice a 0 p q h=0:=Subtype.ext (by change bilinear _ _ _ _ _= (0:Pol d); simp [bilinear])
lemma trio_adj : trio i j k= -trio i k j:=by
    by_cases h:i=j∨j=k∨k=i; · unfold trio; rw[if_pos h,if_pos (by grind), neg_zero]
    unfold trio; rw[if_neg h,if_neg (by grind)]; push Not at h; rw [mul_assoc,mul_assoc,clifford h.2.1, mul_neg]
lemma trio_1 : trio i j k= -trio j i k:=by
    by_cases h:i=j∨j=k∨k=i; · unfold trio; rw[if_pos h,if_pos (by grind),neg_zero] -- grind fails sym
    unfold trio; rw[if_neg h,if_neg (by grind)]; push Not at h; rw [clifford h.1,neg_mul]
local notation "P"=>RawTensor (-1) 8
local notation "L" i:arg=> UV.first i
local notation "U"=> (0:Multi 6)
noncomputable def triple(a:Flavor 6)(i j k:Axis):Label 8:= mixed a (trio i j k) 0 (L i) (by rw[cost_root,juicy])
lemma trout: (triple a i j k).val= bilinear a a (trio i j k) 0 (L i)+bilinear a a (trio i j k) (L i) 0:=by unfold triple mixed; rw [trio_c]; rfl
include hw
lemma trio_l : pinAct w ((triple a i j k).val)= ((signT s j:ℂ)*(signT s k:ℂ)) • (triple a (s.perm i) (s.perm j) (s.perm k)).val:=by
     have he:= trio_t i j k s w hw; have ht:= paidM a _ 0 (L i) (by rw [cost_root,juicy]) s w hw _ _ he (by rw [trio_c,trio_c]; exact he); simp only [marked_root,one_mul,vital,hem_ground,hem_first] at ht
     rw[mul_assoc (signT s i:ℂ),←mul_assoc (signT s i:ℂ),← Complex.ofReal_mul (signT s i), UV.sign_sq,Complex.ofReal_one,one_mul] at ht; exact ht
omit hw
lemma trise: triple a i k j= - triple a i j k:=by unfold triple mixed; rw[trio_c,trio_c, trio_adj i k, push_neg,push_neg]; apply Eq.symm; exact neg_add (solstice a _ _ _ _) (solstice a _ _ _ _) --]
noncomputable def arcS (a: Flavor 6):P := stoke (fun p=>∑ i:Axis,triple a i p.1 p.2) (-1) (by intro i j; apply Submodule.sum_mem; intro k _; exact munity ..) (by intro s w hp i j; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum,trio_l a _ _ _ s w hp, ← smul_sum]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun k=>(triple a k (s.perm i) (s.perm j)).val))) (by intro i j; rw [smul_sum]; apply sum_congr rfl; intro k _; exact (trise a k i j).trans (neg_one_smul ℂ (triple a k i j)).symm)
noncomputable def gamma6(a:Flavor 6)(i j k:Axis): Label 6:= solstice a (trio i j k) U U (by rw [cost_root])
end Carnal
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Carnal.arcS
