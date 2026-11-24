import YM.Alum.Beam
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c:Side}
open Chess Cells Romance Massive.Lyre.Array Plum Patria
variable (T:Tiling n)(x y y':Cover)(u v:T.Cell)
-- nearby *negative* displacement ALWAYS rounding down( move positive to y). enough within 2*d length. parity matching.Per.Support.Any α.
variable (X Y:Cover → Stud n 6)
variable (R:Regulator n 6)(hK:Smoke T R)(hs:0<R.Z)(W:ℝ)(ho:0 ≤ W)(k b d:ℕ)(ht:0 < b)(hd:d ≤ b)
variable (hX:FlowsP T R u k X W)(hY:FlowsP T R v k Y W)
variable (δ:Axis →ℕ)(hδ:∀ i,δ i ≤d)
variable (hh:∀ i:Axis,y i=y' i+2*δ i)
local notation "F" y:arg=> valueH R (X x* Y y)
variable (hx:wrap n x∈ T.margin u (4*b+1+k))(hy:wrap n y'∈ T.margin v ((2*d+1)+(4*b+1+k)))
include hK hs hX hY ho hδ hh hx hy ht hd
lemma waves (hv:∀ a:Axis,u∈ T.minusCells v a)(hw:∀ a:Axis,v∈ T.plusCells v a): ‖valueH R (X x * Y y)-valueH R (X x* Y y')‖ ≤ 4*(d*(4*W^2/(b:ℝ))) :=by
       let z(s:Finset Axis) : Cover:= fun a=> if a∈s then y a else y' a
       have hz(s:Finset Axis): wrap n (z s)∈ T.margin v (4*b+1+k):=by
            have he(k:Cover): k=y'+(k-y'):=by abel
            rw [he (z s)]; apply shifted T v hy; intro i; unfold z; simp only [Pi.sub_apply]; split; · rw [hh i]; have hv:= hδ i; omega
            simp
       let P:= 4*W^2/(b:ℝ); have hp:0 ≤ P:=by positivity
       have he(s:Finset Axis):‖F (z s)- F y'‖ ≤ s.card*(d*P):=by
            induction s using Finset.induction_on with
            | empty=>simp only [z,notMem_empty,↓reduceIte]; simp
            | insert a s ha ih=>
              have h:z (insert a s)= z s+ (2*δ a) • step a:=by
                    funext i; by_cases e:i=a; · subst i; simpa [z,ha] using hh a -- hh needed explicitly
                    simp [z,e]
              rw [h,card_insert_of_notMem ha]; have H:= pairFlow T a x (z s) u v b k hx (hz s) X Y R hK hs W ho hX hY (hv a) (hw a) ht (δ a) ((hδ a).trans hd); apply (norm_sub_le_norm_sub_add_norm_sub _ (F (z s)) _).trans; apply (add_le_add H ih).trans; push_cast; rw [add_mul,one_mul, add_comm]; exact add_le_add_right (mul_le_mul_of_nonneg_right (show (↑(δ a):ℝ) ≤ (d:ℝ) from by exact_mod_cast hδ a) hp) _ -- expected add left direction
       have ht:=he univ; rw [show z univ=y from funext fun i=>by simp [z], Finset.card_univ] at ht; simpa using ht
omit hK hs hX hY ho hδ hh hx hy ht hd
-- rounding down stride parity. O(length ratio ℓN). allow within one period odd.
lemma reach_b (hm:Odd d) (y:ℤ): ∃ x:ℤ, ∃ a:ℕ,a ≤d∧ y=d*x+ 2*a:=by
     -- if remainder even choose floor, else floor-1
     let q:= y/(d:ℤ); let v:= y%(d:ℤ); have hd:0<d:=hm.pos; have hv:0 ≤v:= Int.emod_nonneg _ (by exact_mod_cast hd.ne'); have ht:v < d:= Int.emod_lt_of_pos _ (by exact_mod_cast hd); have hT:y=d*q+v:= (Int.mul_ediv_add_emod y _).symm; obtain ⟨w,h⟩:=hm
     by_cases he:v%2=0; · exact ⟨q,(v/2).toNat,by omega,by omega⟩
     refine ⟨q-1,((v+d)/2).toNat,by omega,?_⟩; rw[mul_sub,mul_one]; omega
lemma near_c (h:Odd d):∃ x:Cover,∃ a:Axis→ ℕ,(∀ i,a i ≤d) ∧ ∀ i,y i=(d • x) i+2*a i:=by -- include h accidentally from above. remove
    choose x t h h' using fun i:Axis=>reach_b d h (y i); exact ⟨x,t,h,fun i=>by have hh:= h' i; simpa using hh⟩ -- omega simp
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.waves
#print axioms YM.Massive.Lyre.Goblet.near_c
