import YM.Heron.Mage
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Arise.Range
open Maxwell.Free (fromCenter)
open Finset
section
variable {β γ R S : Type*} [AddCommGroup R] [Module ℂ R] [AddCommGroup S] [Module ℂ S]
noncomputable def slips (u:List β)(f:β→ List β→ R) := ∑ i:Fin u.length, (-1:ℂ)^i.val • f (u.get i) (u.eraseIdx i.val)
lemma slips_cons(a:β)(u:List β)(f:β→ List β→R): slips (a::u) f=f a u - slips u (fun b v=> f b (a::v)):=by
    let V(i:Fin (u.length+1)):= (-1:ℂ)^i.val • f ((a::u).get i) ((a::u).eraseIdx i.val); change (∑ i:Fin (u.length+1),V i)=_; rw[Fin.sum_univ_succ]; unfold V; change ((-1:ℂ)^0 • f a u)+ ∑ i:Fin u.length, (-1:ℂ)^(i.val+1) • f (u.get i) (a::(u.eraseIdx i.val))= _; simp only [pow_succ',pow_zero,neg_one_mul,one_smul,neg_smul,slips,Finset.sum_neg_distrib]; exact (sub_eq_add_neg ..).symm
lemma slips_nil(f:β→ List β→ R):slips [] f=0:=by unfold slips; simp
lemma slips_zero (u:List β) :slips u (fun _ _=>(0:R))=0:=by simp [slips]
lemma slips_map(h:β→γ)(u:List β)(f:γ→List γ→R): slips (u.map h) f=slips u (fun a b=>f (h a) (b.map h)):=by
   induction u generalizing f with|nil=> rw [List.map_nil,slips_nil,slips_nil]| cons a u ih=> rw [List.map_cons,slips_cons, slips_cons,ih]; rfl
lemma slips_twice(u:List β)(f:β→β→List β→R): slips u (fun a v=> slips v (fun b w=>f a b w))= -slips u (fun b v=> slips v (fun a w=> f a b w)):=by
   induction u generalizing f with
   | nil=> simp [slips_nil]
   | cons a u ih=>
       simp_rw [slips_cons]; have he:= ih (fun a' b w=>f a' b (a::w)); unfold slips at *; simp_rw [smul_sub, sum_sub_distrib,he]; abel
lemma slips_append (u v:List β)(f:β→List β→R): slips (u++v) f=slips u (fun x p=> f x (p++v))+ (-1:ℂ)^u.length • slips v (fun x p=> f x (u++p)):=by
    induction u generalizing f with
    | nil => simp
                [slips_nil]
    | cons a u ih=> rw [List.cons_append, slips_cons, slips_cons, ih]; simp only [List.length_cons,pow_succ',neg_one_mul,neg_smul]; abel -- cons list simpl
lemma from_slip (u:List β)(f:β→List β→R)(L:R→ₗ[ℂ] S): L (slips u f)=slips u (fun b p=> L (f b p)):=by unfold slips; simp only[map_sum,map_smul]
end
variable {A B:Type}[Fintype A][Fintype B](Q:Matrix A A ℂ)
lemma slipH (v:Seed A)(u:List (Seed A)) : lease Q (line v*pwn u) = slips u (fun z t=>(unionB Q v z) • lease Q (pwn t)):=by rw [veil]; unfold slips; simp_rw [smul_eq_mul,mul_assoc]
-- PF on backup lists.Lay
lemma spin_pulls {I:Type}(r:I→Seed A)(R:List I)(p q:Seed A)(h: unionB Q p q=0): lease Q (line p*(line q* pwn (R.map r)))= -slips R (fun a v=> slips v (fun b u=> unionB Q p (r a) * unionB Q q (r b)*lease Q (pwn (u.map r)))):=by
    change lease Q (line p*pwn (q::R.map r))=_; rw [slipH,slips_cons,h,zero_smul,zero_sub,slips_map]; refine congr_arg Neg.neg (?_); unfold slips; apply sum_congr rfl; intro j _; dsimp only; apply congr_arg (_ • ·); -- may projection concret.C.
    change (unionB Q p (r _) • (lease Q (line q *pwn _)))=_; rw [slipH,slips_map]; unfold slips; simp only[smul_eq_mul,Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
end YM.Heron
#print axioms YM.Heron.slips_twice
#print axioms YM.Heron.spin_pulls
