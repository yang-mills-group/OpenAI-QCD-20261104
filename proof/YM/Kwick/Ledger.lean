import YM.Kwick.Vault
import YM.Parishes.Sheds
import YM.Tinus.Pace
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT Tawny.Cast.Zinc
open Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
local notation "T"=>Grade
variable (x y:Z)(i:Axis)(s:Grade)(p:Rings 10)(k:Fin 4)(Pt Q:BudgetPoint)(w w' r v A ε C u t:ℝ)
-- unweighted & point-alpha; charges.Normal.Cos. Goal access cost using `weight` primitive
noncomputable def bud (k:Fin 4)(t w:ℝ):ℝ:= t^(tierQ k).2.1*w^(tierQ k).2.2
local notation "W" x:arg=> (fun i:Axis=> x.val i) -- shadow F.S
noncomputable def grunt (p:Rings 10)(i:Axis) : Z→ₗ[ℂ]ℂ:= coord p.val ∘ₗ ((labels 10).subtype ∘ₗ LinearMap.proj i ∘ₗ (RawVec 10).subtype)
lemma read_p : grunt p i (vaultP s x)= if crest p.val=s then grunt p i x else 0:= kind_S ..
lemma other (h:∀ i, crest p.val ≠ tierQ i) : grunt p i x=0:=by
    rw [bill_zero x,map_sum]; unfold bet; rw[Finset.sum_eq_zero]; intro i' _ ; rw [read_p,if_neg (h i')]
noncomputable def stitchQ (p:Rings 10)(t w:ℝ):ℝ:=t^life p.val.1*w^p.val.2.card
lemma bLoom : fare p.val (x.val i).val t w= (stitchQ p t w:ℂ)*grunt p i x:=by unfold fare; rw [rank_fee]; unfold stitchQ; push_cast; rfl
lemma blooms : coord p.val (dimming t w 10 (x.val i)).val= (stitchQ p t w:ℂ)*grunt p i x:=bLoom ..
lemma stitch_up(h:crest p.val=tierQ k) : stitchQ p t w= bud k t w:=by unfold bud; rw [←h]; rfl
-- wealth decomposition.Unnormalized y.
lemma shoot (i:Axis) : let f:=((bet k) x).val i; Sieve.dimming t w 10 f=(bud k t w:ℂ) • f:=by
    intro f; apply Subtype.ext; apply (zBasis 10).repr.injective; ext j; by_cases hh: j∈ chair 10
    · let p:Rings 10:= ⟨j,hh⟩; change coord p.val (widths t w (((bet k x).val i).val))=coord p.val ((bud k t w:ℂ) • (((bet k x).val i).val)); rw[show coord p.val (widths _ _ _)=_ from bLoom (bet k x) i p w t,map_smul,smul_eq_mul]; change (stitchQ p t w:ℂ)*grunt p i (vaultP (tierQ k) x)= _ * grunt p i (vaultP (tierQ k) x); rw [read_p]; split; next h=>rw[stitch_up _ _ _ _ h] -- arg check
      next h=> rw[mul_zero,mul_zero]
    have hv(x:Label 10):coord j x.val=0:=by by_contra h; exact hh (menu x.val ((label_law _).1 x.property).1 _ h)
    exact (hv (dimming t w 10 f)).trans (hv ((bud k t w:ℂ) • f)).symm
noncomputable def wages (i:Axis)(x:Z):ℝ:= ∑ p:Rings 10, ‖grunt p i x‖
noncomputable def stack (k:Fin 4)(t w:ℝ)(x:Z):Z:= (bud k t w:ℂ) • bet k x
lemma worth_cash : wealth (((bet k x).val i).val) t w=wages i (stack k t w x):=by
     refine sum_congr rfl fun p _=>?_ ; refine congr_arg norm (?_ : fare _ _ _ _ = _); rw [bLoom,stack,map_smul,smul_eq_mul,bet,read_p]; split; next h=> rw[stitch_up _ _ _ _ h]
     next h=> rw [mul_zero,mul_zero]
lemma wow(x:Z)(t w:ℝ)(i:Axis): wealth ((x.val i).val) t w=∑ k:Fin 4,wages i (stack k t w x):=by
    simp_rw [← worth_cash]; unfold wealth; rw [Finset.sum_comm (s:=Finset.univ)]; -- chooses RHS?
    refine sum_congr rfl fun p _=>?_ ; simp_rw [show ∀ (k:Fin 4),fare p.val ((bet k x).val i).val t w=if crest p.val=tierQ k then fare p.val (x.val i).val t w else 0 from fun k=>size_ν ..]
    by_cases hp:∃ k,tierQ k=crest p.val
    · obtain ⟨k,h⟩:=hp; have he(i j: Fin 4): tierQ i=tierQ j ↔ i=j:=by decide +revert
      rw [← h]; simp[he,apply_ite norm]
    push Not at hp; rw [bLoom, other _ _ _ (fun j=>Ne.symm (hp j)),mul_zero,norm_zero]; -- rw bLoom both L R? check
    rw[sum_eq_zero]; intro j hj; rw[if_neg (Ne.symm (hp j)),norm_zero]
-- easier toted:p charge weights.M Plan gauge.K. rearrange.
lemma toteQ : toted u (x.val i) Pt w=∑ k:Fin 4,u^(tierQ k).1*wages i (stack k Pt.threshold w x):=by
     simp_rw[← worth_cash]; unfold toted princS wealth; simp_rw [Finset.mul_sum]; rw [sum_comm,sum_comm (s:=Finset.univ) (t:=@Finset.univ (Rings 10) _)]; -- ordering brittle
     apply sum_congr rfl; intro p _; simp_rw [show ∀ j:Jars 10, fare p.val (gradeCut 10 j.val (x.val i)).val Pt.threshold w= if crest p.val=j.val then fare p.val (x.val i).val Pt.threshold w else 0 from fun _=>size_ν .., show ∀ j:Fin 4, fare p.val ((bet j x).val i).val Pt.threshold w=if crest p.val=tierQ j then fare p.val (x.val i).val Pt.threshold w else 0 from fun _=>size_ν ..]; let j:Jars 10:=⟨crest p.val, mem_image_of_mem _ p.property⟩; rw [sum_eq_single j]; swap
     · intro b hb hg; rw[if_neg (fun h=> hg (Subtype.ext h.symm)),norm_zero,mul_zero]
     swap; intro hx; simp at hx
     rw [if_pos (show crest p.val=j.val from rfl)]; by_cases hp:∃ k,tierQ k= crest p.val
     · obtain ⟨k,h⟩:= hp; have hv (b c:Fin 4): tierQ b=tierQ c ↔ b=c:=by decide +revert
       rw[sum_eq_single k]; rw[if_pos h.symm, show weightJ j=(tierQ k).1 from congr_arg Prod.fst h.symm]; intro b hb hg; rw [← h,if_neg (fun h'=>hg ((hv _ _).mp h').symm),norm_zero,mul_zero]; intro h; simp at h
     push Not at hp; rw[bLoom,other _ _ _ (fun i=>Ne.symm (hp i)),mul_zero,norm_zero,mul_zero]; rw [sum_eq_zero]; intro k _; rw [if_neg (Ne.symm (hp k)),norm_zero,mul_zero]
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.shoot
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.wow
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.toteQ
