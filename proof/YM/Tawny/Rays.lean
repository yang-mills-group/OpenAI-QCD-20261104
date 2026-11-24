import YM.Tawny.Temp
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
variable (i j k l:Axis)
namespace Rays
local notation "D"=> Multi 10
local notation "U"=> (0:D)
-- variable (p q:Multi 10)(s:Signed)
open Finset
noncomputable def leadR (i:Axis):D:= ⟨fun k:Axis=> if i=k then 1 else 0,by unfold order; simp [apply_ite Fin.val]⟩
private lemma pots : power (leadR i) k = if i=k then 1 else 0:=by by_cases h:i=k <;> simp [power,leadR,h]
private lemma cap (w:Axis)(v:D)(h:order (power v)<10): order (Function.update (power v) w (power v w + 1))=order (power v)+1:=by
     let f:= power v; have he:Function.update (power v) w (power v w+1)=fun x=>f x+(if w=x then 1 else 0):=by
          funext i; by_cases hi:i=w; subst i; simp [f]
          simp [hi, Ne.symm hi,f]
     unfold order; rw [he,sum_add_distrib]; simp only [sum_ite_eq,mem_univ,if_true]; rfl
lemma l_order : order (power (leadR i))=1:=by unfold order; simp_rw [pots]; simp
noncomputable def ηR (i j:Axis):D:=
   let f:= Function.update (power (leadR i)) j ((power (leadR i)) j + 1); ⟨fun k => ⟨f k,by
                 unfold f; by_cases hi:k=j; subst k; rw [Function.update_self,pots]; split_ifs <;> decide
                 rw [Function.update_of_ne hi,pots]; split_ifs <;> decide⟩,by change order f ≤ _; unfold f; rw[cap j _ (by rw [l_order]; omega),l_order]; decide⟩ -- rewrite indentation
lemma gradeL : spinWeight (leadR i)=5:=by rw[spinWeight,l_order]
lemma gradeV: spinWeight U=3:=cost_root _
private lemma flex : power (ηR i j) k= power (leadR i) k + power (leadR j) k:=by
      change Function.update (power (leadR i)) j _ k=_; rw [pots j k]; split_ifs with hx; subst k; rw [Function.update_self]
      rw [Function.update_of_ne (Ne.symm hx),add_zero]
lemma gradeH : spinWeight (ηR i j)=7:=by
      rw[spinWeight,show power (ηR i j)=_ from (funext (flex i j))]; rw [show order _=order (power (leadR i))+order (power (leadR j)) from Finset.sum_add_distrib]; rw[l_order,l_order];
lemma add_next (j:Axis) : AtNext i (leadR j) (ηR j i):=rfl
lemma add_zeroL : AtNext i U (leadR i):=by
      unfold AtNext; funext j; by_cases hi:i=j; subst j; rw[Function.update_self,pots,if_pos rfl]; rfl
      rw [Function.update_of_ne (Ne.symm hi),pots,if_neg hi]; rfl
lemma via_eq (v w : Multi d)(h: power v=power w): v=w:=Subtype.ext (funext fun i=>Fin.ext (congr_fun h i))
lemma lead_in : Injective leadR:=by intro i j h; have hp:power (leadR i) i=power (leadR j) i:= congr_arg (fun k=> power k i) h; rw[pots,pots,if_pos rfl] at hp; contrapose! hp; rw [if_neg hp.symm]; decide
lemma H_swap : ηR i j=ηR j i:=via_eq _ _ (funext fun k=>by rw [flex,flex,add_comm])
lemma H_unique (h:ηR i j=ηR k l): i=k ∧ j=l ∨ i=l ∧ j=k:=by
     have he(a): power (leadR i) a+power (leadR j) a= power (leadR k) a+power (leadR l) a:=by rw[← flex,← flex,h]
     have ht :i=k ∨ i=l:=by
          by_contra! hv; obtain ⟨h,H⟩:=hv; have hx:=he i; simp [pots,h,H,h.symm,H.symm] at hx -- result
     have hr(i j k:Axis)(h: ηR i j=ηR i k): j=k:=lead_in (via_eq _ _ (funext fun l=>Nat.add_left_cancel  ((flex i j l).symm.trans ((congr_arg (fun p=>power p l) h).trans (flex i k l)))))
     rcases ht with rfl|rfl; · exact Or.inl ⟨rfl,hr _ _ _ h⟩
     rw [H_swap k i] at h; exact Or.inr ⟨rfl,hr _ _ _ h⟩
variable (s:Signed)
lemma hem_lead : hem s (leadR i)=leadR (s.perm i):=via_eq _ _ (funext fun j=>by simp only [hemming,pots,pots,s.perm.eq_symm_apply])
lemma hem_η : hem s (ηR i j)=ηR (s.perm i) (s.perm j):=by
    apply via_eq; funext k; rw [hemming,flex,flex,←hem_lead,←hem_lead,hemming,hemming]
lemma markedL : marked s (leadR i)=signT s i:=by unfold marked; simp_rw [pots i]; simp
lemma markedH : marked s (ηR i j)=signT s i*signT s j:= by unfold marked; simp_rw[flex, pow_add]; rw[prod_mul_distrib]; exact congr_arg₂ (·*·) (markedL i s) (markedL j s)
variable (p q:Multi 10)(s:Signed)
-- exhaustive shapes
private lemma baseZ(h:order (power p)=1):∃ i, p= leadR i:=by
     obtain ⟨i,hi⟩ : ∃ i,power p i≠0:= by by_contra! hx; unfold order at h; simp [hx] at h
     have he:order (power p) = power p i+∑ j∈(univ.erase i),power p j:= (add_sum_erase _ _ (mem_univ i)).symm
     have hp: power p i=1:=by omega
     have hz(j:Axis)(ht:j≠i): power p j=0:=by
          have hq:=Finset.single_le_sum (f:=power p) (fun _ _=>Nat.zero_le _) (mem_erase.mpr ⟨ht,mem_univ j⟩); omega
     refine ⟨i, via_eq _ _ ?_⟩; funext j; rw[pots]; by_cases hi:i=j; subst j; rw[if_pos rfl,hp]; rw [if_neg hi, hz j (Ne.symm hi)]
private lemma baseL (h:order (power p)=2): ∃ i j,p=ηR i j:=by
    let f:=power p; obtain ⟨i,hi⟩:∃ i,f i ≠ 0:=by by_contra! he; change order f=2 at h; simp [order,he] at h
    let g:= Function.update f i (f i-1); have he:g + power (leadR i)= f:=by
           funext x; simp only [Pi.add_apply,pots,g]; by_cases hx:i=x; subst x; rw[if_pos rfl,update_self]; omega
           rw[if_neg hx, Function.update_of_ne (Ne.symm hx),add_zero]
    have hp:order g=1:=by have hx :order (g+power (leadR i))=2:=he ▸ h; rw[show order (g+power _)= _ + _ from (Finset.sum_add_distrib : (∑ k:Axis,(g k+power (leadR i) k))= order g+order (power (leadR i)))] at hx; change order g + order (power (leadR i)) =2 at hx; rw [l_order] at hx; omega
    have hP(x): g x ≤ 1:=by rw[← hp]; exact single_le_sum (f:=g) (fun _ _=> Nat.zero_le _) (mem_univ x)
    let q:D:=⟨fun x=>⟨g x,(hP x).trans_lt (by decide)⟩, show order g≤10 from hp ▸ (by decide)⟩
    obtain ⟨j,hj⟩:= baseZ q hp; have ht:g=power (leadR j):= show power q=_ from congr_arg power hj
    refine ⟨j,i,via_eq _ _ ?_⟩; funext k; rw[flex,← ht]; exact congr_fun he.symm k
lemma sky(hp:spinWeight p+spinWeight q≤10):
      p=U∧ (q=U∨(∃ i,q=leadR i)∨(∃ i j,q=ηR i j))∨ q=U∧ ((∃ i,p=leadR i)∨(∃ i j,p=ηR i j)) ∨∃ i j,p=leadR i∧q=leadR j:=by
    let P:= order (power p); let Q:=order (power q); have hP:P=0↔p=0:=ground_iff p; have hQ:Q=0↔q=0:=ground_iff q
    change 3+2*P+(3+2*Q) ≤ 10 at hp
    by_cases hv:P=0
    · left; refine ⟨hP.mp hv,?_⟩; by_cases hx:Q=0; · exact Or.inl (hQ.mp hx)
      right; rcases (show Q=1∨Q=2 from by omega) with h|h; exact Or.inl (baseZ _ h); exact Or.inr (baseL _ h)
    right; by_cases hx:Q=0
    · left; refine ⟨hQ.mp hx,?_⟩; rcases (show P=1∨P=2 from by omega) with h|h; exact Or.inl (baseZ _ h); exact Or.inr (baseL _ h)
    right; obtain ⟨i,t⟩:=baseZ p (show P=1 from by omega); obtain ⟨j,v⟩:= baseZ q (show Q=1 from by omega); exact ⟨i,j,t,v⟩
end Rays
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Rays.sky
