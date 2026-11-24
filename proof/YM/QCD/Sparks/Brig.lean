import YM.QCD.Sparks.Forecourt

/-! # finite additive plaquette recovery of a closed cover walk -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary
open scoped Topology Matrix BigOperators Classical ContDiff
lemma propels (a:Step)(l:Walk)(x:Cover): ∃ p:List Plaid,p.length ≤ l.length∧ (∀ b ∈ p,Laurent.size b.p.1≤Laurent.size x+l.length+1) ∧ stop x (l++[a])=stop x (a::l) ∧∀ Z:Flux, bill Z x (l++[a])=bill Z x (a::l)+(p.map fun v=> v.beat Z).sum:=by
  induction l generalizing x with
  | nil=> exact ⟨[],le_rfl, by simp,rfl,fun _=>by simp⟩
  | cons d l ih=>
    obtain ⟨p,hp,ht,h₀,H⟩:=ih (x+d.vec)
    have hh : stop x ((d::l)++[a])=stop x (a::d::l):=h₀.trans (by simp only [stop]; rw [add_right_comm x])
    have hv (v)(he:v∈p) : Laurent.size v.p.1 ≤ Laurent.size x+(d::l).length+1:=by
      apply (ht v he).trans; have he := Laurent.size_add x (d.vec (R:=ℤ)); rw [price_vec] at he; rw [List.length_cons]; omega
    have he (Z:Flux): bill Z x ((d::l)++[a]) = bill Z x (a::d::l) + (ash Z x d a + (p.map fun v=>v.beat Z).sum):=by
      rw [List.cons_append, add_bill,H]; simp only [ash,drawer,add_bill]; rw [add_right_comm x]; abel
    by_cases hD : d.dir=a.dir
    · refine ⟨p,(hp.trans (by simp)),hv,hh,fun Z=>?_⟩; rw [he]; simp [ash,strait d a hD]
    obtain ⟨B,hB,hK⟩:=check_all d a hD x
    refine ⟨B::p,by simpa only [List.length_cons] using Nat.add_le_add_right hp 1,fun b hb=> ?_,hh,fun Z=> by rw [he,hK,List.map_cons,List.sum_cons]⟩
    rcases List.mem_cons.mp hb with hb|hb; swap; exact hv b hb
    subst b; apply hB.trans; have hp (a: Bool): a.toNat ≤ 1:= by cases a<;> decide
    rw [List.length_cons]; have :=hp d.neg; have :=hp a.neg; omega
lemma uphill (a : Axis) (l: Walk)(x:Cover)(h : negDir a∉l): x a ≤ stop x l a := by
  induction l generalizing x with
  | nil=> exact le_rfl
  | cons d l ih=>
    have hv : x a≤ (x+d.vec:Cover) a:=by
      rcases d with ⟨d,b⟩
      by_cases he:a=d
      · subst d; cases b
        · simp [Step.vec]
        exact absurd List.mem_cons_self h
      cases b <;> simp [Step.vec,step_apply,he]
    exact hv.trans (ih (x+d.vec) (fun v=> h (List.mem_cons_of_mem _ v)))
lemma downhill (a: Axis)(l:Walk)(x:Cover)(h: posDir a∉l): stop x l a≤x a:=by
  induction l generalizing x with
  | nil => exact le_rfl
  | cons d l ih =>
    apply (ih (x+d.vec) (fun v=>h (List.mem_cons_of_mem _ v))).trans
    rcases d with ⟨d,b⟩; by_cases he:a=d
    · subst d; cases b; · exact absurd List.mem_cons_self h
      simp [Step.vec]
    cases b <;> simp [Step.vec,step_apply,he]
lemma encounter (a : Step)(x:Cover)(l : Walk) (h : stop x (a::l)=x):a.rev∈l:=by
  rcases a with ⟨a,_|_⟩ <;> by_contra hh
  · have H:=uphill a l (x+step a) hh; rw [show stop (x+step a) l=x from h] at H; simp at H
  have H:=downhill a l (x+(-step a)) hh; rw [show stop (x + -step a) l=x from h] at H; simp at H

lemma removal (x: Cover)(w:Walk)(h:stop x w=x): ∃ p:List Plaid,p.length≤ w.length^2 ∧ (∀ b∈p,Laurent.size b.p.1 ≤ Laurent.size x+w.length) ∧∀ Z:Flux, bill Z x w=(p.map fun v=>v.beat Z).sum:=by
  cases w with
  | nil=> exact ⟨[],Nat.zero_le _,by simp,fun _=>rfl⟩
  | cons a w=>
    obtain ⟨l,r,hr⟩:=List.append_of_mem (encounter a x w h)
    have he: x+a.vec+a.rev.vec=x:=by rw [Step.vec_rev]; abel
    subst w
    obtain ⟨P,hP,hC,hV,hQ⟩:=propels a.rev l (x+a.vec)
    have hL: stop x (a::(l++a.rev::r))=stop x (l++r):=by
      rw [stop,show l++a.rev::r=(l++[a.rev])++r by simp, stop_append, hV,stop,he,stop_append]
    obtain ⟨Q,hq,hh,HE⟩:= removal x (l++r) (hL.symm.trans h)
    refine ⟨P++Q,?_,fun b hb=>?_,fun Z=>?_⟩
    · simp only [List.length_append,List.length_cons]; rw [List.length_append] at hq; nlinarith only [hq,hP,Nat.zero_le l.length,Nat.zero_le r.length]
    · have hy:= Laurent.size_add x (a.vec (R:=ℤ)); rw [price_vec] at hy
      rcases List.mem_append.mp hb with h|h
      · apply (hC b h).trans; simp only [List.length_cons,List.length_append]; omega
      apply (hh b h).trans; simp only [List.length_cons,List.length_append]; omega
    rw [List.map_append,List.sum_append,← HE,spendPath Z x l r,add_bill,show l++a.rev::r=(l++[a.rev])++r by simp, spendPath,hV,hQ,add_bill,reverse_step,Lattice.stop,he]; abel
termination_by w.length
decreasing_by subst_vars; simp
end YM.QCD.Sparks
