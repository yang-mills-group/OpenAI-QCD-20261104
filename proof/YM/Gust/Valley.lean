import YM.Gust.Maple
import YM.Gust.Shield
import Mathlib.LinearAlgebra.Multilinear.Curry
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV Mater Kind
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}(hK:K.Domestic)
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
local notation "Sz"=>Stake T n
local notation "Yr"=>Mater T n
-- bare.z Evaluation extension shape star.No cut budgets.
noncomputable def ValueP(x:Points m)(A:Fin m→ Mater T n) := Kind.led (List.ofFn (fun i=> (A i).u))*∏ j: J, K.total m x (fun i=> (A i).v j)

private lemma spawned {I:Type}(m:ℕ)(R:(Fin m→ I)→ ℂ):∃ F:MultilinearMap ℂ (fun _:Fin m=> I→₀ ℂ) ℂ,∀ a:Fin m→ I,F (fun i=> Finsupp.single (a i) 1)=R a:=by
       induction m with
       | zero=>refine ⟨MultilinearMap.constOfIsEmpty ℂ (fun _:Fin 0=> _) (R Fin.elim0),fun i=>?_⟩; exact congr_arg R (Subsingleton.elim ..)
       | succ n ih=>
             choose G hG using fun i:I=> ih (fun p=>R (Fin.cons i p)); let h:= Finsupp.linearCombination ℂ G; refine ⟨LinearMap.uncurryLeft (M:=fun _=> I→₀ ℂ) h,fun a=>?_⟩; rw [LinearMap.uncurryLeft_apply]; unfold h; rw [Finsupp.linearCombination_single,one_smul]; exact (hG _ (Fin.tail a)).trans (congr_arg R (Fin.cons_self_tail _))
noncomputable def valuation (T:Pollens P K)(n m:ℕ)(x:Points m):= (spawned (I:=Mater T n) m (ValueP x)).choose
@[simp] lemma values (x:Points m)(u:Fin m→ Mater T n):valuation T n m x (fun i=>plant (u i))= ValueP x u:= (spawned m (ValueP x)).choose_spec u
open Finset
-- Multilinear array expansion induction (can ignore one-slot in induction if overwritten). Keeps universal parity.S proofs multilinear on arbitrary fields.
lemma recurs {I : Type*}[Fintype I][DecidableEq I] (H : (I→ Stake T n)→Prop)
    (hz:∀ a t,a t=0→ H a)(hj:∀ (a:I→Mater T n), H (fun i=>plant (a i)))
    (ha:∀ a i x y, H (update a i x) → H (update a i y)→ H (update a i (x+y)))
    (hb:∀ a i x,H (update a i x) →∀ c:ℂ, H (update a i (c • x))) (q:I→Stake T n) : H q:=by
      -- if I empty and Mater empty? always Mater nonempty incl zero in Col. construct.
      haveI : Nonempty (Mater T n):= ⟨⟨none,fun _=>0,fun i=> Submodule.zero_mem _⟩⟩
      have h (A: Finset I)(p:I→Stake T n)(hp:∀ i,i∉A → ∃ r,p i=plant r):H p:=by
            induction A using Finset.induction_on generalizing p with
            | empty=>choose! w h using hp; rw[show p=(fun i=> plant (w i)) from funext fun i=>h i (notMem_empty _)]; exact hj w
            | @insert a L hx ih=>
                  have hh (v:Stake T n): H (update p a v):=by
                       induction v using Mater.induced with
                       | h=> exact hz _ a (update_self ..)
                       | hu i c=> exact hb _ _ _ (ih (update p a (plant i)) (fun j hj=>by by_cases h:j=a; · subst j; exact ⟨_,update_self ..⟩
                                                                                          rw [update_of_ne h]; exact hp j (by simp[h,hj]))) _
                       | ht x y h k=> exact ha p a x y h k
                  exact update_eq_self a p ▸ hh (p a)
      exact h univ q fun i hi=> (hi (mem_univ _)).elim
-- usage: eval all.Any. equivalence stamps oriented names.
variable (x:Points m)(t:Fin m)(p:Fin m→ Stake T n)(u v:Stake T n)(hv:Fees u v)
noncomputable def wordT(x:Kind n)(t:Fin m)(y:Fin m→ Mater T n)(A:J→K.W):ℂ := Kind.led (List.ofFn (update (fun i=> (y i).u) t x)) -- adjust multiply
lemma sightV (u:Fin m→Mater T n)(t:Fin m):∃ N: Model K n,∀ i:Mater T n,ValueP x (update u t i)= N i.u i.v:=by
     let L(j:J): K.W→ₗ[ℂ]ℂ:= (K.total m x).toLinearMap (fun i=> (u i).v j) t
     let A:= MultilinearMap.mkPiAlgebra ℂ J ℂ; let B:= A.compLinearMap L; let c(r):= Kind.led (List.ofFn (update (fun i=> (u i).u) t r)); refine ⟨fun i:Kind n=> c i • B,fun i=>?_⟩; unfold ValueP; have hh:(fun j=> (update u t i j).u)=update (fun i=> (u i).u) t i.u:=funext fun j=>by by_cases he:j=t<;>simp[he]
     rw[hh]; refine congr_arg (fun h:ℂ => c i.u*h) (Finset.prod_congr rfl (fun k _=>?_)); refine congr_arg (K.total _ _) ?_; ext1 j; by_cases h:j=t <;> simp[h]
lemma towardT(t:Fin m)(v:Fin m→Mater T n): ∃ N: Model K n, ∀ w:Stake T n, valuation T n m x (update (fun i=> plant (v i)) t w)= morph N w:=by
      obtain ⟨N,hN⟩:= sightV x v t; refine ⟨N,fun i=>?_⟩; induction i using Mater.induced with
      | h=> rw [map_zero, MultilinearMap.map_update_zero]
      | hu i c=> rw[map_smul, MultilinearMap.map_update_smul,show update (fun i=>plant (v i)) t (plant i)=fun j=>plant (update v t i j) from funext fun j=>by by_cases h:j=t<;>simp[h],values,once,hN i]
      | ht x y hh hv=> rw[MultilinearMap.map_update_add,map_add,hh,hv]
include hv
lemma quotes : valuation T n m x (update p t u)=valuation T n m x (update p t v):=by
       haveI : Nonempty (Mater T n):= ⟨⟨none,fun _=>0,fun i=> Submodule.zero_mem _⟩⟩; let Y:=Classical.arbitrary (Mater T n); let S(p:Fin m→Stake T n):Prop:= valuation T n m x (update p t u)=valuation T n m x (update p t v)
       have H(A:Finset (Fin m))(q:Fin m→Stake T n)(h:t∉A)(hs:∀ i∉A,i≠t→∃ p,q i=plant p):S q:=by
             induction A using Finset.induction_on generalizing q with
             | empty=>
                  choose! p hp using hs; obtain ⟨M,hM⟩:=towardT x t p; have hE(r:Stake T n): update q t r= update (fun i=> plant (p i)) t r:=by
                     funext i; by_cases h:i=t; · subst i; simp
                     simp only[update_of_ne h]; exact hp i (notMem_empty _) h
                  unfold S; rw[hE,hE,hM,hM,hv]
             | @insert i A hi ih=>
                 have ht:t∉A:=fun h' => h (by simp [h']); have hj:t≠i:=by intro hp; exact h (by simp[hp])
                 have G(r:Stake T n): S (update q i r):=by
                     induction r using Mater.induced with
                     | h=> unfold S; rw[update_comm hj.symm, update_comm hj.symm, MultilinearMap.map_update_zero, MultilinearMap.map_update_zero] -- args
                     | hu j c=>
                           have hL:=ih (update q i (plant j)) ht (fun b hb he=>by
                               by_cases hz:b=i; · subst b; exact ⟨_,update_self ..⟩
                               rw [update_of_ne hz]; exact hs _ (by simp[hz,hb]) he);
                           unfold S at hL ⊢; rw [update_comm hj.symm,update_comm hj.symm] at hL ⊢; rw [MultilinearMap.map_update_smul,MultilinearMap.map_update_smul,hL]
                     | ht x y h k=> unfold S at h k ⊢; rw [update_comm hj.symm,update_comm hj.symm] at h k ⊢; rw[MultilinearMap.map_update_add,MultilinearMap.map_update_add,h,k]
                 exact update_eq_self i q ▸ G (q i)
       exact H (univ.erase t) p (by simp) fun i hi h=> False.elim (hi (mem_erase_of_ne_of_mem h (mem_univ i)))
omit hv
end YM.Massive.Gust
#print axioms YM.Massive.Gust.sightV
