import YM.Eole.Wanted
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Bloc
variable (q:I→Bool)
local notation "X"=> Patio (A⊕Spine I)
local notation "Z"=> Patio (A⊕Spine J)
local notation "T'"=> spark -- dummy
local notation "G★"=> glowT W g
local notation "Γ"=> W.plant
local notation "P"=> sparC A q W
local notation "u"=> W.flag q
variable (x:E⊕K→Patio (A⊕Spine I))(h:∀ i,Polite q (g i) (x i))
lemma few_nonzero {D:Type}(f:D→Finset I) (s:Finset D)(x:D→Patio (A⊕Spine I))(h:∀ i,Polite q (f i) (x i))(hp:∏ i∈s,x i ≠0) : (s:Set D).PairwiseDisjoint f:=by
     intro i hi j hj he; by_contra H; apply hp; rw [← mul_prod_erase s x hi,← mul_prod_erase (s.erase i) x (mem_erase.mpr ⟨he.symm,hj⟩),←mul_assoc,(h i).nilpotent (h j) H,zero_mul]
variable (t:Support c)
lemma col_far (s:Finset (Finset (E⊕K)))(hs:s∉Set.range (piles W g)) : wanted W g Y q x s t=0:=by
    unfold wanted; split; next h=>
                by_contra hw; let v:=reward W g q x; have ht : (s:Set (Finset N)).PairwiseDisjoint G★:=few_nonzero u G★ s v (fun i=> overlay _ ..) hw; apply hs; exact ⟨_,Collide.uncluttered (tags W g) s (fun i hi j hj he=>by dsimp only[Function.onFun]; rw [tiles,tiles]; exact ht hi hj he) (fun i hi=> (h.1 i hi).1)⟩ -- onFun unfold
    next _=>rfl
noncomputable def gift (F:K→Patio A)(g:K→Hat c)(t:Support c)(s:Finset K): Patio A:= if (s:Set K).PairwiseDisjoint (fun i=>(g i).place) ∧ t=s.biUnion fun i=>(g i).inv then ∏ i∈s,F i else 0
lemma budgets (F:K→Patio A)(hf:Summable (fun i=> ‖F i‖)) : Summable (fun i=> ‖gift F Y t i‖):=by
    have hz:= summable_finsetProd_of_summable_nonneg (fun (i:K)=> norm_nonneg (F i)) hf; refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ?_) hz
    unfold gift; split; exact Finset.norm_prod_le ..
    rw [norm_zero]; exact prod_nonneg fun _ _=>norm_nonneg _
lemma illum (FXQ:K→Patio A)(h:∀ i:K,FXQ i*FXQ i=0)(hx:Summable fun i=> ‖FXQ i‖): HasSum (fun (p':Finset K)=>∏ i∈p',FXQ i) (NormedSpace.exp (∑' i,FXQ i)):=by
     have hh :Summable (fun p':Finset K=> ‖∏ i∈p',FXQ i‖):=Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun _=>Finset.norm_prod_le ..) (summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) hx)
     refine hasSum_of_subseq_of_summable hh (p:=atTop) (s:=Finset.powerset) (tendsto_atTop.2 ?_) ?_
     · intro i; filter_upwards [eventually_ge_atTop (i.biUnion id)] with z hz; exact fun j hj=>mem_powerset.mpr ((subset_biUnion_of_mem id hj).trans hz)
     have hz(i): NormedSpace.exp (FXQ i)-1=FXQ i:=by apply Subtype.ext; change light A (NormedSpace.exp _-1)=_ ; rw [map_sub,map_one,Cove.light_exp,radius_two _ (by rw[←map_mul,h,map_zero]),add_sub_cancel_left]; rfl
     have he(s:Finset K): NormedSpace.exp (∑ i∈s,FXQ i) = _ := flicker FXQ s; simp_rw [hz] at he; simp_rw [← he]; exact NormedSpace.exp_continuous.continuousAt.tendsto.comp hx.of_norm.hasSum
include h
variable (hr:∀ i:E,(g (.inl i)).Nonempty)(hx: Summable fun i:E⊕K=> ‖x i‖)
include hr hx
lemma developed : HasSum (fun s=>wanted W g Y q x s t) (sparC A q W (NormedSpace.exp (∑' i,x (.inl i))*(∑' i,gift (x ∘ Sum.inr) Y t i))):=by
    let f i:= x (Sum.inl i); let z':=gift (x ∘ Sum.inr) Y t; have ht:= illum f (fun i=>(h (.inl i)).nilpotent (h (.inl i)) (by obtain ⟨k,hk⟩:=hr i; exact fun he=>disjoint_left.mp he hk hk)) (hx.comp_injective Sum.inl_injective); have hZ:= budgets Y t (x∘Sum.inr) (hx.comp_injective Sum.inr_injective); let e := (@Finset.sumEquiv E K).toEquiv
    let JQ(i: Finset N):= prize W Y q x i t; have he : HasSum JQ (P (NormedSpace.exp (∑' i,f i) * ∑' i,z' i)):=by
         apply (e.symm.hasSum_iff).mp; refine ((P).hasSum (Cove.toss_big ht hZ.of_norm.hasSum ht.summable.norm hZ)).congr_fun fun p'=>?_ ; rcases p' with ⟨s,v⟩; change prize _ _ _ _ (s.disjSum v) _= P ((∏ i∈s,f i)*gift _ _ _ v); unfold prize selected flagsOf gift; rw[toRight_disjSum]; split_ifs with hv hh hh; · rw [prod_disjSum]; rfl
         · exact False.elim (hh ⟨hv.1,hv.2.symm⟩)
         · exact False.elim (hv ⟨hh.1,hh.2.symm⟩)
         rw[mul_zero,map_zero]
    have hi:Injective (piles W g):=fun i j h=> (recombine (tags W g) i).symm.trans ((congr_arg (fun p:Finset (Finset N)=>p.biUnion id) h).trans (recombine (tags W g) j))
    exact (hi.hasSum_iff (fun i=> col_far W g Y q x t i)).1 (he.congr_fun fun s=> unique_col W g Y q x h t s)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.developed
