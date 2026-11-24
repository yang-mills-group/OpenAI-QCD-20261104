import YM.MassiveQCD.Ribbon.Axis
/-! # l¹ joint charges -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Cove QCD.Creek Function Finset
open scoped Topology BigOperators ContDiff Classical
variable {A B C:Type}[Fintype A][Fintype B]{p:A→ℝ}{q:B→ℝ} (h:∀ i,0<p i)(k:∀ i,0<q i)
lemma pause (u:A↪ B) (x:Alg A)(s: Finset A): ‖coef (s.map u) (embed u x)‖= ‖coef s x‖:=by
   conv_lhs=> rw [← write x,map_sum,map_sum];
   rw [sum_eq_single s]; rotate_left
   · intro i _ hi; rcases embed_blade u i with he|he <;> rw [map_smul,map_smul,he] <;> simp [read_other _ _ (show s.map u≠ i.map u from fun hm=> hi (map_injective u hm).symm)]
   · simp
   rcases embed_blade u s with he|he <;> rw [map_smul,map_smul,he] <;> simp
include k in
lemma transplant (u:A↪ B) (x:Alg A) : load q (embed u x)= load (q ∘ u) x:=by
   let E:= univ.image (fun i:Finset A=> i.map u); rw [dry q k,← sum_subset (s₁:=E) (subset_univ _) (fun i _ hi=> ?_)]
   · rw [sum_image (fun i (_:i∈(univ:Finset (Finset A))) j _ (h:i.map u=j.map u)=> map_injective u h),dry (q ∘ u) (fun i=> k (u i))]; exact sum_congr rfl fun i _=> by rw [pause, prod_map]; rfl
   have hV (s:Finset A): i≠s.map u:=by rintro rfl; exact hi (mem_image_of_mem _ (mem_univ _))
   have he:Cove.light (Pairs A) 1=1:=map_one _ -- edit
   rw [show coef i (embed u x)=0 from ?_,norm_zero,mul_zero]
   rw [← write x,map_sum,map_sum]; refine sum_eq_zero fun j _=>?_ ; rw [map_smul,map_smul]; rcases embed_blade u j with h|h <;> simp only [h,map_neg,read_other _ _ (hV _),neg_zero,smul_zero]
lemma scenic (u:A↪ B) (x: Alg A) : ‖embed u x‖=‖x‖:=by
   have he{I:Type}[Fintype I](x:Alg I): load (fun _=>1) x= ‖x‖:=by rw [dry _ (fun _=>one_pos),norm_def]; simp
   exact (he _).symm.trans ((transplant (q:=fun _=>1) (fun _=>one_pos) u x).trans (he x))
lemma implant (u:A↪ B): Injective (embed u):=by
    intro a b he; apply sub_eq_zero.mp; refine norm_eq_zero.mp ?_; rw [← scenic u,map_sub,he,sub_self,norm_zero]
lemma bank (s:Finset A)(t:Finset B)(x: Alg (A⊕B)): ‖coef s (scrape A t x)‖= ‖coef (s.disjSum t) x‖:=by
    rw [pokes,map_sum,sum_eq_single s]
    · rcases broken s t with h|h <;> rw [h] <;> simp
    · intro i _ hi; rw [map_smul,map_smul,read_other _ _ hi.symm,smul_zero,smul_zero]
    simp
noncomputable abbrev expRate : A⊕B→ℝ:=Sum.elim p q -- autoImplicit inaccessible p q abbrev body? omitted
include h k
omit [Fintype A] [Fintype B] in
lemma expPos (i:A⊕B): 0< expRate (p:=p) (q:=q) i:=by cases i with | inl=> exact h _ | inr=> exact k _
lemma fiscal (x:Alg (A⊕B)) : load (expRate (p:=p) (q:=q)) x=∑ i :Finset B,(∏ j∈i,q j)*load p (scrape A i x):=by
   rw [dry _ (expPos h k)]; let e : Finset A × Finset B ≃ Finset (A⊕B) := ⟨fun ⟨a,b⟩=> a.disjSum b, fun i=>(i.toLeft,i.toRight), fun i=>Prod.ext (by simp) (by simp),fun i=>by ext u; cases u <;>simp⟩
   rw [← Equiv.sum_comp e, Fintype.sum_prod_type,sum_comm]; refine sum_congr rfl fun i _=>?_; rw [dry p h, Finset.mul_sum]; refine sum_congr rfl fun j _=>?_ ; change (∏ k∈ j.disjSum i, expRate (p:=p) (q:=q) k)* ‖coef (j.disjSum i) x‖= _; rw [prod_disjSum,bank]; simp only [expRate,Sum.elim_inl,Sum.elim_inr]; ring
lemma stakesBill (s:Finset B)(x:Alg A): load (expRate (p:=p) (q:=q)) (stake A s x)=(∏ j∈s,q j)*load p x:=by
    rw [fiscal h k,sum_eq_single s]
    · rw [quid]
    · exact fun i _ hi=>by rw [stakesX,if_neg hi,QCD.Cove.load_zero,mul_zero]
    simp
end YM.MassiveQCD.Ribbon
