import YM.DawnS.Autumn
import YM.DawnS.Sea
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder ENNReal
variable {d:ℕ}(r:ℝ)(hr:0<r)
set_option quotPrecheck false
local notation "I"=> Vault d
local notation "wd"=>fun _ : Fin 2 =>d
local notation "Q"=> chime (fun _ : Fin 2=>d) (dotsG r)
local notation "QZ"=>unionB Q
variable (C:Matrix (Vault d) (Vault d) ℂ)(hc:IsUnit C)(he:Cᴴ*hank d r*C=1)
local notation "M"=>cream r C
variable (l t:List (Vault d))(a:Vault d)
include he hr
local notation "K"=> List.length
lemma silk (l':List (Vault d))(a:Vault d): M [] (a::l')=0:=by
     let L:= l'.map (rightP C)
     change lease Q (line (rightP C a)*pwn L)=_; rw[veil]; apply Finset.sum_eq_zero; intro i _
     rw [show (unionB Q (rightP C a) (L.get i)) =0 from ?_,mul_zero,zero_mul]; unfold L; simp only[List.get_eq_getElem,List.getElem_map]; exact quiets (dotsG r) (distinct r hr) _ _ _
lemma vernal (h:l.Nodup): M l l=1:=by
     induction l using List.reverseRecOn with
     | nil => exact clean1 _
     | append_singleton l a ih=>
        have hp:=List.nodup_append.mp h; let i: Fin (l++[a]).length:=⟨l.length,by simp⟩; let L:=l++[a]
        rw [flute r hr C he,Finset.sum_eq_single_of_mem i (mem_univ _)]; swap
        · intro j _ hj; have hv: (l++[a])[i]= a:=by simp only[i]; simp
          rw[if_neg (fun he'=> hj ((List.nodup_iff_injective_get.mp h) (he'.symm.trans hv.symm))),zero_mul]
        rw [show L[i]=a from (by unfold L i; simp),if_pos rfl,show L.eraseIdx i.val=l from ?_]; rw [ih hp.1, mul_one, (show Even (l.length+i.val) from ⟨i.val,rfl⟩).neg_pow,one_pow]; unfold L i; rw[List.eraseIdx_append]; simp
omit he hr in
lemma deseret (i:Fin l.length) : insert l[i] (l.eraseIdx i.val).toFinset = l.toFinset:=by
     induction l with
     | nil=> exact Fin.elim0 i
     | cons a l ih=>
        refine Fin.cases ?_ (fun j=>?_) i
        · simp
        simp only [Fin.getElem_fin,Fin.val_succ,List.getElem_cons_succ,List.eraseIdx_cons_succ,List.toFinset_cons]; rw[Finset.insert_comm]; exact congr_arg (fun x:Finset (Vault d)=>insert a x) (ih j)
lemma wiseman (h:l.Nodup)(hT:t.Nodup)(hf:l.toFinset≠t.toFinset): M l t=0:=by
     induction l using List.reverseRecOn generalizing t with
     | nil=>cases t with|nil=>contradiction|cons a t=> exact silk r hr C he t a
     | append_singleton l a ih=>
        rw[flute r hr C he _ t a]; refine Finset.sum_eq_zero fun i _=>?_ ; split_ifs with hv
        · have h₁ : l.toFinset ≠ (t.eraseIdx i.val).toFinset:=by intro hs; apply hf; rw [List.toFinset_append,show [a].toFinset={a} from (by simp),Finset.union_singleton,hs,hv]; exact deseret t i
           -- h shadow
          rw [ih (t.eraseIdx _) (List.nodup_append.mp h).1 (List.Nodup.eraseIdx i.val hT) h₁,mul_zero]
        rw[zero_mul]
end YM.DawnS
