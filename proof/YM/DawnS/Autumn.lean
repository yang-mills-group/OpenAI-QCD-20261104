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
noncomputable abbrev leans (i:Vault d):= rifle wd 0 (adjLine d (jewel C i))
noncomputable abbrev rightP(i:Vault d):= rifle wd 1 (jewel C i)
noncomputable def cream(l t:List (Vault d)) :ℂ:= lease Q (pwn (l.reverse.map (leans C) ++ t.map (rightP C)))
local notation "M"=>cream r C
variable (l t:List (Vault d))(a:Vault d)
include he hr
local notation "K"=> List.length
private lemma tought (i j:I): QZ (leans C i) (rightP C j)=if i=j then 1 else 0:=ports r C he i j
lemma flute : cream r C (l++[a]) t =∑ i:Fin t.length,(if a=t[i] then (-1:ℂ)^(l.length+i.val) else 0)*cream r C l (t.eraseIdx i.val):=by
     let x:= l.reverse.map (leans C); let y:=t.map (rightP C); let A:=leans C a
     have hx: x.length=l.length:=by simp[x]
     have hz : M (l++[a]) t=lease Q (line A*pwn (x++y)):=by unfold cream; simp only[List.reverse_append,List.reverse_singleton,List.cons_append,List.nil_append,List.map_cons,pwn,List.prod_cons]; rfl
     rw [hz,veil]; let g(i:Fin (x++y).length):= (-1:ℂ)^i.val * (unionB Q A ((x++y)[i.val]))* lease Q (pwn ((x++y).eraseIdx i.val))
     change (∑ i:Fin (x++y).length,g i)=_
     let V:= l.reverse; let hK: (x++y).length=l.length+t.length:=by simp[x,y]
     let k:=finCongr hK; rw [show ∑ i,g i=∑ j:Fin (l.length+t.length),g (k.symm j) from Fintype.sum_equiv k g _ (fun i=>by rw [Equiv.symm_apply_apply]), Fin.sum_univ_add]; rw [Finset.sum_eq_zero (f:=fun i:Fin l.length=>g (k.symm (i.castAdd t.length))) ?h1,zero_add]
     swap
     · intro i _; let j:= k.symm (i.castAdd t.length); have h:j.val=i.val:=rfl; have hp: j.val<x.length:=hx.symm ▸ h.symm ▸ i.isLt
       have hW: j.val<l.reverse.length:=by rw[h,List.length_reverse]; exact i.isLt
       have hz:(x++y)[j.val]=leans C l.reverse[j.val]:=(List.getElem_append_left hp).trans (List.getElem_map _)
       unfold g; rw[hz,show unionB Q A (leans C _) =0 from quiets (dotsG r) (distinct r hr) _ _ _,mul_zero,zero_mul]
     apply Finset.sum_congr rfl; intro i _; let j:= k.symm (Fin.natAdd l.length i); have heq:j.val=l.length+i.val:=rfl
     have hp:x.length≤j.val:=by rw [hx,heq]; omega
     have hz :(x++y)[j.val]=rightP C t[i]:=(List.getElem_append_right hp).trans ((List.getElem_map (rightP C)).trans (by simp[heq,hx]))
     have hY:(x++y).eraseIdx j.val=x++(t.eraseIdx i.val).map (rightP C):=by rw[List.eraseIdx_append]; unfold y; simp [heq,hx,List.eraseIdx_map]
     unfold g; rw [hz,tought r hr C he a _,hY,heq]; split <;> simp only[*,mul_one, mul_zero] <;> rfl
end YM.DawnS
