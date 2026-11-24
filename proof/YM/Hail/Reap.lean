import YM.Hail.Left
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)
local notation "p"=> Points.direction (0:Fin 2) j
local notation "Q"=> chime (![d,e]) x
local notation "M"=>unionB Q
local notation "X"=> letters d
local notation "Y"=> letters e
local notation "B"=>Pol (d+2)
noncomputable def tagD (s:List (letters d)):SpinPol d := (s.map atom).prod
private lemma rises {N:ℕ}{g:Fin N→ℕ}(s:Fin N)(L:List (letters (g s))) : twig g s (tagD L)= pwn (L.map (fun i=> rifle g s (thetaBasis _ i))):= by
    induction L with
    | nil=> exact map_one _
    | cons i L h=> change twig g s (atom i*tagD L)=line _*_; rw [map_mul,h]; congr 1; exact ExteriorAlgebra.map_apply_ι _ _ -- line name Creek?
variable (s:List (letters d))(t:List (letters e))
lemma beamK : spins d e x (tagD s) (tagD t)=lease Q (pwn (s.map (fun i=> rifle (![d,e]) 0 (thetaBasis _ i))++t.map (fun i=>rifle (![d,e]) 1 (thetaBasis _ i)))):=by
   change lease Q (twig (![d,e]) 0 _ * twig (![d,e]) 1 _)=_; apply congr_arg
   have hz : twig (![d,e]) 0 _= _ :=rises (g:=![d,e]) 0 s; have he:=rises (g:=![d,e]) 1 t
   exact Eq.trans (congr_arg₂ (·*·) hz he) (by simp [pwn])
noncomputable def atP (x:Points 2)(u:letters d)(v:letters e):ℂ:=pair x (u:=![d,e]) ⟨(0:Fin 2),u⟩ ⟨1,v⟩ -- arg order x named?
noncomputable def fan (x:Points 2)(s:List (letters d))(t:List (letters e)):=spins d e x (tagD s) (tagD t)
include hx
lemma hus (V:X): fan x (V::s) t =∑ i:Fin t.length,(-1:ℂ)^(s.length+i.val) * atP x V t[i] * fan x s (t.eraseIdx i.val) :=by
    let H:Fin 2→ℕ:=![d,e]; let N:=fun v:X=>rifle H 0 (thetaBasis _ v); let W:=fun v:Y=>rifle H 1 (thetaBasis _ v); let A:=s.map N; let C:=t.map W
    rw [fan,beamK]; change lease Q (line (N V) * pwn (A++C))=_; rw [veil]; let g(i:Fin (A++C).length):= (-1:ℂ)^i.val*(unionB Q (N V) ((A++C)[i.val])) *lease Q (pwn ((A++C).eraseIdx i.val)); change (∑ i:Fin (A++C).length,g i)=_; let B': (A++C).length=s.length+t.length:=by simp [A,C];
    let k':= finCongr B'; rw [show ∑ i,g i= ∑ j:Fin (s.length+t.length),g (k'.symm j) from Fintype.sum_equiv k' g _ (fun i=>by rw [Equiv.symm_apply_apply]), Fin.sum_univ_add]; rw [Finset.sum_eq_zero (f:=fun i:Fin s.length=>g (k'.symm (i.castAdd t.length))) ?h1, zero_add]; swap
    · intro i _; let j:= k'.symm (i.castAdd t.length); have h:j.val=i.val:=rfl; have hh:j.val<s.length:=h.symm▸i.isLt; have hp:j.val<A.length:=by simpa [A];
      have hv: (A++C)[j.val]=N s[j.val]:=(List.getElem_append_left hp).trans (List.getElem_map _); unfold g; rw[hv,show unionB Q (N V) (N _)=0 from quiets x hx _ _ _,mul_zero,zero_mul]
    apply Finset.sum_congr rfl; intro i _; let j:=k'.symm (Fin.natAdd s.length i); have he:j.val=s.length+i.val:=rfl; have hp:A.length≤j.val:=by simp [A,he];
    have hv: (A++C)[j.val]= W t[i]:=(List.getElem_append_right hp).trans ((List.getElem_map W).trans (by simp [he,A])); have hY:(A++C).eraseIdx j.val=A++(t.eraseIdx i.val).map W:=by rw[List.eraseIdx_append]; unfold C; simp [he,A,List.eraseIdx_map]
    have hZ(u:X)(v:Y): M (N u) (W v)=atP x u v:=by unfold N W; rw [mounted,mounted,DawnS.sector x hx]; rfl
    unfold g; rw [hv,hZ,hY,he,fan,beamK]; rfl
lemma tailV(u:Y): fan (d:=d) x [] (u::t)=0:=by
    let H:= ![d,e]; let W:=fun v:Y=>rifle H 1 (thetaBasis _ v); let A:= t.map W; rw [fan,beamK]; change lease Q (line (W u)*pwn A)=_; rw[veil]; apply Finset.sum_eq_zero; intro i _; have hh: i.val<t.length:=by have ht:=i.isLt; simpa [A] using ht
    have he:A.get i=W t[i.val]:= List.getElem_map W
    rw [he,show unionB Q (W u) (W _)=0 from quiets x hx _ _ _,mul_zero,zero_mul]
lemma emptyS : fan (d:=d) (e:=e) x [] []=1:=by rw[fan,beamK]; exact clean1 _
lemma sweet(v:PowerPair d): basisU d v= (MvPolynomial.monomial v.1 1)⊗ₜ[ℂ] tagD (atomList v.2):=by unfold tagD; rw [show ((atomList v.2).map atom).prod= mono v.2 from ((expression v.2).choose_spec.2.2.trans (by rw [atomList,List.map_ofFn])).symm]; exact Module.Basis.tensorProduct_apply ..
end YM.Hail
#print axioms YM.Hail.tailV
#print axioms YM.Hail.hus
