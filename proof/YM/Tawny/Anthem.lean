import YM.Tawny.Snip
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
local notation "U"=> (0:Multi 8)
variable (e:ℂ) (x:RawTensor e 8)
set_option quotPrecheck false
local notation "X" i:arg j:arg=> (x.val (i,j)).val
local notation "D" p q => prism0 a p q
local notation "g" p:arg q:arg i:arg j:arg=>prism0 a p q (X i j)
local notation "L" i:arg=> UV.first i
variable (p q:Multi 8)(i j k l:Axis)
open StressFlux.Offer
private lemma hA (S:Signed)(i j:Axis): (marks S (i,j):ℂ)≠0:=by simp [marks,StressFlux.sign]; split_ifs <;> simp_all
lemma bid0 : ∃ z:ℂ,g U U i j=z • flair [i,j]:=by
    apply roleS a _ _ _ _ _ _ _ (by decide) _ _ (fun _=> rfl) _ (fun k=> hA _ _ _)
    intro k s v; rw [visa]; unfold v marks StressFlux.sign
    have hx:= marked_root s 8; simp only [hx,mul_one, Complex.ofReal_one,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Prod.fst,Prod.snd]; unfold signT; split <;> split <;> norm_num
lemma bidP : ∃ z:ℂ,g U (L k) i j=z • flair [i,j,k]:=by
    apply roleS a _ _ _ _ _ _ _ (by decide) _ _ (fun _=>rfl) _ (fun _=> hA _ _ _)
    intro v s r; rw[visa]; unfold r marks StressFlux.sign
    simp only [marked_root,vital,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul, Prod.fst,Prod.snd]; unfold signT; split <;> split <;> first| (split <;> norm_num)|(norm_num) -- k sign cancels directly
set_option maxHeartbeats 900000 in
lemma parade(P:Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag P)): g (hem (flag P) p) (hem (flag P) q) (P i) (P j)=conjug w (g p q i j):=by
    exact roleP a p q e acts marks Prod.swap x (by decide) (i,j) P w hw (show marks (flag P) (i,j)=1 from by simp [marks,flag,StressFlux.sign])
lemma parade0 (P: Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag P)): g U U (P i) (P j)=conjug w (g U U i j):=by have hp:=parade a e x U U i j P w hw; rw [hem_ground] at hp; exact hp
lemma paradeL (P: Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag P)): g U (L (P k)) (P i) (P j)= conjug w (g U (L k) i j):=by have hp:=parade a e x U (L k) i j P w hw; rw [hem_ground,hem_first] at hp; exact hp
lemma S_seal : g p q j i=e • g p q i j:=by rw [show x.val (j,i)=e • x.val (i,j) from (show Meaning _ _ _ _ _ _ from x.property).sym (i,j), SetLike.val_smul, map_smul] -- coe_smul
lemma trans1 : g q p i j=truck (g p q i j):=Eq.symm (roleL a p q _ _ _ _ x (by decide) (i,j))
lemma negS (S:Spike)(h: -S=S):S=0:=by ext i j; exact neg_eq_self.mp (congr_fun (congr_fun h i) j)
lemma unroof (hi:i≠j): g U U i j=0:=by
     obtain ⟨z,hz⟩:= bid0 a e x i j; have he:= trans1 a e x U U i j; apply negS; apply Eq.symm; rw [hz] at he; rw [hz]
     rw [truck_v,show flair [i,j]=gamma i*gamma j from by simp [flair],truck_double _ _ hi,smul_neg] at he; simpa only [flair,List.map_cons,List.map_nil,List.prod_nil,List.prod_cons,mul_one] using he
lemma flairC (P:Equiv.Perm Axis)(w:EuPin)(hw:w.Lifts (flag P))(l:List Axis): conjug w (flair l)= flair (l.map P):=by rw [flair_turn _ _ hw,show visa l (flag P)=1 from (by unfold visa; induction l <;> simp_all only[List.map_cons,List.map_nil,List.prod_cons,List.prod_nil] <;> simp [flag,signT]),one_smul]; rfl
-- symmetric h:isTensor determinant branches
lemma off_ax (x:RawTensor 1 8)(hi:i≠j)(ht:k≠i)(hl:k≠j): prism0 a U (L k) (x.val (i,j)).val=0:=by
     obtain ⟨z,hz⟩:= bidP a 1 x i j k; let P:= Equiv.swap i j; obtain ⟨w,h⟩:=EuPin.choice (flag P); let B:=flair [i,j,k]; let s:= prism0 a U (L k) (x.val (i,j)).val
     have he: s= conjug w s:=by
          have hp:= paradeL a 1 x i j k P w h; rw [show P k=k from Equiv.swap_apply_of_ne_of_ne ht hl,show P i=j from Equiv.swap_apply_left ..,show P j=i from Equiv.swap_apply_right .., S_seal a 1 x,one_smul] at hp; exact hp
     change s= z • B at hz; change s=0
     have ht₁:conjug w B= -B:=by unfold B; rw [flairC _ _ h]; unfold P; simp only [flair,List.map_cons,List.map_nil,Equiv.swap_apply_left,Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne ht hl,List.prod_nil,List.prod_cons,mul_one,←Matrix.mul_assoc,clifford hi.symm,neg_mul]
     exact negS _ (by nth_rw 2[he,hz]; rw [conj_s, ht₁, hz,smul_neg])
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.off_ax
