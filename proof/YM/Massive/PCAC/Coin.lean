import YM.Massive.PCAC.Bare
/-! Gauge invariance and local support of mass-probe bare current. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open Onsite Tide Plum
open scoped Kronecker
open Finset
variable {S:Set (Site c)} (p q:Site c) (R:Regulator c F)(a b:Flavor F)(X:Spike)
local notation "P"=> Grid c
local notation "Ω"=> Modes c F
local notation "Λ"=> zone F
local notation "y"=> flavorW X a b c

structure RowsAt (S:Set (Site c))(T:P → Sour Ω):Prop where
    reads : LocalOn S T
    contained (U:P)(i j:Ω): T U i j≠0 → i.1.1∈S ∧ j.1.1∈S
    -- cov: Rᴴ* T(U^g)*R=T(U); equivalently use commuted intertwiner
    covariant (g:Frame c)(U:P) : T (gauge g U)*rotates F g= rotates F g*T U
variable {T V: Grid c → Sour (Modes c F)} -- notation bug var
lemma RowsAt.mulT (h:RowsAt S T)(v:RowsAt S V): RowsAt S (T*V):=by
    refine ⟨fun i j hp=> congr_arg₂ (·*·) (h.reads i j hp) (v.reads i j hp),?_,?_⟩
    · intro U i j he; by_contra! hr; apply he; rw [Pi.mul_apply,Matrix.mul_apply]; apply sum_eq_zero; intro k _; apply not_ne_iff.mp; intro H; exact hr ((h.contained U i k (left_ne_zero_of_mul H)).1) ((v.contained U k j (right_ne_zero_of_mul H)).2)
    intro g U; simp_rw [Pi.mul_apply]; rw [mul_assoc,v.covariant,←mul_assoc _ (rotates F g),h.covariant,mul_assoc]
lemma RowsAt.addT(h:RowsAt S T)(v:RowsAt S V): RowsAt S (T+V):=by
    refine ⟨fun i j hp=> congr_arg₂ (·+·) (h.reads i j hp) (v.reads i j hp),fun U i j he=>?_ , ?_⟩
    · by_cases hp:T U i j=0; swap; · exact h.contained U i j hp
      rw [Pi.add_apply,Matrix.add_apply,hp,zero_add] at he; exact v.contained U i j he
    intro g U; rw [Pi.add_apply,Pi.add_apply,add_mul,mul_add,v.covariant,h.covariant]
lemma RowsAt.subT(h:RowsAt S T)(v:RowsAt S V): RowsAt S (T-V):=by
    refine ⟨fun i j hp=> congr_arg₂ (·-·) (h.reads i j hp) (v.reads i j hp),fun U i j he=>?_ , ?_⟩
    · by_cases hp:T U i j=0; swap; · exact h.contained U i j hp
      rw [Pi.sub_apply,Matrix.sub_apply,hp,zero_sub] at he; exact v.contained U i j (neg_ne_zero.mp he)
    intro g U; rw [Pi.sub_apply,Pi.sub_apply,sub_mul,mul_sub,v.covariant,h.covariant]
lemma RowsAt.arg(h:RowsAt S T)(f:Insertion c F)(he:∀ U,f U=form (T U)): Fence S ⇑f:=by
    have hx: LocalOn S ⇑f:= fun i j H=> by rw [he,he,h.reads i j H];
    refine ⟨stays f.continuous,⟨hx,fun U=> ?_⟩,?_⟩
    · obtain ⟨u,hu⟩: f U∈ (pass (RP.setDay S (F:=F))).range:=by
         let P1:= (pass (RP.setDay S (F:=F))).range; rw [he]; unfold form; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _
         by_cases hp : T U i j=0; · rw [hp,zero_smul]; exact P1.zero_mem
         obtain ⟨hm,hx⟩:=h.contained U i j hp; let i':RP.Deck S F:= ((⟨i.1.1,hm⟩,i.1.2),i.2); let j':RP.Deck S F:= ((⟨j.1.1,hx⟩,j.1.2),j.2)
         exact ⟨T U i j • (psi j'*bar i'),by change (pass (RP.setDay S (F:=F))) _=_; rw [map_smul,map_mul,pass_psi,pass_bar]; rfl⟩
      exact ⟨u,(show pass (RP.setDay S) u=_ from hu).symm⟩
    intro k U; unfold slots; rw [he,form_map,Matrix.transpose_transpose,h.covariant,←mul_assoc, (rotates_law F k).1,one_mul,he]
lemma rowing {i j: Lat.Row c}(U V: Grid c)(hi:i.1∈S)(hj:j.1∈S)(h: Agrees S U V) : bareD R.t U 0 i j=bareD R.t V 0 i j:=by
    have hz(a:Axis): singleHop R.t U a i j=singleHop R.t V a i j:=by
        have hg : i.1+step a=j.1 → Lat.thread R.t U a i.1=Lat.thread R.t V a i.1:=fun he=> by unfold Lat.thread; rw [h (i.1,a) hi (by rw [show (i.1,a).1+step _=j.1 from he]; exact hj)];
        have hh : i.1-step a=j.1 → Lat.thread R.t U a (i.1-step a)= Lat.thread R.t V a (i.1-step a):=fun he=> by unfold Lat.thread; rw [h (i.1-step a,a) (show i.1- _∈S from he ▸ hj) (by rw [show (i.1-step a,a).1+step _=i.1 from sub_add_cancel ..]; exact hi)];
        rw [hop_read,hop_read]; split_ifs with h f g <;> first | rw [hg h, hh f] | rw [hg h] | rw [hh f] | rw [hh g] | skip
        all_goals rfl
    unfold bareD; simp_rw [Matrix.add_apply,Matrix.sum_apply,Matrix.sub_apply,hz]
lemma lean_change (k:Frame c)(U:P): leanD R (gauge k U)*rotates F k= rotates F k * leanD R U:=by
   unfold leanD rotates; rw [bareD_covariant,← copies_mul,← copies_mul, mul_assoc (siteRot k * _), (siteRot_u _).1,mul_one]
noncomputable def sext (U:P): Sour Ω:= Λ p * leanD R U * Λ q
lemma sextAt (h:p∈S)(hv:q∈S):RowsAt S (sext p q R):=by
    refine ⟨?_,?_,fun k U=>?_⟩
    · intro U V hx; ext i j; unfold sext; simp_rw [zright,zleft]; by_cases hi:i.1.1=p; swap; · simp [hi]
      by_cases hj:j.1.1=q; swap; · simp [hj]
      rw [if_pos hj,if_pos hj, if_pos hi,if_pos hi]; unfold leanD copies; rw [Matrix.blockDiagonal_apply,Matrix.blockDiagonal_apply]; split; exact rowing R _ _ (hi ▸ h) (hj ▸ hv) hx; rfl
    · intro U i j hX; by_cases hi:i.1.1=p; · by_cases hj:j.1.1=q; · exact ⟨hi ▸ h,hj ▸ hv⟩
                                             exact False.elim (hX (by unfold sext; rw [zright, if_neg hj]))
      exfalso; exact hX (by simp only [sext,zleft,zright,if_neg hi,ite_self])
    unfold sext; rw [mul_assoc _ (Λ q),(commute_zone q k).eq,← mul_assoc, mul_assoc (Λ p) (leanD R (gauge k U)), lean_change,← mul_assoc (Λ p), (commute_zone p k).eq]; simp_rw [mul_assoc]
lemma RowsAt.extend(h:RowsAt S T): RowsAt S (fun U=> T U*y):=by
    refine ⟨fun i j hx=> congr_arg (·*y) (h.reads i j hx),fun i j k he=>?_, fun k U=>?_⟩
    · obtain ⟨t,-,ht⟩:=exists_ne_zero_of_sum_ne_zero (by rw [Matrix.mul_apply] at he; exact he); obtain ⟨hx,hv⟩:= h.contained i j t (left_ne_zero_of_mul ht); have hh:t.1.1=k.1.1:= not_not.mp fun ha=> right_ne_zero_of_mul ht (focused a b X t k ha); exact ⟨hx,hh ▸ hv⟩
    change _*y*_= _*(T U*y); rw [mul_assoc (T (gauge k U)), ← (commuteSpin a b X k).eq,← mul_assoc (T (gauge k U)), h.covariant,mul_assoc]
lemma invariant_flow (h:p∈S)(hv:q∈S): Fence S (⇑(current R a b p q)):=by apply RowsAt.arg (RowsAt.extend a b 1 ((sextAt q p R hv h).subT (sextAt p q R h hv))) _ fun i=>rfl
lemma scalar (h:p∈S): Fence S (⇑(scalarProbe a b p X)):=by
    apply RowsAt.arg (RowsAt.extend a b X (T:=fun _=>zone F p) ?_) _ (fun _=>rfl); refine ⟨fun _ _ _=> rfl,fun U i j he=>?_,fun k U=> (commute_zone _ _).eq⟩
    unfold zone at he; simp only [Matrix.diagonal_apply] at he; split_ifs at he with h1 h2; · exact ⟨h2 ▸ h,h1 ▸ h2 ▸ h⟩
    all_goals exact False.elim (he rfl)
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.invariant_flow
