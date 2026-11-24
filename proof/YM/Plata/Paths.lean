import YM.Alum.Goblet
/-! # Cut walks for buying independent replicas. All geometric assertions are at finite cutoff. The **single** adjoint per block may require arbitrary thermal sign, irrelevant to its seminorm but relevant to real stencils. -/
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Filter Lattice Wilson Massive Massive.Lyre Massive.Romance
open QCD QCD.Lat QCD.Tide QCD.RP Chess Cells
open scoped Topology BigOperators Classical ComplexOrder
variable {F:ℕ}{n:Side}(T:Tiling n)(a:Axis)(p:T.Cell)
/-- pivot a genuine seam with bounded physical height -/
lemma landing: ∃ p:T.Cell, (T.starts p a).val < T.side.val:=by
     let w:= T.side.val; let r:= (T.base a).val; let b:= r/w; let t:= r%w
     have hT:t<w:= Nat.mod_lt _ T.side.property
     have hh:t+b*w=r:=by unfold t b; rw[mul_comm]; exact Nat.mod_add_div ..
     let v:T.Cell:= -(b • step a)
     have he:T.starts v a=(t: Per n):=by
          unfold Tiling.starts v; simp only [map_neg,map_nsmul,T.root_step]; simp only[Pi.add_apply,Pi.neg_apply,Pi.mul_apply,Pi.natCast_apply,step_apply,↓reduceIte,nsmul_eq_mul,mul_one]
          rw[← ZMod.natCast_zmod_val (T.base a)]; change (↑r:Per n) + -((b:Per n)* _) = _; rw[← hh]; push_cast; unfold w; ring -- check det
     rw [← show T.side.val = w from rfl] at hT
     refine ⟨v,?_⟩; rw [he, ZMod.val_natCast_of_lt (hT.trans T.narrow)]; exact hT
noncomputable def peak (T:Tiling n)(p:T.Cell)(a:Axis)(d:ℕ):T.Cell:= p+d • step a
noncomputable def y (T:Tiling n)(p:T.Cell)(a:Axis):Cover:= (2*((T.starts p a).val:ℤ)-(1:ℤ)) • step a
noncomputable def hail (T:Tiling n)(p:T.Cell)(a:Axis)(d:ℕ): Cover:= y T p a+(2*d*T.side.val) • step a
noncomputable def trace (T:Tiling n)(p:T.Cell)(a:Axis)(d:ℕ)(adj:Bool): TapeWalk n T:= (peak T p a d,a)::(if adj then [] else [(p,a)])
lemma fence (i:ℕ)(ht:T.kind=.link): wrap n (hail T p a i)=(T.bandCut (peak T p a i) a).slide:=by
    unfold peak; have ht':∀ d:ℕ,T.starts (p+d • step a) a=T.starts p a+(d:Per n)*T.side.val:=by intro d; unfold Tiling.starts; rw [map_add,map_nsmul, T.root_step]; simp [add_assoc]
    unfold Tiling.bandCut Cut.slide; simp only[ht']; unfold hail y; rw [map_add,map_zsmul,map_nsmul,wrap_step]; ext1 j; by_cases h:j=a; subst j
    · change (2*((T.starts p a).val:ℤ)-1) • ((step a:Site n) a)+(2*i*T.side.val) • ((step a:Site n) a)=(2*_ - (T.kind.shift: Per n)) * ((step a:Site n) a)
      simp only [step_apply,↓reduceIte,nsmul_eq_mul,zsmul_eq_mul,Int.cast_mul,Int.cast_sub, Int.cast_natCast,mul_one,ZMod.natCast_zmod_val,ht,Kind.shift]; push_cast; ring
    simp [h]
lemma fenceP(ht:T.kind=.link): wrap n (y T p a)= (T.bandCut p a).slide:=by simpa [peak,hail] using fence T a p 0 ht
lemma arrived(i:ℕ)(x:T.Cell)(s:Bool): finish T x (trace T p a i s)=(if s then T.mate p a x else x)+(2*i) • step a:=by
     ext1 j; by_cases h:j=a; subst j
     · cases s<;> simp [trace,finish,peak]; all_goals ring
     cases s <;> simp [trace,finish,peak,h]
lemma withinJ (l:TapeWalk n T):Injective (fun p=> finish T p l):=by
     induction l with| nil=>exact injective_id| cons a l ih=> exact ((show Involutive _ from T.mate_invol a.1 a.2)|>.injective).comp ih
/-- Greedy selection of bounded offsets with arbitrary seam transports. -/
lemma freed {I J L X:Type*} [Fintype I] [Fintype J] [Fintype L] (v:I→ L→ J→ X) (hi:∀ i l,Injective (v i l)) (hV:∀ i j, Injective (fun l=> v i l j))(hx:Fintype.card (I × J) * Fintype.card J < Fintype.card L): ∃ g:I→ L,Injective (fun p:I × J => v p.1 (g p.1) p.2):=by
     haveI : Nonempty L:= Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hx)
     suffices ∀ s:Finset I,∃ g:I→L, ∀ a∈s,∀ b∈s,a ≠ b → ∀ i j, v a (g a) i≠ v b (g b) j by
          obtain ⟨g,hg⟩:= this Finset.univ
          refine ⟨g,?_⟩; rintro ⟨x,i⟩ ⟨y,j⟩ hh; by_cases h:x=y; · subst y; exact Prod.ext rfl (hi _ _ hh)
          exact (hg _ (Finset.mem_univ _) _ (Finset.mem_univ _) h i j hh).elim
     intro s; induction s using Finset.induction_on with
     | empty=> exact ⟨fun _=>Classical.arbitrary L,by simp⟩
     | @insert a s ha ih=>
          obtain ⟨g,hg⟩:=ih
          obtain ⟨l,hl⟩: ∃ l:L,∀ b∈s,∀ i j:J,v a l i≠v b (g b) j:=by
               by_contra! hp; choose b hm i j h using hp
               let f:L→ (I× J) ×J:=fun l=> ((b l,i l),j l)
               have ht:Injective f:=by
                    intro x y he; obtain ⟨he,hj⟩:= Prod.mk.inj he; obtain ⟨he,hi⟩:= Prod.mk.inj he; apply hV a (i y); change v a x (i y)=_; change _= v a y (i y); rw [← hi, h,he,hj, hi,h y] -- fun reducible
               exact not_lt_of_ge ((Fintype.card_le_of_injective f ht).trans_eq (Fintype.card_prod ..)) hx
          refine ⟨update g a l,?_⟩; intro x hx y hy h i j; rcases Finset.mem_insert.mp hx with hx|hx <;> rcases Finset.mem_insert.mp hy with hy| hy
          · subst x y; contradiction
          · subst x; simpa only [update_of_ne (Ne.symm h),update_self] using hl y hy i j
          · subst y; simpa only [update_of_ne h,update_self] using (hl x hx j i).symm
          rw [update_of_ne (show x ≠ a from fun h=> ha (h ▸ hx)),update_of_ne (show y≠a from fun h=>ha (h ▸ hy))]; exact hg x hx y hy h i j
lemma awards {I J:Type*}[Fintype I][Fintype J]{L:ℕ}(b:I→ Bool)(u:I→ℕ)(v:J→ T.Cell)(hv:Injective v)(hl:Fintype.card (I× J)* Fintype.card J<L)(hp:2*L≤ T.period.val):∃ g:I→ Fin L, Injective (fun q:I× J => finish T (v q.2) (trace T p a (u q.1+(g q.1).val) (b q.1))):=by
    refine freed (fun i (l:Fin L) v'=>finish T (v v') (trace T p a (u i+l.val) (b i))) (fun i l=> (withinJ T (trace T p a (u i+l.val) (b i))).comp hv) (fun i j=>?_) (by simpa using hl)
    intro x y he; apply Fin.ext; have hX := congr_fun he a
    change finish T _ (trace T p a _ _) a=finish T _ (trace T p a _ _) a at hX
    rw [arrived,arrived,Nat.left_distrib,Nat.left_distrib] at hX; simp only [Pi.add_apply,Pi.mul_apply,Pi.natCast_apply,nsmul_eq_mul,step_apply,↓reduceIte,mul_one, Nat.cast_add,add_right_inj] at hX -- rewrite order
    have hh:2*x.val=2*y.val:=by rw [← ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left x.isLt (by decide)) hp),←ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left y.isLt (by decide)) hp)]; rw [hX]
    omega
end YM.Plata
#print axioms YM.Plata.awards
#print axioms YM.Plata.fence
