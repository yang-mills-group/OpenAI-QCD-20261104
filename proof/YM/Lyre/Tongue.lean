import YM.Lyre.Value
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open FlareV
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
variable (Q:I→Bool)(u v: List I)(a b:Finset I)
local notation "ZI"=> Patio (A⊕Spine I)
local notation "ZJ"=>Patio (B⊕Spine J)
noncomputable def chants (A:Type)[Fintype A] := numbered Q A u.get
lemma tops : crest u.get=u.toFinset:=by ext i; simp only [exists_fix,List.mem_toFinset]; exact (List.mem_iff_get).symm
variable (x y: Patio (A⊕Spine I))
lemma tipN (V:Patio (A⊕Spine I)) : chants Q u A (pick A Q u.toFinset V)= chants Q u A V:=by
   unfold chants numbered; simp only [_root_.smul_apply,pick]; rw [many]; rw[tops]; simp
lemma knolls (hi:¬ a⊆ b)(hp: ValidPieces A Q b x): pick A Q a x=0:=by
   nth_rw 1 [← hp.wholly]; apply Subtype.ext; change stake A _ (pluck A _ (slash A Q _ x))=_; rw [control]; split
   next h=> obtain ⟨i,hi',h⟩:=h; apply False.elim (hi ((burstUnique Q h).symm ▸ (mem_powerset.mp hi')))
   exact map_zero _
private lemma stall {x y:ZI}(hp:Polite Q a x)(hg:Polite Q b y)(H:Finset I)(he:a∪b≠ H): pick A Q H (x*y)=0:=by apply Subtype.ext; change stake A _ (pluck A _ _)=0; rw [show pluck A _ (x*y)=0 from (hp.attached hg).spectral _ ((burstUnique Q).ne (Ne.symm he)),map_zero]
lemma concert (hx: ValidPieces A Q a x)(hy:ValidPieces A Q b y)(hp:Disjoint a b): pick A Q (a∪b) (x*y)=(pick A Q a x)*(pick A Q b y):=by
    let f:=fun i=>pick A Q i x; let g:=fun i=>pick A Q i y
    let U:=a.powerset; let V:=b.powerset; let W:=pick A Q (a∪b)
    have h₁(i:Finset I)(j:Finset I)(hi:i⊆ a)(hj:j⊆ b)(ht: i∪j=a∪b): i=a ∧ j=b:=by
        apply And.intro
        · apply Finset.Subset.antisymm hi; intro x hx; have hh:x∈i∪j:=ht.symm ▸ mem_union_left _ hx; exact (mem_union.mp hh).resolve_right (fun hx'=> disjoint_left.mp hp hx (hj hx'))
        apply Finset.Subset.antisymm hj; intro x hx; have hh:x∈i∪j:=ht.symm ▸ mem_union_right _ hx; exact (mem_union.mp hh).resolve_left (fun hx'=> disjoint_left.mp hp (hi hx') hx)
    change W (x*y)= f a*g b; have hx': x=∑ i∈U,f i:=by convert hx.wholeV using 2; ext i; simp [U]
    have hy': y=∑ i∈V,g i:=by convert hy.wholeV using 2; ext i; simp[V]
    rw [hx',hy',Finset.sum_mul,map_sum,sum_eq_single a]
    · rw [mul_sum,map_sum,sum_eq_single b]; exact eq_pick _ _ _ _ ((choseTuft ..).attached (choseTuft ..))
      intro j hj hv; exact stall Q a j (choseTuft ..) (choseTuft ..) (a∪b) (fun h=>hv (h₁ _ _ le_rfl (mem_powerset.mp hj) h).2); simp[V]
    · intro i hi hh; rw [mul_sum,map_sum]; exact sum_eq_zero fun j hj=>stall Q i j (choseTuft ..) (choseTuft ..) (a∪b) (fun h=>hh (h₁ _ _ (mem_powerset.mp hi) (mem_powerset.mp hj) h).1)
    simp[U]
noncomputable def chorus := armature Q u.get
lemma hymns (u v:List I): chorus Q (u++v)=chorus Q v * chorus Q u:=by
    have he(u:List I): chorus Q u = (u.map (fun i=>mono (burst Q {i}))).reverse.prod:=by
         unfold chorus armature; have hp : u= List.ofFn u.get:=List.ofFn_get _|>.symm; -- from get
         rw [show List.ofFn (fun i=>mono (burst Q {u.get i}))=(u.map _) from ?_];
         conv_rhs=> rw[hp];
         rw [List.map_ofFn]; rfl
    rw [he,he,he,List.map_append,List.reverse_append,List.prod_append]
lemma melody (hx:Polite Q u.toFinset x)(hu:u.Nodup):(x:Alg (A⊕Spine I))=fiber (Spine I) (chants Q u A x)*quill A (chorus Q u):=Quills.charge _ _ _ _ ((tops u).symm ▸ hx) (List.nodup_iff_injective_get.mp hu)
lemma weaveV (U V:ZI)(hx:Polite Q u.toFinset U)(hy:Polite Q v.toFinset V)(hw:(u++v).Nodup):
    chants Q (u++v) A (U*V)=chants Q u A U *chants Q v A V:=by
   let P:= chants Q u A U; let R:= chants Q v A V; let S:= fiber (Spine I) (A:=A); let w:= chorus Q (u++v); let H:= quill A (B:=Spine I); have hp:U.val=S P * H (chorus Q u):=melody Q u U hx (List.nodup_append.mp hw).1
   refine Quills.cuts A Q (u++v).get (List.nodup_iff_injective_get.mp hw) _ _ (?_); change U.val*V.val=S (P*R)*H w
   rw [hp,mul_assoc, (V.property.central _).eq, melody Q v V hy (List.nodup_append.mp hw).2.1,show w=_ from hymns Q u v,map_mul,map_mul]; simp only [mul_assoc]; rfl
lemma voiced (hx:ValidPieces A Q u.toFinset x) (hy:ValidPieces A Q v.toFinset y)(hw:(u++v).Nodup) : chants Q (u++v) A (x*y)=chants Q u A x*chants Q v A y:=by
    rw[← tipN Q (u++v) (x*y)]; rw [List.toFinset_append,concert Q _ _ x y hx hy (by -- proof
       apply disjoint_left.mpr; intro i hi hu; have hv:= (List.nodup_append.mp hw).2.2; exact hv i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hu) rfl)]
    rw [weaveV Q u v _ _ (choseTuft ..) (choseTuft ..) hw,tipN Q u x,tipN Q v y]
lemma solo0 (x:Patio A): chants Q [] A (rootR (Spine I) A x)=light A x:=by rw[chants, emptyN]; change scrape A ∅ (fiber (Spine I) x.val)=_; rw [← quiet,quid]; rfl
lemma solv (x:Patio A): ValidPieces A Q ∅ (rootR (Spine I) A x):=by apply ValidPieces.role (∅:Finset I); change Polite Q ∅ (rootR _ _ _); refine ⟨x.val,?_⟩; change stake A _ _= _; rw [burst_absent]; exact quiet ..; exact Subset.refl _
lemma multiplied {L:Type} (l:List L)(W:L→List I)(V:L→ ZI)(hp:∀ i∈ l, ValidPieces A Q (W i).toFinset (V i))(hv:(l.flatMap W).Nodup) : ValidPieces A Q (l.flatMap W).toFinset (l.map V).prod ∧ chants Q (l.flatMap W) A (l.map V).prod=(l.map fun i=> chants Q (W i) A (V i)).prod:=by
   induction l with
   | nil=> exact ⟨ValidPieces.oneV, by change chants Q [] _ 1=1; exact (map_one (rootR (Spine I) A)) ▸ (solo0 Q (1:Patio A)).trans (map_one _)⟩
   | cons i l ih=>
      rw [List.flatMap_cons] at hv ⊢; obtain ⟨h₁,h₂⟩:= ih (fun i hi=> hp i (List.mem_cons_of_mem _ hi)) (List.nodup_append.mp hv).2.1; have hm:= hp i (by simp); rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons]; refine ⟨?_,?_⟩; · rw[List.toFinset_append]; exact (hm.raise Finset.subset_union_left).mul (h₁.raise Finset.subset_union_right)
      rw [voiced Q (W i) (l.flatMap W) _ _ hm h₁ hv,h₂]
lemma song {L:Type} (l:List L)(W:L→List I)(V:L→ ZI)(hp:∀ i∈ l, ValidPieces A Q (W i).toFinset (V i))(hv:(l.flatMap W).Nodup)(x:Patio A): chants Q (l.flatMap W) A ((l.map V).prod * rootR (Spine I) A x)=(l.map fun i=> chants Q (W i) A (V i)).prod*x.val:=by
     let T:=l.flatMap W; obtain ⟨hq,hL⟩:= multiplied Q _ _ V hp hv; change chants Q T _ _=_; rw [show chants Q T A= chants Q (T++[]) A from congr_arg (fun K=>chants Q K A) (List.append_nil ..).symm,voiced Q _ [] _ _ hq (solv Q _) (by simpa using hv),solo0]; rw[hL]; rfl
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.song
