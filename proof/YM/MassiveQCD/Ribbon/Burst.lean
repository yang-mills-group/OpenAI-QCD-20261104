import YM.MassiveQCD.Ribbon.Lifts
import YM.MassiveQCD.Ribbon.Rates
/-!
# Source masks, square-zero, designated sign posture
 No positivity estimate for the marker storage; use cone on ACTUAL fields.
 No extra projections for this phase (sub-ideal pruning separately).
 Henry's all-grades value balance uses carried support/sharp costs, not supremum
 of mixture once spins deleted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Cove QCD.Creek Function Finset Filter
open scoped Topology ContDiff BigOperators Classical
variable {A I:Type} [Fintype A] [Fintype I]
abbrev Spine (I:Type):= (I×Bool)× Fin 3
variable (q:I→Bool)
noncomputable def post (s:Finset I): Finset (I×Bool):= (s×ˢ({false}))∪((s.filter fun i=>q i=false)×ˢ({true}))
noncomputable def burst (s:Finset I): Finset (Spine I):=post q s ×ˢ univ
section test
omit [Fintype I]
lemma place (i:I)(s:Finset I): i∈s ↔ ((i,false),0)∈ burst q s:=by simp [burst,post]
lemma located (s:Finset I)(i)(h:i ∈ burst q s): i.1.1 ∈ s:= by
    have he:= (mem_product.mp h).1; unfold post at he; rcases mem_union.mp he with he|he
    · exact (mem_product.mp he).1
    exact (mem_filter.mp (mem_product.mp he).1).1
@[simp] lemma postZero : post q ∅=∅:= by ext i; simp [post]
@[simp] lemma burst_absent : burst q ∅=∅:=by simp [burst]
lemma burstUnique : Injective (burst q):=fun s t he=>by ext i; rw [place q i s,place q i t,he]
lemma pulver (s t:Finset I): burst q (s∪t)= burst q s∪burst q t:= by ext ⟨⟨i,b⟩,j⟩; cases b <;> simp [burst,post] ; tauto
lemma crossedR (s t:Finset I): Disjoint (burst q s) (burst q t)↔ Disjoint s t:=
 ⟨fun h=>Finset.disjoint_left.mpr (fun i hp ht=>Finset.disjoint_left.mp h ((place q i s).1 hp) ((place q i t).1 ht)),fun h=>Finset.disjoint_left.mpr (fun _ hp ht=>Finset.disjoint_left.mp h (located q _ _ hp) (located q _ _ ht))⟩
lemma onePost (s:I): (burst q {s}).card=if q s then 3 else 6:=by
    unfold burst post; rw [Finset.card_product]; split
    next h=>simp [h]
    next h=>
       have hp:q s=false:=Bool.eq_false_iff.2 h
       have he (b:Bool):({s}:Finset I)×ˢ({b})={(s,b)}:=by ext ⟨i,j⟩; simp
       rw [show Finset.filter _ {s} = {s} from by ext i; simp; rintro rfl; exact hp]; simp [he]
lemma flavor (s:I): shade (burst q {s})=q s:=by rw [shade,onePost]; cases q s<;> decide
lemma burstPos {s:Finset I}(h:s.Nonempty) : (burst q s).Nonempty:=by obtain ⟨i,h⟩:=h; exact ⟨((i,false),0),(place q i s).mp h⟩
end test
noncomputable def Polite (s:Finset I)(x: Patio (A⊕Spine I)) : Prop:= light _ x ∈ (stake A (burst q s)).toLinearMap.range
variable {s t:Finset I} {x y:Patio (A⊕Spine I)}
variable {q}
lemma Polite.exact (h:Polite q s x) : stake A (burst q s) (scrape A (burst q s) x.val)=x.val:=by
    obtain ⟨z,h⟩:=h; change stake A _ z=_ at h; have hd : x.val= stake A (burst q s) z:= h.symm; rw [hd,quid]
lemma Polite.spectral (h:Polite q s x)(t:Finset (Spine I))(he:t≠burst q s) : scrape A t x.val=0:=by nth_rw 1 [← h.exact]; rw [stakesX,if_neg he]
lemma Polite.of_ranges (he:∀ t:Finset (Spine I), t≠ burst q s → scrape A t x.val=0): Polite q s x:=by
   refine ⟨(scrape A (burst q s) x.val),?_⟩; apply vista A; intro i; by_cases h : i=burst q s
   · subst i; exact quid ..
   exact (stakesX A i _ _).trans ((if_neg h).trans (he i h).symm)
lemma polite_nil (q:I→Bool)(s:Finset I) : Polite q s (A:=A) 0:=by unfold Polite; rw [map_zero]; exact Submodule.zero_mem _
lemma Polite.smooch (h:Polite q s x) (a:ℂ): Polite q s (a • x):=by unfold Polite; rw [map_smul]; exact Submodule.smul_mem _ a h
lemma polite_empty_one (q:I→Bool): Polite q (A:=A) ∅ 1:= by unfold Polite; rw [burst_absent]; exact ⟨1,(quiet A 1).trans (map_one _)⟩
lemma Polite.minus (h:Polite q s x) : Polite q s (-x):=by unfold Polite; rw [map_neg]; exact Submodule.neg_mem _ h
lemma Polite.lays (h:Polite q s x)(he:Polite q s y): Polite q s (x+y):=by unfold Polite; rw [map_add]; exact Submodule.add_mem _ h he
lemma politeSpace (q:I→Bool)(s:Finset I) : IsClosed {x: Patio (A⊕Spine I)| Polite q s x}:=by
    let P:= LinearMap.range (stake A (burst q s)).toLinearMap; exact (P.closed_of_finiteDimensional).preimage (lightC _)
lemma polite_tsum {J:Type}{x:J→ Patio (A⊕Spine I)}(h:∀ i,Polite q s (x i)): Polite q s (∑' i,x i):=by
    by_cases he:Summable x; swap; · rw [tsum_eq_zero_of_not_summable he]; exact polite_nil ..
    have hh (p:Finset J): Polite q s (∑ i∈p,x i):=by unfold Polite; rw [map_sum]; exact Submodule.sum_mem _ (fun _ _=> h _)
    exact (politeSpace q s).mem_of_tendsto he.hasSum (Eventually.of_forall hh)
lemma double_stamp (s t:Finset I)(x y: Alg A): let z:=x*(if shade (burst q s) then grade y else y); let u:=stake A (burst q s) x * stake A (burst q t) y; if Disjoint s t then (u=stake A (burst q (s∪t)) z ∨ u= -stake A (burst q (s∪t)) z) else u=0 :=by
    intro z u; unfold u; rw [wheel]; split
    next h=> rcases mono_mul_sign _ _ ((crossedR q s t).mpr h) with hp|hp <;> rw [Finset.disjUnion_eq_union,← pulver] at hp; exact Or.inl (by rw [hp]; exact rfl); exact Or.inr (by rw [hp,map_neg,mul_neg]; exact rfl)
    next h=> rw [mono_mul_zero _ _ (fun hv=> h ((crossedR q s t).mp hv)),map_zero,mul_zero]
lemma Polite.nilpotent (h:Polite q s x)(he:Polite q t y)(hv:¬ Disjoint s t): x*y=0:=by
    apply Subtype.ext; change x.val*y.val=0; have hh:= double_stamp (q:=q) s t (scrape A (burst q s) x.val) (scrape A (burst q t) y.val)
    rw [← h.exact,← he.exact]; exact (if_neg hv ▸ hh : _) -- edit
lemma Polite.attached (h:Polite q s x)(he:Polite q t y) : Polite q (s∪t) (x*y):=by
    by_cases ht: Disjoint s t; swap; · rw [h.nilpotent he ht]; exact polite_nil ..
    have hh:= double_stamp (q:=q) s t (scrape A (burst q s) x.val) (scrape A (burst q t) y.val); dsimp only at hh; rw [if_pos ht,h.exact,he.exact] at hh -- rewrite eats nested? 
    rcases hh with hh|hh
    · exact ⟨_,hh.symm⟩
    let t':=scrape A (burst q s) x.val * (if shade (burst q s) then grade (scrape A (burst q t) y.val) else scrape A (burst q t) y.val)
    exact ⟨-t',(map_neg (stake A (burst q (s∪t))) t').trans hh.symm⟩
end YM.MassiveQCD.Ribbon
