import YM.Oars.Missions
/-! # Joint re-index, options on the actual proof-support, no collision orders implicit -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Function Finset Ribbon Cupola
open scoped Topology BigOperators ContDiff Classical
variable {A B C I J :Type}[Fintype A][Fintype B][Fintype C][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
local notation "Z"=> A⊕R
local notation "X"=> A⊕S
-- permitted schedules: compatible maps at a downward closed family of independent sets
noncomputable def findV (r:I→J→Prop)(s:Finset J) (i:I) : Option J:=if he:∃ j∈s,r i j then some he.choose else none
variable (r:I→J→Prop) (P:Set (Finset J)) (D:Set (Finset I)) -- input restrictions only used thru Lift.E
local notation "Hz"=>findV r
noncomputable def Melts (i:Finset I)(j:Finset J):Prop:= j∈P ∧ Fare (findV r j) i ∧ front (findV r j) i=j
structure Hyp :Prop where
   empty : (∅: Finset J)∈P
   below (i j:Finset J): i∈P → j⊆i → j∈P
   sends (s:Finset J) (i:I)(j k:J): s∈P → j∈s → k∈ s → r i j→ r i k→ j=k
structure Pledge : Prop where
   mast : Hyp r P
   takes (i:I)(j:J): r i j→ q i=p j
   was (i:Finset I)(j:Finset J): Melts r P i j → i∈ D -- ordering inspect
local notation "Y"=>Melts r P
noncomputable def loft (i:Finset I) : Finset (Finset J):= univ.filter (Melts r P i)
local notation "Ω"=> Pledge q p r P D
variable {P}(H:Hyp r P)
include H
lemma findG {s:Finset J}(i:I)(j:J)(he:s∈P): findV r s i=some j ↔ j∈s ∧ r i j:=by
    unfold findV; split
    next h=> exact ⟨fun e=> Option.some.inj e ▸ h.choose_spec,fun hx=> congr_arg some (H.sends s i _ j he h.choose_spec.1 hx.1 h.choose_spec.2 hx.2)⟩
    next h=> exact ⟨fun e=>(by cases e),fun hx=>(h ⟨_,hx⟩).elim⟩
lemma gateM (s t:Finset J)(i:Finset I)(hv:s∈P)(ht:t⊆s)(hf: Fare (Hz t) i) : (∀ a∈i,Hz s a=Hz t a) ∧ Fare (Hz s) i ∧ front (Hz s) i=front (Hz t) i:=by
    have h0(a:I)(h:a∈i): Hz s a=Hz t a:=by
        obtain ⟨j,hj⟩:= Option.ne_none_iff_exists'.1 (hf.2 a h); have he:= (findG r H _ _ (H.below _ _ hv ht)).1 hj; exact ((findG r H _ _ hv).2 ⟨ht he.1,he.2⟩).trans hj.symm
    refine ⟨h0, ⟨fun x hx y hy h=> hf.1 hx hy (by exact Eq.trans (h0 _ hx).symm (h.trans (h0 _ hy))),fun x hx=> h0 x hx |>.symm ▸ hf.2 _ hx⟩,?_⟩; ext j; rw [frontM,frontM]; exact exists_congr fun x=> and_congr_right fun hx=> by rw [h0 _ hx]
lemma frontG (v: Finset J)(s: Finset I)(hv:v∈P): front (Hz v) s⊆ v:=by intro j hj; obtain ⟨k,_,hk⟩:=(frontM (Hz v)).1 hj; exact ((findG r H _ _ hv).1 hk).1
lemma glows (v: Finset J)(s: Finset I)(hv:v∈P) (hs:Fare (Hz v) s): Melts r P s (front (Hz v) s):=by
    let l:=front (Hz v) s; let hp:=H.below v l hv (frontG r H v s hv); have h0(a:I)(ha:a∈s): Hz v a=Hz l a:=by
           obtain ⟨j,hj⟩:= Option.ne_none_iff_exists'.1 (hs.2 a ha); exact hj.trans ((findG r H _ _ hp).2 ⟨(frontM (Hz v)).2 ⟨_,ha,hj⟩, ((findG r H _ _ hv).1 hj).2⟩).symm
    have hF: Fare (Hz l) s:=⟨fun x hx y hy h=> hs.1 hx hy (Eq.trans (h0 _ hx) (h.trans (h0 _ hy).symm)), fun x hx=> h0 x hx ▸ hs.2 _ hx⟩
    exact ⟨hp,hF,(gateM r H v l s hv (frontG r H v s hv) hF).2.2.symm⟩
lemma meeting (i:I)(j:J)(hv:{j}∈P) (h:r i j): Melts r P {i} {j}:=by
   have hg:Hz ({j}:Finset J) i=some j:= (findG r H _ _ hv).2 ⟨mem_singleton_self _,h⟩; exact ⟨hv,by simp [Fare,hg], by ext; simp [frontM,hg,eq_comm]⟩
lemma shrink (i:Finset I)(j:Finset J)(h: Melts r P i j)(x: Finset I)(he:x⊆i): let s:=front (Hz j) x; Melts r P x s:=by
    intro s; apply glows r H j x h.1 ⟨h.2.1.1.mono he,fun i hi=> h.2.1.2 _ (he hi)⟩
omit H
variable {D}(h:Pledge q p r P D)
local notation "G"=>Sample.flame A q p
local notation "λg"=>leaves A q p
local notation "G!" t=>G (Hz t) g -- syntax use
local notation "L!" i=> loft r P i
include h
lemma hym (j:Finset J)(hv:j∈P)(a:I)(i:J)(ht: Hz j a=some i):q a=p i:= h.takes a i ((findG r h.mast _ _ hv).1 ht).2
lemma countT (j:Finset J)(s:Finset I)(hs:Melts r P s j)(x:Patio Z)(hp:Polite q s x) : Polite p j ((G! j) x) ∧ ∃ c:ℂ, ‖c‖=‖purse (Hz j) g s‖∧ pluck A (burst p j) ((G! j) x)=c • pluck A (burst q s) x:=by
    obtain ⟨c,hx,hX⟩:= flameStake A q p _ g (hym q p r h j hs.1) s x hp hs.2.1; rw [hs.2.2] at hX
    exact ⟨⟨_,hX.symm⟩, c,hx,(congr_arg (scrape A (burst p j)) hX).trans (quid ..)⟩
lemma shineR {u:Finset J}(hv:u∈P)(a:Finset I)(x:Finset J)(hx:x⊆u)(hF:Fare (Hz x) a) : λg (Hz x) g (quill A (mono (burst q a)))=λg (Hz u) g (quill A (mono (burst q a))):=by
     have hp(a:I)(j:J)(hj:r a j) : q a=p j:= h.takes a j hj; let H:= h.mast; induction a using Finset.induction_on with
     | empty=>simp
     | insert i s hi ih=>
       have hf:= ih (show Fare (Hz x) s from ⟨hF.1.mono (show (s:Set I) ⊆ ↑(insert i s) from coe_subset.mpr (subset_insert ..)),fun t ht=> hF.2 _ (mem_insert_of_mem ht)⟩)
       obtain ⟨j,hj⟩:=Option.ne_none_iff_exists'.1 (hF.2 i (mem_insert_self ..)); have hq:= hym q p r h x (H.below _ _ hv hx) i j hj; have hA:= (gateM r H u x _ hv hx hF).1 i (mem_insert_self ..)
       rcases stave q hi with hX|hX <;> simp only [hX,map_neg,map_mul,hf, leaving A q p (Hz x) g _ _ hj hq,leaving A q p (Hz u) g _ _ (hA.trans hj) hq]
lemma fareSum {u:Finset J}(hv:u∈P)(a:Finset I)(x:Patio (A⊕Spine I))(hp:Polite q a x) : shutter A u (∑ i∈(L! a), (G! i) x)=(G! u) x:=by
    rw [map_sum]; by_cases he:Fare (Hz u) a
    · let d:=front (Hz u) a; have hD:= glows r h.mast u a hv he; have hf:d⊆u:= frontG r h.mast u a hv; have hφ:= shineR A q p g r h hv a d hf hD.2.1 -- binder order g before r
      rw [sum_eq_single d]; swap
      · intro i hi hi'; have hI:= (mem_filter.mp hi).2; have hp':¬ i⊆u:=fun he=> hi' ((((gateM r h.mast u i a hv he hI.2.1).2.2).trans hI.2.2).symm); rw [stamen_h A p i _ _ (countT A q p g r h i a hI x hp).1,if_neg hp']
      rotate_left; · exact fun h=>False.elim (h (mem_filter.mpr ⟨mem_univ _,hD⟩))
      rw [stamen_h A p _ _ _ (countT A q p g r h _ _ hD x hp).1,if_pos hf]; apply Subtype.ext; change λg (Hz d) g x.val= λg (Hz u) g x.val; rw [← hp.exact,markedOut,map_mul,map_mul,hφ]; apply congr_arg (·*_); exact (by rw [leaves,leaves,AlgHom.comp_apply,AlgHom.comp_apply,tarfib,tarfib,blot_left,blot_left])
    rw [latentF _ _ _ _ _ (hym q p r h u hv) a x hp he]; apply sum_eq_zero; intro i hi; have ht:= (mem_filter.mp hi).2; rw [stamen_h A p i _ _ (countT _ _ _ g r h i a ht x hp).1,if_neg (fun hp'=>he ((gateM r h.mast u i a hv hp' ht.2.1).2.1))]
-- Version after discarding O old.Set
lemma portR (a:Finset I)(u:Finset J)(t:Patio Z)(hv:u∈P)(hp:Polite q a t)(hx:a ∉ D) : (G! u) t=0:=latentF A q p (Hz u) g (hym q p r h u hv) _ _ hp (fun he=> hx (h.was _ _ (glows r h.mast u a hv he)))
lemma edgeS (i:I)(j:J)(s:Finset J)(hv:s∈P)(hS:j∈s)(hx:r i j)(x: Patio Z)(hp:Polite q {i} x): Cove.light X ((G! s) x)= (↑(g i j):ℂ) • stake A (burst p {j}) (pluck A (burst q {i}) x):=by
     change λg (Hz s) g x.val = _; nth_rw 1 [← hp.exact]; rw [markedOut,markedOut,map_mul,leaving A q p _ g _ j ((findG r h.mast _ _ hv).2 ⟨hS,hx⟩) (h.takes _ _ hx),mul_smul_comm,leaves,AlgHom.comp_apply,tarfib,blot_left]; rfl
end YM.MassiveQCD.Sample
