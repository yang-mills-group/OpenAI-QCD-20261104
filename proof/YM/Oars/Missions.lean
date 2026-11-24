import YM.Oars.Apogee
/-! # Partial drawing exact direction and cost -/
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
local notation "le"=>Sample.leaves A q p f g
local notation "U"=>Sample.flame A q p f g
lemma abandon (i:I)(h:f i=none) : Sample.leaves A q p f g (quill A (mono (burst q {i})))=0:=by
    have hp(t:Finset R) := tarStake A (slot q p f g) 1 t
    simp_rw [markedOut,map_one,one_mul] at hp; rw [leaves,AlgHom.comp_apply,hp,map_smul]; apply Eq.trans _ (smul_zero (Cupola.pole (slot q p f g) (burst q {i}))); apply congr_arg
    -- kill via any leg
    let t:=((i,false), (0:Fin 3)); let s:=burst q {i}; have hv:t∈s:= (place q i _).1 (mem_singleton_self _); let G:= changeVars (blot A f); have hg : G (quill A (mono {t}))=0:=by rw [mono_single,embed_atom]; unfold G; rw [change_atom,Fintype.sum_sum_type]; simp [blot,t,h,stencil]
    -- mono factors
    have hT: Disjoint ({t}:Finset R) (s.erase t):= disjoint_singleton_left.mpr (notMem_erase t s)
    have hS:= mono_mul_sign _ _ hT; rw [Finset.disjUnion_eq_union,singleton_union,insert_erase hv] at hS
    rcases hS with e|e
    · change G (quill A (mono s)) = _; rw [← e,map_mul,map_mul,hg,zero_mul]
    change G (quill A (mono s)) = _; rw [← neg_eq_iff_eq_neg.mpr e,map_neg,map_neg,map_mul,map_mul,hg,zero_mul,neg_zero] -- orientation
-- success sets
variable (h:∀ i j,f i=some j→q i=p j)
noncomputable def Fare (s:Finset I):Prop:= Set.InjOn f (s:Set I) ∧ ∀ i∈s,f i≠none
noncomputable def front (s:Finset I):Finset J:= univ.filter fun j=>some j ∈ s.image f
lemma frontM {s:Finset I}{i:J}: i∈front f s ↔ ∃ k∈s,f k=some i:=by simp only [front, mem_filter,mem_univ,mem_image,true_and]
noncomputable def purse (s:Finset I):ℂ:=∏ i∈s,(↑((f i).elim 0 (fun j=>g i j)):ℂ)
lemma stave (q:I→Bool){s:Finset I}{i:I}(h:i ∉ s): mono (burst q (insert i s))= mono (burst q {i})*mono (burst q s) ∨ mono (burst q (insert i s))=-(mono (burst q {i})*mono (burst q s)):=by
    have hd : Disjoint {i} s:= disjoint_singleton_left.mpr h
    have h:= mono_mul_sign _ _ ((crossedR q {i} s).mpr hd); rw [Finset.disjUnion_eq_union, ← pulver,singleton_union] at h; exact h.imp Eq.symm (fun e=>(neg_eq_iff_eq_neg.mpr e).symm)
include h
local notation "λq"=> leaves A q p f g
local notation "Κ"=> quill A
-- orientation scalar exact
lemma poke (s:Finset I)(he:Fare f s):∃ a:ℂ, (a=1 ∨ a= -1) ∧ λq (Κ (mono (burst q s)))=(a*purse f g s) • Κ (mono (burst p (front f s))):=by
    induction s using Finset.induction_on with
    | empty=> exact ⟨1,Or.inl rfl,by simp [front,purse]⟩
    | insert i s hi ih=>
      have hs:= he.1; have hN:= he.2; obtain ⟨j,hj⟩:=((Option.ne_none_iff_exists').1 (hN i (mem_insert_self _ _))) -- iff name
      obtain ⟨a,ha,hx⟩:= ih ⟨hs.mono (Finset.coe_subset.mpr (subset_insert ..)),fun t ht=> hN t (mem_insert_of_mem ht)⟩
      let X':=mono (burst p {j}); let Y':=mono (burst p (front f s)); have ht : j∉ front f s:=fun hk=> (frontM f).1 hk|>.elim (fun k he=>hi ((hs (mem_insert_of_mem he.1) (mem_insert_self ..) (he.2.trans hj.symm)) ▸ he.1));
      have hb : front f (insert i s) = insert j (front f s):=by ext k; simp [frontM,hj,eq_comm]
      rw [hb,purse,prod_insert hi,hj,Option.elim_some]; have hq:= leaving A q p f g i j hj (h _ _ hj)
      rcases stave q hi with hs|hs <;> rcases stave p ht with hP|hP
      · refine ⟨a,ha,?_⟩; rw [hs,map_mul,map_mul,hq,hx,hP,map_mul]; exact (by rw [smul_mul_assoc,mul_smul_comm,smul_smul]; congr 1; unfold purse; ring)
      · refine ⟨-a,by rcases ha with h|h <;> simp [h],?_⟩; rw [hs,map_mul,map_mul,hq,hx,hP,map_neg,map_mul]; exact (by rw [smul_mul_assoc,mul_smul_comm,smul_smul,neg_mul,smul_neg,neg_smul,neg_neg]; congr 1; unfold purse; ring)
      · refine ⟨-a,by rcases ha with h|h <;> simp [h],?_⟩; rw [hs,map_neg,map_neg,map_mul,map_mul,hq,hx,hP,map_mul]; rw [smul_mul_assoc,mul_smul_comm,smul_smul,neg_mul,neg_smul]; congr 2; unfold purse; ring
      refine ⟨a,ha,?_⟩; rw [hs,map_neg,map_neg,map_mul,map_mul,hq,hx,hP,map_neg,map_mul]; rw [smul_mul_assoc,mul_smul_comm,smul_smul,smul_neg]; congr 2; unfold purse; ring
lemma latent (s:Finset I)(he:¬ Fare f s): λq (Κ (mono (burst q s)))=0:=by
    induction s using Finset.induction_on with
    | empty => exfalso; apply he; simp [Fare]
    | insert i s hi ih=>
      by_cases hv:f i=none; · rcases stave q hi with hT|hT <;> simp only [hT,map_neg,map_mul,abandon A q p f g i hv,zero_mul,neg_zero]
      by_cases hx: Fare f s; swap; · rcases stave q hi with hT|hT <;> simp only [hT,map_neg,map_mul, ih hx,mul_zero,neg_zero]
      obtain ⟨a,ha,hx'⟩:= poke A q p f g h s hx
      obtain ⟨j,hj⟩:= (Option.ne_none_iff_exists').1 hv
      have hk : j∈front f s:=by
           by_contra H; apply he; obtain ⟨h1,h2⟩:=hx; have hN (t:I)(ht:t∈s): f t≠ some j:=fun hh=>H ((frontM f).2 ⟨_,ht,hh⟩); refine ⟨fun x hx y hy hf=>?_,fun t ht=> (mem_insert.mp ht).elim (fun e=>e.symm ▸ hv) (h2 t)⟩; rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with gH|hy
           · exact gH.symm
           · exact (hN y hy (hf.symm.trans hj)).elim
           · exact (hN x hx (by rw [←gH, ← hf] at hj; exact hj)).elim
           exact h1 hx hy hf
      have ht:= mono_mul_zero (burst p {j}) (burst p (front f s)) (fun h=> disjoint_singleton_left.mp ((crossedR p {j} _).mp h) hk) -- args
      rcases stave q hi with hh|hh <;> simp only [hh,map_neg,map_mul,hx',leaving A q p f g i j hj (h _ _ hj),smul_mul_assoc,mul_smul_comm] <;> rw [← map_mul (quill A),ht,map_zero,smul_zero,smul_zero] <;> simp
lemma flameStake (s:Finset I)(x: Patio Z)(hp:Polite q s x)(he:Fare f s):∃ c:ℂ, ‖c‖=‖purse f g s‖ ∧ Cove.light X (U x) = stake A (burst p (front f s)) (c • pluck A (burst q s) x):=by
    obtain ⟨a,ht,hΦ⟩:= poke A q p f g h s he; refine ⟨a*purse f g s,?_,?_⟩; swap
    · change λq x.val = _; nth_rw 1 [← hp.exact]; rw [markedOut,map_mul, hΦ,mul_smul_comm,markedOut,map_smul,smul_mul_assoc,show λq (fiber R _)=_ from (by rw [leaves,AlgHom.comp_apply,tarfib,blot_left])] -- RHS mv.W
      rfl
    rcases ht with rfl|rfl <;> simp
lemma latentF (s:Finset I)(x:Patio Z)(hp:Polite q s x)(he:¬Fare f s) : U x=0:=by
    apply Subtype.ext; change λq x.val=0; rw [← hp.exact,markedOut,map_mul,latent _ _ _ _ _ h s he,mul_zero]
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.latentF
#print axioms YM.MassiveQCD.Sample.flameStake
