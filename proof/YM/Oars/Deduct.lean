import YM.Oars.StarFall
/-! # Cost of many options at common addresses -/
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
-- use cardinal option estimates δ=?, geometric counting compiler
variable (r:I→J→Prop) {P:Set (Finset J)} (hp:Hyp r P)
local notation "Y"=>Melts r P
noncomputable def opts (i:I):= Finset.univ.filter (r i)
local notation "Ω" a=> loft r P a
lemma singletonAll {i:I}{j:J}{s:Finset J}(h:Melts r P {i} s)(he:some j=findV r s i) : s={j}:=by ext u; rw [← h.2.2,frontM]; simp only [mem_singleton,exists_eq_left,←he, Option.some.injEq]; exact eq_comm
include hp
lemma solo (i:I)(j:J)(hx:Melts r P {i} {j}) : r i j:=by
    obtain ⟨b,hb⟩:= Option.ne_none_iff_exists'.1 (hx.2.1.2 i (mem_singleton_self ..)); have hg: b=j:=mem_singleton.mp ((findG r hp i b hx.1).1 hb).1; exact hg ▸ ((findG r hp i b hx.1).1 hb).2
noncomputable def interlude (i:Finset I)(j:↥(loft r P i))(u:↥i): ↥(opts r u.val):=by
    let s:=j.val; have hM: Melts r P i s:= (mem_filter.mp j.property).2; have h:=hM.2.1.2 u.val u.property
    let a:= Option.ne_none_iff_exists'.1 h; exact ⟨a.choose,mem_filter.mpr ⟨mem_univ _, ((findG r hp _ _ hM.1).1 a.choose_spec).2⟩⟩ -- `include hp` automatically appended? use as var bound.
lemma interplays (i: Finset I)(j:↥(loft r P i))(u:↥i): findV r j.val u.val=some (interlude r hp i j u).val:= Option.ne_none_iff_exists'.1 ((show Melts r P i j.val from (mem_filter.mp j.property).2).2.1.2 _ u.property) |>.choose_spec
lemma worldM (z:Finset J)(_hv:z∈P)(i:Finset I)(h:Melts r P i z) : z.card=i.card:=by
    rw [← h.2.2]; let s:= front (findV r z) i; let o:i→ s:= fun u : ↥i => ⟨(interlude r hp i (⟨z,mem_filter.mpr ⟨mem_univ _,h⟩⟩) u).val, (frontM _).2 ⟨_,u.property, interplays r hp i ⟨z,mem_filter.mpr ⟨mem_univ _,h⟩⟩ u⟩⟩
    have he(u): findV r z (u:↥i).val=some (o u).val:= interplays r hp i ⟨z,mem_filter.mpr ⟨mem_univ _,h⟩⟩ u
    have hB : Function.Bijective o:=by
      refine ⟨fun u v e=>?_ ,?_⟩; · exact Subtype.ext (h.2.1.1 u.property v.property (by rw [he u,he v,e]))
      intro w; obtain ⟨j,hj,hg⟩:= (frontM _).1 w.property; let v:↥i:=⟨j,hj⟩; exact ⟨v,Subtype.ext (Option.some.inj ((he v).symm.trans hg))⟩
    change s.card = _; exact Fintype.card_coe s ▸ Fintype.card_coe i ▸ (Fintype.card_congr (Equiv.ofBijective o hB)).symm -- cast
lemma recycle (i:Finset I)(j:↥(loft r P i)):j.val= i.attach.image (fun u=>(interlude r hp i j u).val):=by
    have hz: ↑j∈ loft r P i:= j.property; have hv:= ((mem_filter.mp hz).2 : Melts r P i j.val); ext p; rw [mem_image]; constructor
    · intro hx; obtain ⟨k,hk,hk'⟩:=(frontM _).1 (hv.2.2.symm ▸ hx); let u:↥i:=⟨k,hk⟩; exact ⟨u,mem_attach ..,Option.some.inj ((interplays r hp i j u).symm.trans hk')⟩
    rintro ⟨a,hA,rfl⟩; exact (findG r hp _ _ hv.1|>.1 (interplays r hp i j a)).1
lemma cardLo (i:Finset I)(N:ℕ)(h:∀ a∈i,(opts r a).card≤ N): (Ω i).card ≤ N^i.card:=by
   have he: Injective (interlude r hp i):= fun x y e=> Subtype.ext ((recycle r hp _ _).trans (by rw [e]; exact (recycle r hp _ _).symm))
   have hk:= Fintype.card_le_of_injective (interlude r hp i) he; rw [Fintype.card_coe,Fintype.card_pi] at hk; exact hk.trans ((prod_le_prod (fun _ _=>Nat.zero_le _) (fun i _=> by simpa using h i.val i.property)).trans_eq (by rw [prod_const,Finset.card_univ,Fintype.card_coe])) -- simpa syntax
variable {v:ℝ}
lemma wears (x:Finset I)(y:Finset J)(h:Melts r P x y)(hw:∀ a∈x,∀ j,r a j→ |g a j|≤ v): ‖purse (findV r y) g x‖ ≤ v^x.card:=by
   unfold purse; rw [norm_prod]; apply (prod_le_prod (fun _ _=>norm_nonneg _) ?_).trans_eq (prod_const v); intro i hi; obtain ⟨j,hj⟩:=Option.ne_none_iff_exists'.1 (h.2.1.2 i hi); rw [hj, Option.elim_some,Complex.norm_real,Real.norm_eq_abs]; exact hw _ hi j (((findG r hp _ _ h.1).1 hj).2)
lemma duties (N:ℕ)(he:∀ i,(opts r i).card ≤ N)(x:Finset I) (hw:∀ a∈x,∀ j,r a j→ |g a j|≤ v)(hv:0≤v): ∑ j ∈ loft r P x, ‖purse (findV r j) g x‖≤(↑N*v)^x.card:=by
    refine (sum_le_sum (g:=fun _=>v^x.card) fun i hi=>wears g r hp x i (mem_filter.mp hi).2 hw).trans ?_
    rw [sum_const,nsmul_eq_mul,mul_pow]; gcongr
    exact_mod_cast (cardLo r hp x N (fun _ _=>he _)) -- gcongr shape
end YM.MassiveQCD.Sample
