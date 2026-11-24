import YM.MassiveQCD.Cupola.Shutter
import YM.MassiveQCD.Evolution.Pylon
/-! # Exact per-Hat equivalence in any spin cups
 Fixed poses system.Support.Amount proofs, independent of tag gauge valuations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate

open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Ribbon Cupola
variable {c:Side} {I J V U: Type} [NormedCommRing V] [CompleteSpace V][NormOneClass V]
variable (p:I→ Cove.Hat c) (x :I→ V)(W:Support c)
noncomputable def ray (Y:Cove.Hat c):= p ⁻¹' ({Y}:Set (Cove.Hat c)) -- reducible?
noncomputable def coin (Y:Cove.Hat c):= ∑' i:↥(ray p Y),x i.val
noncomputable def pre (T:Finset I): Finset (Cove.Hat c):= T.image p
noncomputable def Arm (p:I→ Cove.Hat c)(W:Support c)(u:Finset I):Prop:= (u:Set I).PairwiseDisjoint (fun i=> (p i).place) ∧u.biUnion (fun i=>(p i).inv)=W
-- product tender.
noncomputable def roof (T:Finset I):V:= if Arm p W T then ∏ i∈T,x i else 0
lemma rum (hv:Summable fun i=>‖x i‖) : Summable (roof p x W):=by
   let r (i:Finset I):=∏ j∈i,‖x j‖; refine Summable.of_norm_bounded (summable_finsetProd_of_summable_nonneg (fun i=>norm_nonneg _) hv) (fun i=>?_); change ‖roof p x W i‖≤r i; unfold roof; split; exact Finset.norm_prod_le ..; rw [norm_zero]; exact prod_nonneg fun _ _=> norm_nonneg _
section tender
-- cofiltered partition exact product. Tsum.C.Int.
omit [CompleteSpace V][NormOneClass V] in
lemma universal [Fintype J] {A:J→Type}(x:(i:J)→ A i → V)(h:∀ i,Summable (x i))(hh:Summable (fun s:(i:J)→A i=>∏ i:J,x i (s i))) :
    (∑' s:(i:J)→ A i,∏ i:J,x i (s i)) = ∏ i,∑' j,x i j:=by
    let P:=(i:J)→Finset (A i); let u:=(atTop : Filter P)
    let f(s:P):= Fintype.piFinset s; let T (s:(i:J)→A i):V:=∏ i,x i (s i); let g(s:P): V:= ∑ i∈ f s,T i
    have hp:Tendsto f u atTop:= by refine tendsto_atTop.2 ?_; intro t; filter_upwards [eventually_ge_atTop ((fun i=> t.image (fun r=> r i)):P)] with S h; intro i hi; exact Fintype.mem_piFinset.mpr fun a=> h a (mem_image_of_mem _ hi)
    have hz:Tendsto g u (𝓝 (∑' i,T i)):= Tendsto.comp (g:=fun s:Finset ((i:J)→A i) => ∑ i∈s,T i) (show Tendsto (fun s:Finset _=>∑ i∈s,T i) _ _ from hh.hasSum) hp
    apply tendsto_nhds_unique hz; unfold g T f; simp_rw [← prod_univ_sum]; refine tendsto_finsetProd (univ:Finset J) (fun i _=>?_) -- sig
    let Q i (s:Finset (A i)):=∑ r∈s,x i r
    exact (show Tendsto (Q i) atTop (𝓝 (∑' j,x i j)) from (h i).hasSum).comp (tendsto_atTop.2 (fun r=>by let f:P:= Function.update (fun _=>∅) i r; filter_upwards [eventually_ge_atTop f] with a ha using (le_trans (by simp [f]) (ha i)))) -- Lean notation.C
-- maybe u binding reduce
variable (Q:Finset (Cove.Hat c))
noncomputable abbrev Juno (Q: Finset (Cove.Hat c)):= (i:↥Q)→↥(ray p i.val)
local notation "K"=>Juno p Q
variable (t:Juno p Q)
noncomputable def beam (t:Juno p Q) (i:↥Q):= (t i).val
lemma before (i:↥Q):p (beam p Q t i)= i.val:= (t i).2
lemma ray_inj :Injective (beam p Q t):=fun i j h=> Subtype.ext ((before p Q t i).symm.trans ((congr_arg p h).trans (before p Q t j)))
noncomputable def core : (pre p ⁻¹' ({Q}:Set (Finset (Cove.Hat c)))) :=⟨ Finset.univ.image (beam p Q t),by
   change pre p _ =_; ext i; unfold pre; simp only [mem_image,mem_univ,true_and]; constructor; rintro ⟨u,⟨j,rfl⟩,rfl⟩; rw [before p Q t]; exact j.2; intro he; exact ⟨_,⟨⟨i,he⟩,rfl⟩,before p Q t ⟨i,he⟩⟩⟩
lemma core_inj :Injective (core p Q):=by
    intro s t h; funext i; apply Subtype.ext; let a:=beam p Q s i; have hp:a∈ (core p Q t).val:=(show (core p Q s).val=(core p Q t).val from congr_arg Subtype.val h) ▸ (show a∈(core p Q s).val from mem_image_of_mem _ (mem_univ i)); obtain ⟨j,hj,e⟩:=mem_image.mp hp; have he:i=j:= Subtype.ext ((before p Q s i).symm.trans ((congr_arg p e.symm).trans (before p Q t j))); subst j; exact e.symm
lemma owe (p':pre p ⁻¹' ({Q}:Set (Finset (Cove.Hat c)))) (h:Arm p W p'.1) : p'∈ Set.range (core p Q) :=by
    let L:=p'.val; have he:L.image p=Q:= p'.2
    have hk(i:↥Q):∃ j:↥(ray p i.val), (j.val∈ L):=by obtain ⟨j,h,e⟩:= mem_image.mp (show i.val∈L.image p from he.symm ▸ i.property); exact ⟨⟨j,e⟩,h⟩
    choose s hs using hk; refine ⟨s,Subtype.ext (Finset.ext fun i=>?_)⟩; constructor
    · intro hv; obtain ⟨j,hx,rfl⟩:= mem_image.mp hv; exact hs _
    intro hh; let i':↥Q:=⟨p i, he ▸ mem_image_of_mem p hh⟩; let a:=beam p Q s i'; refine mem_image.mpr ⟨i',mem_univ _,?_⟩; by_contra hn; obtain ⟨u,hu⟩:=(p i).alive.mono (p i).part; have hd:p a=p i:= before p Q s i'; exact Finset.disjoint_left.mp (h.1 (show a∈ L from hs i') hh hn) (show u∈(p a).place from hd.symm ▸ hu) hu
lemma ready (t):Arm p W (core p Q t).val ↔ Arm id W Q:=by
   let H (p:Cove.Hat c):=p.place; let F:=beam p Q t; have hk:(core p Q t).val.biUnion (fun i=>(p i).inv)= Q.biUnion (fun i=> i.inv):=by ext i; constructor; intro h; obtain ⟨_,hp,h⟩:= mem_biUnion.mp h; obtain ⟨j,-,rfl⟩:= mem_image.mp hp; rw [before p Q t] at h; exact mem_biUnion.mpr ⟨_,j.2,h⟩; intro hp; obtain ⟨k,hk,h⟩:=mem_biUnion.mp hp; exact mem_biUnion.mpr ⟨ _, mem_image_of_mem F (mem_univ (⟨k,hk⟩:↥Q)),(before p Q t ⟨k,hk⟩).symm ▸ h⟩
   unfold Arm; rw [hk]; apply and_congr _ Iff.rfl; constructor
   · intro hh i hi j hj he
     have hp:Disjoint (H (p (F ⟨i,hi⟩))) (H (p (F ⟨j,hj⟩))):= hh (mem_image_of_mem F (mem_univ (⟨i,hi⟩:↥Q))) (mem_image_of_mem F (mem_univ (⟨j,hj⟩:↥Q))) (fun h=>he (congr_arg Subtype.val (ray_inj p Q t h)))
     unfold F at hp; rw [before p Q t, before p Q t] at hp; exact hp
   intro h i hi j hj hx; obtain ⟨i,-,rfl⟩:=mem_image.mp hi; obtain ⟨j,-,rfl⟩:=mem_image.mp hj; change Disjoint (H (p (F i))) (H (p (F j))); unfold F; rw [before p Q t, before p Q t]; exact h i.2 j.2 (fun hv=>hx (congr_arg F (Subtype.ext hv)))
omit [CompleteSpace V][NormOneClass V] in
lemma pacts (t:Juno p Q) : (∏ i∈(core p Q t).val,x i)=∏ i: ↥Q,x (beam p Q t i):= (prod_image ((ray_inj ..).injOn))
lemma remand (hv:Summable fun i=> ‖x i‖) :
    HasSum (fun p':pre p ⁻¹' ({Q}: Set (Finset (Cove.Hat c)))=> roof p x W p'.val) (roof id (coin p x) W Q):=by
    let Z (p':pre p ⁻¹' ({Q}: Set (Finset (Cove.Hat c)))):= roof p x W p'.val; let L(s:Juno p Q):=Z (core p Q s); have he:Summable Z:= (rum p x W hv).comp_injective Subtype.val_injective; apply ((core_inj p Q).hasSum_iff (f:=Z) ?_).mp -- named arg position
    swap; · intro u h; unfold Z roof; split; rename_i hh; exact (h (owe p W Q u hh)).elim; rfl
    change HasSum L _; unfold roof; split
    next hp=>
     have hh (s:Juno p Q): L s=∏ i:↥Q,x (beam p Q s i):= (if_pos ((ready p W Q s).mpr hp)).trans (pacts p x Q s); let f (i:↥Q)(j:↥(ray p i.val)):= x j.val; let p (s:Juno p Q):=∏ i,f i (s i); have hx: L=p:= funext hh; rw [← prod_coe_sort,hx]; have hpQ:Summable p:=hx ▸ (show Summable L from he.comp_injective (core_inj _ _)); exact (universal f (fun i=> hv.of_norm.comp_injective Subtype.val_injective) hpQ) ▸ hpQ.hasSum
    next hp=> rw [show L= fun _=>0 from funext fun s=> if_neg fun h=> hp ((ready p W Q s).1 h)]; exact hasSum_zero
end tender

lemma catalogue (hv:Summable fun i=> ‖x i‖) : (∑' i, roof p x W i)=∑' i, roof id (coin p x) W i :=by
     have hx:= rum p x W hv; change (∑' i, roof p x W i)=_; symm; refine HasSum.tsum_eq ?_; exact ((hx.hasSum.tsum_fiberwise (pre p)).congr_fun fun i=> (remand p x W i hv).tsum_eq.symm) -- orientation
open Ruby
lemma termsK {N:ℕ}(X:Patron.Rail c N I)(t:ℝ)(U:Grid c)(T:Finset I) : tK X t U T= roof X.addr (fun i=>X.warp i U) (RG.flags t U) T:=by unfold tK roof; refine if_congr ?_ rfl rfl; exact and_congr (GasP.close _ _ _) Eq.comm
lemma goodsK {N:ℕ}(X: Patron.Rail c N I)(t:ℝ)(U:Grid c)(h:Summable fun i=>‖X.warp i U‖): Kites.heartK X t U=∑' i,roof id (coin X.addr (fun i=> X.warp i U)) (RG.flags t U) i:=by unfold Kites.heartK; simp_rw [termsK]; exact catalogue _ _ _ h
-- use also summon-algebra for TINE physical
omit [CompleteSpace V][NormOneClass V] in
lemma fingerprint (Y:Cove.Hat c): coin p x Y = ∑' i,if p i=Y then x i else 0:=by
    let g i:= if p i=Y then x i else 0; have hg : Function.support g ⊆ ray p Y := fun i (h:g i≠0)=> (show p i=Y from by_contra fun he=>h (if_neg he)); exact Eq.trans (tsum_congr (fun i:↥(ray p Y)=> (show g i.val=x i from if_pos (show p i.val=Y from i.2)).symm)) (tsum_subtype_eq_of_support_subset hg)
omit [NormOneClass V] in
lemma readycoin {A: Type}[NormedCommRing A][NormedSpace ℂ A][NormedSpace ℂ V](T: Cove.Hat c)(f:V→L[ℂ]A)(h:Summable fun i=>‖x i‖): coin p (f∘x) T= f (coin p x T):= (f.map_tsum (h.of_norm.comp_injective Subtype.val_injective)).symm
end YM.MassiveQCD.Plate

#print axioms YM.MassiveQCD.Plate.goodsK
