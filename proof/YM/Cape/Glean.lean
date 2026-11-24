import YM.Cape.Fall
/-!
# Handling soft mask terms in marked K transactions
Bank plane implementation. Fixed old unmarked representation. Right Spine.
Soft entries appear precisely when W overlaps flags; we do not substitute an all-flat complement.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U:Type}[Fintype I]
variable (p:I→Site c)(q:I→Bool) (Y:Lure c N I Z) (F:Film c N I D)(M: Patron.Rail c N U)
variable {t v:ℝ}
local notation "K"=> Keys c N
local notation "R"=> Ribbon.Spine I
local notation "Φ"=> banknote N p v
local notation "Sh"=> withdraw N p v
local notation "φ"=> rootR R (Keys c N)
local notation "X"=> torah p F M v
local notation "Z'"=> vesta p Y v
local notation "P"=> Stalk p Y F M v
local notation "Γ"=> fog p Y F M v
variable (hY:Y.On p q t) (hF:F.Beat N p q t)(hM:M.Reg t)(hC:∀ i,Cove.shadeG (M.warp i))(hP:0<v)
local notation "T!"=> Trail Z' X t
local notation "Cz"=> Cob p Y F M v
local notation "H"=> coverP p Y F M v t

lemma ground_aux (i:U): Ruby.gemD Z' X {.inl (.inl i)} :=by
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro u hu z hz he; have h₁ := mem_singleton.mp (mem_toLeft.mp hu); have h₂ := mem_singleton.mp (mem_toLeft.mp hz); exact (he (Sum.inl_injective (h₁.trans h₂.symm))).elim
    · simp
    · exact ⟨_,mem_toLeft.mpr (mem_singleton_self _)⟩
    exact ⟨singleton_nonempty _,fun _ he _ hh=>(mem_singleton.mp he |>.trans (mem_singleton.mp hh).symm) ▸ .refl⟩
noncomputable def hush (v:ℝ)(i:U): Stalk p Y F M v:=⟨{.inl (.inl i)},ground_aux p Y F M i⟩
noncomputable def reelOut (v:ℝ): U⊕ Cob p Y F M v → Stalk p Y F M v:= Sum.elim (hush p Y F M v) Subtype.val
local notation "M₀"=> reelOut p Y F M v
lemma mistP (i:U): Γ (M₀ (.inl i))=∅:=by unfold fog; rw [show (M₀ (.inl i)).val={_} from rfl,singleton_biUnion]; rfl -- placeholder
lemma sheeny :Injective M₀ :=by
   rintro (i|i) (j|j) h
   · apply congr_arg (Sum.inl); exact Sum.inl_injective (Sum.inl_injective (Finset.singleton_injective (congr_arg Subtype.val h)))
   · exact (Finset.nonempty_iff_ne_empty.mp j.2 ((congr_arg (Γ) h).symm.trans (mistP ..))).elim
   · exact (Finset.nonempty_iff_ne_empty.mp i.2 ((congr_arg (Γ) h).trans (mistP ..))).elim
   exact congr_arg Sum.inr (Subtype.ext h)
include hY hF
lemma benches (i:P)(he:Γ i=∅) : ∃ u:U, i=M₀ (.inl u):=by
   let B:=U⊕D; let T:=i.val
   have hk(k: (U⊕D)⊕ Z)(hh:k∈T): ∃ u:U,k=.inl (.inl u):=by
      have h :exitA Y F k =∅:=subset_empty.mp ((subset_biUnion_of_mem (exitA Y F) hh).trans he.le)
      rcases k with (u|j)|j; exact ⟨_,rfl⟩; exact ((hF.commits j).ne_empty h).elim; exact ((hY.enough _).ne_empty h).elim
   have hg(i' j)(h:Ac.bonds (footD Z' X) T i' j): i'=j:=by
      obtain ⟨h₀,h₁,a,hx,hq⟩:=h; obtain ⟨u,rfl⟩:= hk _ h₀; obtain ⟨z,rfl⟩:=hk _ h₁
      by_contra he; apply Finset.disjoint_left.mp ?_ hx hq -- he binder? details
      exact ((GasP.close _ _ _).mp i.property.1.1) (mem_toLeft.mpr h₀) (mem_toLeft.mpr h₁) (fun h=> he (congr_arg Sum.inl h))
   have hl :∀ i' j, Ac.chain (footD Z' X) T i' j→i'=j :=by
      intro a b h -- ∈ applies j only?
      induction h with
      | refl=>rfl
      | tail u hv IHv=> exact Eq.trans IHv (hg _ _ hv)
   obtain ⟨e,he⟩:=i.property.2.2.1; obtain ⟨u,rfl⟩:= hk _ he
   refine ⟨u,Subtype.ext ?_⟩; change i.val={_}; ext x; rw [mem_singleton]; exact ⟨fun h=>hl x _ (i.property.2.2.2 x h _ he),fun h=> h ▸ he⟩
lemma showUp : Surjective M₀:=by
    intro i; by_cases h:(Γ i).Nonempty; exact ⟨.inr ⟨i,h⟩,rfl⟩; obtain ⟨u,rfl⟩:= benches p q Y F M hY hF i (not_nonempty_iff_eq_empty.mp h); exact ⟨_,rfl⟩
omit hY hF
include hM hP
lemma aloud (V:Grid c)(i:U⊕ Cz): ((T!).addr (M₀ i)= Film.addressSets N H M i) ∧ Sh ((T!).warp (M₀ i) V)= Film.spruced N H M i V:=by
   rcases i with i|i; swap; · exact ⟨rfl,rfl⟩
   let j:=M₀ (.inl i); let E:=banknote N p v; have he:j.val={.inl (.inl i)}:=rfl
   have hf: badgeK X j.val=(M.addr i).inv:=by unfold badgeK; rw [he,show ({Sum.inl (Sum.inl i)}:Finset ((U⊕ D)⊕Z)).toLeft={.inl i} from ?_,singleton_biUnion]; rfl; ext; simp
   have hp:scopeK Z' X j.val=(M.addr i).place:=by unfold scopeK; rw [he,singleton_biUnion]; rfl
   refine ⟨?_ ,?_⟩
   · change Hat.mk (scopeK ..) (badgeK ..) _ _ = M.addr i; congr
   change Sh (payer Z' X t V j.val)=φ (M.warp _ _); unfold payer; rw [hp,hf,he]; split; next h=> rw [prod_singleton]; exact Cupola.home N _ _ hP _
   next hh=> rw [map_zero,show M.warp i V=0 from by_contra (fun hn=>hh (hM.buys _ _ hn)),map_zero]
include hY hF
lemma conquer (V:Grid c)(s:Finset (U⊕ Cz)): Sh (Ruby.tK T! t V (s.image M₀))= Plate.roof (Film.addressSets N H M) (fun j=>Film.spruced N H M j V) (flags t V) s :=by
    rw [Plate.termsK]; unfold Plate.roof
    let T:= flags t V; let L:=Film.addressSets N H M
    have he(i): (T!).addr (M₀ i)=L i:=(aloud p Y F M hM hP V i).1
    have hx : Arm (T!).addr T (s.image M₀) ↔ Arm L T s:=by
        unfold Arm; refine and_congr ?_ ?_
        · constructor
          · intro h i hi j hj hn; change Disjoint (L i).place (L j).place; rw [← he,← he]; exact h (mem_image_of_mem M₀ hi) (mem_image_of_mem M₀ hj) ((sheeny p Y F M).ne hn)
          intro h i hi j hj ht; obtain ⟨i,hi0,rfl⟩:=mem_image.mp hi; obtain ⟨j,hj0,rfl⟩:=mem_image.mp hj; change Disjoint ((T!).addr (M₀ i)).place ((T!).addr (M₀ j)).place; rw [he,he]; exact h hi0 hj0 (fun hg=>ht (congr_arg M₀ hg))
        rw [image_biUnion]; simp_rw [he]
    by_cases h:Arm L T s; swap; · rw [if_neg h,if_neg (mt hx.mp h),map_zero]
    rw [if_pos h, if_pos (hx.mpr h),map_prod,prod_image (sheeny p Y F M).injOn]; exact prod_congr rfl (fun i _=> (aloud p Y F M hM hP V i).2) -- why hY included?
omit hM hY hF
lemma retract (V:Grid c)(s:Finset (U⊕ D)): Sh (Ruby.tK X t V s)=Plate.roof (Film.addressSets N F M) (fun j=>Film.spruced N F M j V) (flags t V) s :=by -- shadow U issue
   rw [Plate.termsK]; unfold Plate.roof; split; next h=> rw [if_pos (show Arm (Film.addressSets N F M) (flags t V) s from h),map_prod]; exact prod_congr rfl fun i _=> Cupola.home N _ _ hP _
   next h=> rw [if_neg (show ¬Arm (Film.addressSets N F M) (flags t V) s from h),map_zero]
include hM hY hF
variable [Finite Z]
lemma gladdened (V:Grid c)(hv:Summable (Ruby.tK X t V)) : Film.reports N H M t V= Film.reports N F M t V * NormedSpace.exp (∑' i:Z,Y.wick i V):=by
    let L:=(Sh).toLinearMap.toContinuousLinearMap; have hZ:= Ruby.plenary Z' X V hv (vespers p q Y hY) Summable.of_finite Summable.of_finite
    let w:= (Ruby.tK T! t V); let θ:=Equiv.ofBijective M₀ ⟨sheeny p Y F M,showUp p q Y F M hY hF⟩; let Mv:= Equiv.finsetCongr θ; let hZ':=hZ.summable
    have he : Film.reports N H M t V=∑' i:Finset P,L (w i):=by
        rw [←Equiv.tsum_eq Mv]; apply tsum_congr; intro i; change _=L (w _); rw [show Mv i=image M₀ i from Finset.map_eq_image ..]; exact (conquer p q Y F M hY hF hM hP V i).symm
    rw [he,← L.map_tsum hZ',show ∑' i,w i=_ from hZ.tsum_eq]; change Sh (_*_)=_; rw [map_mul, map_exp (Sh) L.continuous]; apply congr_arg₂ (·*·)
    · change L _=_; rw [L.map_tsum hv]; exact tsum_congr fun i=> retract p F M hP V i
    apply congr_arg; change L _ = _; rw [L.map_tsum Summable.of_finite]; exact tsum_congr fun x=> Cupola.home N _ _ hP _
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.gladdened
