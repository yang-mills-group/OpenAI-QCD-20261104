import YM.MassiveQCD.Cupola.Left
/-! # Root-resonance shutters. Price changes (orientation) & deletion coherent
 Even when keeping all unmarked representations, allowed projections reset *inside* only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function Loom
open MeasureTheory NormedSpace Filter
open scoped Topology BigOperators ContDiff Classical Matrix Kronecker
variable (A:Type){I:Type}[Fintype A][Fintype I](q:I→Bool)
variable (w:I→ℝ)
local notation "Z"=> A⊕Spine I
-- mark w only at detector node i=...; component λ replay joint boosts.
noncomputable def needle : Spine I→ℝ:= fun z=> if z.1.2=false ∧ z.2=0 then w z.1.1 else 1
noncomputable def tar : A⊕Spine I→ℝ:= Sum.elim (fun _=>1) (needle w)
noncomputable def vscale := changeVars (Matrix.diagonal (fun i:A⊕Spine I=> ((tar A w i) :ℂ)))
noncomputable def scaler : Patio Z→ₐ[ℂ] Patio Z:= car (vscale A w) fun x h=> (exterior_parity _ x).trans (congr_arg _ h) -- wscale is AlgHom?
lemma tarfib (x:Alg A) : vscale A w (fiber (Spine I) x)= fiber (Spine I) x:=by
    let t:=Spine I; have ht:(vscale A w).comp (fiber t)=fiber t (A:=A):=by apply ext_atoms; intro i; unfold vscale; rw [AlgHom.comp_apply,embed_atom,change_atom,sum_eq_single (Sum.inl i)]; simp [tar]; intro j _ hj; rw [Matrix.diagonal_apply_ne _ hj.symm,zero_smul]; simp -- inspect
    exact DFunLike.congr_fun ht x
noncomputable def pole (w:I→ℝ)(s:Finset (Spine I)):ℂ:= ∏ i∈s,(needle w i:ℂ)
lemma tarStake (x:Alg A)(s: Finset (Spine I)): vscale A w (stake A s x)=pole w s • stake A s x:=by
   rw [markedOut,map_mul,tarfib]; let e:=Embedding.inr (α:=A) (β:=Spine I); have h:vscale A w (mono (s.map e))=pole w s • mono (s.map e):=by
        have he:= wscale_mono (tar A w) (s.map e); rw [prod_map] at he; unfold wscale at he; convert! he using 1; unfold vscale; congr!
   rcases embed_blade e s with he|he <;> change _*vscale A w (embed e _)= _ • (_ * embed e _) <;> rw [he] <;> simp only [map_neg,h,mul_smul_comm, mul_neg,smul_neg]
lemma pulse (x: Patio Z)(s:Finset (Spine I)): pluck A s (scaler A w x)=pole w s • pluck A s x:=by
    change scrape A s (vscale A w x.val)=_
    rw [← rewriteR A x.val,map_sum,map_sum,sum_eq_single s]
    · rw [tarStake,map_smul,quid]; rfl
    · intro i _ hi; rw [tarStake,map_smul,stakesX,if_neg hi.symm,smul_zero]
    simp
omit [Fintype I] in
lemma sensed (s:Finset I) : pole w (burst q s)= ∏ i∈s,(w i:ℂ):=by
    let k (i:I) : Spine I:=((i,false),0); have hp:s.image k ⊆ burst q s:=by intro j hj; obtain ⟨t,ht,rfl⟩:=mem_image.mp hj; exact (place q t s).1 ht
    unfold pole; rw [← prod_subset hp (fun j hj ht=> ?_),prod_image (show Set.InjOn k _ from (show Injective k from fun i j he=> congr_arg (fun x:Spine I=>x.1.1) he).injOn)]; · simp [needle,k]
    simp only [needle]; rw [if_neg,Complex.ofReal_one]; intro ⟨hf,h⟩; exact ht (mem_image.mpr ⟨_, located q s j hj,Prod.ext (Prod.ext rfl hf.symm) h.symm⟩)
lemma pulseI (s:Finset I) (x:Patio Z) : pick A q s (scaler A w x)=(∏ i∈s,(w i:ℂ)) • pick A q s x:=by
    apply Subtype.ext; change light _ ((chooseBlade _ _) _) = light _ ((_: ℂ) • _); rw [choice,pulse,sensed,map_smul,map_smul, pick,choice] -- RHS a map_smul? edit
lemma stamen (s: Finset I)(x: Patio Z)(h:Polite q s x): scaler A w x=(∏ i∈s,(w i:ℂ)) • x:= by
    have he : Polite q s (scaler A w x) := by apply Polite.of_ranges; intro t ht; change pluck A t (scaler A w x)=0; rw [pulse,show pluck A t x=0 from h.spectral t ht,smul_zero]
    exact (eq_pick A q s _ he).symm.trans ((pulseI A q w ..).trans (congr_arg _ (eq_pick A q s x h))) -- order
-- shutter projection χ.Deleted.Coe at color sphere.
noncomputable def shutter (s:Finset I) : Patio Z→ₐ[ℂ] Patio Z:= scaler A (fun j=> if j∈s then 1 else 0)
lemma stamen_h (s t: Finset I)(x:Patio Z)(hp:Polite q s x): shutter A t x= if s⊆t then x else 0:=by
    unfold shutter; rw [stamen A q _ _ _ hp]; split
    next ht=>rw [show (∏ i∈s,(↑(@ite ℝ (i∈t) _ 1 0):ℂ))=1 from prod_eq_one (fun i hi=> by rw [if_pos (ht hi),Complex.ofReal_one]),one_smul]
    next hf=>obtain ⟨i,hi,hj⟩:= not_subset.mp hf; rw [prod_eq_zero hi (by rw [if_neg hj,Complex.ofReal_zero]),zero_smul]
lemma keen (x:Patio Z)(u:Finset I)(h:ValidPieces A q univ x): shutter A u x=chop A q u x:=by
    rw [h.wholeV,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; let y:=pick A q i x; let P:= choseTuft A q i x; rw [stamen_h A q i _ _ P]; apply pluckVisible; intro j; rw [control]
    by_cases he:i ⊆u
    · rw [if_pos he]; split; rfl
      next hK=> exact P.spectral _ (fun e=> hK ⟨i,mem_powerset.mpr he,e⟩)
    rw [if_neg he,map_zero]; split; swap; · rfl
    next hk=> obtain ⟨t,ht,rfl⟩:=hk; exact (P.spectral _ (fun e=>he ((burstUnique q e) ▸ mem_powerset.mp ht))).symm
lemma aperture {M:Set (Finset I)} (u:Finset I)(x: Patio Z)(hp:(u.powerset:Set (Finset I))⊆ M)(he:ValidPieces A q univ x) : shutter A u (slash A q M x)=shutter A u x:=by
    have h: M⊆ ((Finset.univ:Finset I).powerset:Set (Finset I)):=fun _ _=> mem_powerset.mpr (subset_univ _)
    rw [keen A q _ _ (splash A q x h),keen A q _ _ he]; apply pluckVisible; intro i; rw [control, control A q (↑u.powerset) i x]; split
    next hs=> rw [control,if_pos]; obtain ⟨j,hj,hq⟩:=hs; exact ⟨j,hp hj,hq⟩
    rfl
lemma phoenixC (x y: Patio Z)(T:Finset I)(h:shutter A T x=shutter A T y)(s:Finset (Spine I))(hp:∀ i∈s,i.1.1∈T):pluck A s x=pluck A s y:=by
   have he:= congr_arg (pluck A s) h; unfold shutter at he; rw [pulse,pulse] at he; let w:=fun j=> if j∈T then (1:ℝ) else 0; have hw:pole w s=1:=prod_eq_one fun i hi=> by unfold needle; split <;> simp [w,hp i hi]
   rw [hw,one_smul, one_smul] at he; exact he
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.aperture
