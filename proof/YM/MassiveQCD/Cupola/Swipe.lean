import YM.MassiveQCD.Cupola.Crown
import YM.MassiveQCD.Apron.Blueprint
/-! # Unstamp from any tape, all actual extractions are on its range.
 The competitor port does not even estimate with this map on arbitrary tapes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B: Type}[Fintype A][Fintype B] (u:A↪B)
-- forget structure.P.
noncomputable def exit : Matrix B A ℂ:=fun b a=> if u a=b then 1 else 0
lemma exitLife (i:A): changeVars (exit u) (atom (u i))=atom i:=by
    rw [change_atom,sum_eq_single i]; simp [exit]; intro j _ hj; simp [exit, u.injective.ne hj]; simp -- semicolon scoped?
lemma exitBack (x:Alg A):changeVars (exit u) (embed u x)=x:=DFunLike.congr_fun (f:= (changeVars (exit u)).comp (embed u)) (g:= AlgHom.id ℂ _) (ext_atoms (fun i=>by rw [AlgHom.comp_apply,embed_atom, exitLife]; rfl)) x -- named F? edit
-- region ledger general proof
lemma landed (X:Finset A): mono X ∈region X:=by obtain ⟨f,-,hp,h⟩:= expression X; rw [h]; exact (region X).list_prod_mem fun i hi=> by obtain ⟨j,rfl⟩:= List.mem_ofFn.mp hi; exact marked _ _ ((hp _).mpr ⟨j,rfl⟩)
lemma soil (X Y:Finset A)(x:Alg A)(h:x∈region Y)(hz:¬ X⊆Y): coef X x=0:=by
    obtain ⟨p,rfl⟩:=h; let u:↥Y↪ A:=⟨_, Subtype.val_injective⟩; have he (p:Finset (↥Y)):coef X (embed u (mono p))=0:=by
       have hp:X ≠ p.map u:=fun h=>hz (h.symm ▸ (fun _ hv=>by obtain ⟨s,hn,rfl⟩:= mem_map.mp hv; exact s.2))
       rcases embed_blade u p with h|h <;> rw [h] <;> simp [Grass.read_other _ _ hp]
    change coef X (embed u p)=_; rw [← write p,map_sum,map_sum]; simp only [map_smul,he,smul_zero,sum_const_zero]
lemma embrace {X:Alg A}{T:Finset A}(h:∀ s:Finset A, ¬ s⊆T → coef s X=0) : X∈ region T:=by rw [← write X]; apply Subalgebra.sum_mem; intro i _; by_cases he:i⊆ T; exact Subalgebra.smul_mem _ (regionMon he (landed i)) _; rw [h _ he,zero_smul]; exact (region T).zero_mem
variable {c:Side}{I:Type}[Fintype I]
variable (N:ℕ)(o:I→Site c)(φ:ℝ)
local notation "M"=> ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "X"=> K⊕Spine I
-- actual extraction from port.Full Γ
noncomputable def retreatU: Alg (Keys c (ample N I))→ₐ[ℂ] Alg (Keys c N⊕Spine I):= (stretch φ K R).comp (changeVars (exit (territory N o)))
noncomputable def withdraw: EvenA c (ample N I)→ₐ[ℂ] Patio (Keys c N⊕Spine I):= car (retreatU N o φ) fun x h=> (exterior_parity _ _).trans (congr_arg (stretch φ K R) ((exterior_parity _ x).trans (congr_arg _ h)))
lemma home (h:0< φ) (x:Patio X): withdraw N o φ (banknote N o φ x)=x:=by apply Subtype.ext; change stretch _ _ _ (changeVars _ (pen N o φ _))=_; rw [pen, AlgHom.comp_apply,exitBack]; exact stretch_identity h.ne' ..
noncomputable def mayor (h:0<φ): Apron.Grove.Eraser N o φ := ⟨(withdraw N o φ).toLinearMap.toContinuousLinearMap.restrictScalars ℝ,home N o φ h⟩
-- Ledger opening.U: choice member needs all anchors out.There via quill.] morphology.F
noncomputable def limitQ (S:Support c):Finset (Spine I):=Finset.univ.filter (fun i:Spine I=> o i.1.1∈S)
noncomputable def bankM (S:Support c):Finset (Keys c N⊕Spine I):= (limits S).disjSum (limitQ o S)
lemma held_fee (S:Support c)(i:X): i∈bankM N o S ↔ territory N o i∈ limits S:=by
    rcases i with i|i; simp only [limits,mem_filter,mem_univ,true_and,bankM,Finset.inl_mem_disjSum]; change _↔ locationP (shape N i I)∈ S; rw [locus] -- simp priority
    simp only [bankM,limitQ,limits,Finset.inr_mem_disjSum,mem_filter,mem_univ,true_and]; exact Iff.rfl
lemma boundExit (x: EvenA c (ample N I))(S:Support c)(h:Gated S x): light X (withdraw N o φ x) ∈ region (bankM N o S):=by
   refine effects (retreatU N o φ) ?_ _ h; intro i hi; unfold retreatU; rw [AlgHom.comp_apply,change_atom,map_sum]; apply Subalgebra.sum_mem; intro j _; rw [map_smul]; unfold exit; split; swap; · rw [zero_smul]; exact (region _).zero_mem
   next hj=> apply Subalgebra.smul_mem; unfold stretch; rw [change_atom,sum_eq_single j]; exact Subalgebra.smul_mem _ (marked j _ ((held_fee N o S j).2 (hj.symm ▸ hi))) _; intro k _ hk; simp [hk.symm]; simp
lemma pennied (s: Finset (Spine I))(x: EvenA c (ample N I))(S:Support c)(h:Gated S x):pluck K s (withdraw N o φ x) ∈ region (limits S):=by
   let p:= light X (withdraw N o φ x); have hh:=boundExit N o φ x S h; apply embrace; intro T hu; apply norm_eq_zero.mp; change ‖coef T (scrape K s p)‖ =0; rw [bank,soil _ _ _ hh,norm_zero]; exact fun hf=>hu (fun i hi=> Finset.inl_mem_disjSum.mp (hf (Finset.inl_mem_disjSum.mpr hi)))
lemma confined (s: Finset (Spine I))(x: EvenA c (ample N I))(S:Support c)(h:Gated S x)(hp:¬ s⊆ limitQ o S): pluck K s (withdraw N o φ x)=0:=by
    let p:= pluck K s (withdraw N o φ x); have hh:=boundExit N o φ x S h; change p=0; rw [← Grass.write p]; refine sum_eq_zero fun i _=>?_ ; rw [show coef i p=0 from norm_eq_zero.mp ?_,zero_smul]; rw [show ‖coef i p‖= _ from bank i s (light X (withdraw N o φ x)),soil _ _ _ hh,norm_zero]; exact fun hf=>hp (fun j hk=> Finset.inr_mem_disjSum.mp (hf (Finset.inr_mem_disjSum.mpr hk))) -- infer rhs
-- membership for supports all roots
lemma held_pins (S:Support c)(i:Finset I)(q:I→Bool) : burst q i⊆ limitQ o S ↔ i.image o⊆ S:= by constructor; intro hf j hv; obtain ⟨i,h,rfl⟩:=mem_image.mp hv; exact (mem_filter.mp (hf ((place q i _).mp h))).2; intro hh j hu; exact mem_filter.mpr ⟨mem_univ _,hh (mem_image_of_mem o (located q i j hu))⟩
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.confined
