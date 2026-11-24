import YM.QCD.Reggae.Scalar
/-! # Negative-log local atlas of the scalar regulator. Zero padding. Uses germs at ANY healthy. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Reggae
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{p:BudgetPoint}{z u a r t:ℝ}{i j x:Site c}
open Port AnalyticBridge.VerifiedReset Collection Extra.Iteration Footprint
variable {ι ι' :Type} [Countable ι] (E: Gem c N ι)
abbrev Curtain (n:Side)(ι:Type):=ι ⊕ (ℕ × Site n)
noncomputable def fogX (i: Site c): RegularAddress c:=⟨i,{i},mem_singleton_self i⟩
noncomputable def padA : Curtain c ι →RegularAddress c:= Sum.elim E.addr (fun i=>fogX i.2)
noncomputable def padX : Curtain c ι→Grid c→ℝ:=Sum.elim (fun i=> river c N ∘ E.view i) 0
noncomputable def theater : Listing su c:=⟨padA E ∘ numbering _,fun _=> ⟨univ,univ,univ_nonempty,Subset.refl _,fun _=>True⟩⟩
noncomputable def stock : Collection.Source su c:=⟨padX E ∘ numbering _,0⟩
lemma dome (s: Strut c): (univ:Finset (Site c)).image (affine s.1 s.2)=univ:=image_univ_of_surjective (act s).surjective
lemma localM (h:Crossing E): ∀ s b, Nonempty (((theater E).read (stock E)).Moves s b):=by
    intro s b; let V: Strut c:=(s,b); let T:= Diode N V (sat V) (ink V); obtain ⟨e,hF⟩:=h.rays V (sat V) (ink V) (assured V)
    let j:=Equiv.sumCongr e (Equiv.prodCongr (Equiv.refl ℕ) (act V)); let k:=numbering (Curtain c ι); let z:= (k.trans j).trans k.symm; have he i:k (z i)=j (k i):= k.apply_symm_apply _
    have hZ (x:Curtain c ι): padA E (j x)=rotateL (padA E x) V∧∀ U, padX E (j x) U=padX E x (sky V U):=by
       rcases x with i|⟨n,o⟩
       · refine ⟨(hF i).1,fun U=>?_⟩; change river _ _ (E.view (e i) _)=_; rw [←(hF i).2 U]; exact mur .. -- defeq
       refine ⟨?_ ,fun U=>rfl⟩; change fogX (act V o)=_; simp only [padA,Sum.elim_inr,rotateL,fogX,image_singleton]
    refine ⟨⟨z,Equiv.refl _,?_,?_,fun i=>(dome V).symm,fun i=>(dome V).symm,fun i U=>Iff.rfl,?_,fun i U=>rfl⟩⟩
    · intro i; change (padA E (k (z i))).site=_; rw [he, (hZ _).1]; rfl
    · intro i; change (padA E (k (z i))).support=_; rw [he, (hZ _).1]; rfl
    intro i U; change padX E (k (z i)) _=_; rw [he]; exact (hZ _).2 U
lemma regMoney (hp:Crossing E)(hv:Licence p (Quotes.preExponent p) u a E)(ht:0≤a): Collection.Local (theater E) p (stock E) u 0:=by
    obtain ⟨f,hf,h⟩:= hv.zone; let k:=numbering (Curtain c ι); let B: Curtain c ι→ℝ:= Sum.elim f 0
    have hx (q:Curtain c ι) : p.Regular (padA E q).support (padX E q) ∧ p.supBounds (padA E q).site (padA E q).support (padX E q) (B q):=by
       rcases q with i|⟨n,o⟩
       · exact spores _ _ _ (h i) (hp.blank.gauge i) ht
       exact ⟨reg_const _,Eq.mp (show p.supBounds o (fogX o).support (fun _:Grid c=> (0:ℝ)) |0|=p.supBounds o (fogX o).support (fun _ : Grid c=>0) 0 from by rw [abs_zero]) (sup_const _)⟩
    refine ⟨fun i=> (hx _).1,⟨fun i k U=>rfl,fun i k U=> Iff.rfl,fun _=>measurable_const,fun i=>MeasurableSet.univ,fun i U V h q=>rfl,fun i U V h q=>rfl,fun i U h=> False.elim (h rfl)⟩,localM E hp,⟨B ∘ k, fun i=>(hx _).2,fun i=>?_⟩, ⟨fun _=>0,fun i=>⟨le_rfl,fun V=> by change ‖(0:ℝ)‖ ≤ 0; simp⟩,fun x=> ?_⟩⟩
    · let R j:= if (padA E j).site=i then B j*Real.exp (Quotes.preExponent p *coverNumber p.B (padA E j).support) else 0; have he : SumBudget R (u+0):=by
         apply Extra.Iteration.Cost.sum (hf i); simp [R,B,SumBudget]
      rw [add_zero] at he; exact Extra.Iteration.Cost.equiv k he
    simp [SumBudget]
lemma masker (f:Grid c→EvenA c N)(p:ℝ)(Z:Support c)(U:Grid c) : river _ _ (masked p Z f U)=masked p Z (river c N ∘ f) U:=by
    by_cases h:Healthy p Z U <;> first | rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl| rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,map_zero]
lemma medlar {t:BudgetPoint}(U:Grid c)(hv:Summable (letters E t.threshold U)): river c N (Patron.total E t.threshold U)= ((theater E).read (stock E)).additive t U:=by
    let f v:=masked t.threshold (padA E v).support (padX E v) U; let N':=numbering (Curtain c ι)
    have ht (i:ι) : river c N (letters E t.threshold U i)=f (.inl i):=masker ..; let x:= river c N (Patron.total E t.threshold U); have hh: HasSum (fun i:ι=> f (.inl i)) x:= ((river c N).hasSum hv.hasSum).congr_fun (fun i=> (ht i).symm)
    have he: HasSum (fun i:ℕ × Site c=> f (.inr i)) 0:= hasSum_zero.congr_fun (fun i=>by
       unfold f; by_cases h:Healthy t.threshold (padA E (.inr i)).support U; · rw [masked_eq _ _ _ _ h]; rfl
       rw [masked_ne _ _ _ _ h])
    change _=∑' i:ℕ,f (N' i); rw [N'.tsum_eq, Summable.tsum_sum (f:=f) hh.summable he.summable,he.tsum_eq,hh.tsum_eq,add_zero]
end YM.QCD.Reggae
