import YM.MassiveQCD.Ribbon.Burst
import YM.QCD.Loom.Palm
/-! # Graded storage into a Fleet alphabet

 Analyst after-L costs are booked on M-independent Fleet; reserve Enough M possibly
 extensive number of "auxiliary" slots. There is **NO QCD MEASURE** of Flavor M! It's
 an injective storage using detector in M-independent analytic tape. We populate extra
 generators using one singlet bunch per odd marker and two per even. Thus color orientation
 will respect the interior and full-port masks. No dummy spins are smoothed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Lat QCD.Cove QCD.Creek Function Finset Lattice RG Wilson
open scoped Topology BigOperators ContDiff Classical Kronecker Matrix Matrix.Norms.L2Operator
variable {c:Side}{I:Type}[Fintype I]
variable (N:ℕ) (o:I→Site c)
noncomputable abbrev ample (I:Type) [Fintype I]:= N+Fintype.card I
local notation "S"=> Spine I
local notation "K"=> Keys c N
local notation "M"=> ample N I
local notation "X!"=> Keys c M
local notation "X'"=> K⊕Spine I
noncomputable def scroll (I:Type)[Fintype I]: Flavor N⊕I ≃ Flavor (ample N I) :=(Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin I)).trans finSumFinEquiv
noncomputable def shape (i: K)(I:Type)[Fintype I]: Keys c (ample N I):= Sum.map (Prod.map id (scroll N I∘Sum.inl)) (Prod.map id (scroll N I∘Sum.inl)) i
noncomputable def placket (b:Bool):Pinor:= if b then 1 else 0
private lemma placket_eq {a b} (h:placket a=placket b):a=b:=by
    cases a <;> cases b; exact rfl; exact absurd h (by decide +kernel); exact absurd h (by decide +kernel); exact rfl
noncomputable def swipe (i:S): Keys c (ample N I):= Sum.inl ((o i.1.1,(placket i.1.2,i.2)), (scroll N I (Sum.inr i.1.1)))
lemma separate (i:Keys c N)(j:S):shape N i I ≠ swipe N o j:=by
    intro h
    rcases i with i|i; exact Sum.inl_ne_inr ((scroll N I).injective (congr_arg Prod.snd (Sum.inl.inj h) : scroll N I (.inl i.2)= scroll N I (.inr j.1.1)))
    exact Sum.inr_ne_inl h
noncomputable def shapeE (N:ℕ)(I:Type)[Fintype I] (c:Side): Keys c N ↪ Keys c (ample N I):=by
    let g:= (scroll N I)∘Sum.inl; refine ⟨fun i=> shape N i I,?_⟩; change Injective (Sum.map (Prod.map id g) (Prod.map id g)); have hg : Injective (Prod.map (@id (Row c)) g):=fun a b h=> Prod.ext (congr_arg (fun i:Row c × Flavor (ample N I)=> i.1) h) (((scroll N I).injective.comp Sum.inl_injective) (congr_arg (fun i:Row c × Flavor (ample N I)=> i.2) h)); exact Sum.map_injective.mpr ⟨hg,hg⟩
lemma locus (i: K): locationP (shape N i I)=locationP i:=by cases i <;>rfl
lemma speaker (i:S): locationP (swipe N o i)= o i.1.1:=rfl
noncomputable def swipeE : Spine I↪Keys c (ample N I):=by
   refine ⟨swipe N o,?_⟩; rintro ⟨⟨i,b⟩,j⟩ ⟨⟨i',b'⟩,j'⟩ he; let a:= (Sum.inl.inj he); exact Prod.ext (Prod.ext (Sum.inr.inj ((scroll N I).injective (congr_arg Prod.snd a : (scroll N I) (Sum.inr i)=scroll N I (.inr i')))) (placket_eq (congr_arg (fun z=>(z:Modes c M).1.2.1) a))) (congr_arg (fun z=>(z:Modes c M).1.2.2) a)
noncomputable def territory : Keys c N⊕Spine I ↪ Keys c (ample N I):=by
   refine ⟨Sum.elim (shapeE N I c) (swipeE N o),?_⟩
   rintro (i|i) (j|j) h; exact congr_arg Sum.inl ((shapeE N I c).injective h); exact False.elim (separate N o i j h); exact False.elim (separate N o j i h.symm); exact congr_arg Sum.inr ((swipeE N o).injective h)
-- scaling.
variable (a:ℝ)
noncomputable def stretch (A B:Type)[Fintype A][Fintype B]: Alg (A⊕B)→ₐ[ℂ] Alg (A⊕B):= changeVars (Matrix.diagonal (Sum.elim (fun _=>1) (fun _:B=>a)))
lemma stretched_f (A B:Type)[Fintype A][Fintype B](i:Alg A):stretch a A B (fiber B i)=fiber B i := by
    have ht:(stretch a A B).comp (fiber B)= fiber B:=by apply ext_atoms; intro i; simp [stretch,fiber, change_atom, Matrix.diagonal_apply,ite_smul]
    exact DFunLike.congr_fun ht _
lemma stretched_m (A B:Type)[Fintype A][Fintype B](s:Finset B):stretch a A B (quill A (mono s))=(a:ℂ)^s.card • quill A (mono s):=by
    let e:= (Embedding.inr (α:=A) (β:=B)); let r:A⊕B→ℝ:=Sum.elim (fun _=>1) (fun _=>a); have h : stretch a A B (mono (s.map e))=(a:ℂ)^s.card • mono (s.map e):=by
       have hs: Matrix.diagonal (fun i:A⊕B=> (↑(r i):ℂ))= Matrix.diagonal (Sum.elim (fun _=>1) (fun _:B=>(a:ℂ))):= by apply congr_arg (Matrix.diagonal); funext i; cases i; exact Complex.ofReal_one; rfl
       have he:= wscale_mono r (s.map e); unfold wscale at he; rw [Finset.prod_map] at he; change stretch _ _ _ _=_; apply Eq.trans _ (he.trans ?_); swap; · change (∏ _i∈ s,(a:ℂ)) • _=_; rw [Finset.prod_const]
       refine congr_arg (fun X:Matrix (A⊕B) (A⊕B) ℂ=> changeVars X _) ?_; convert! hs.symm using 1; congr!
    rcases embed_blade e s with hh|hh <;> change quill A _= _ at hh <;> rw [hh] <;> simp only [map_neg,h,smul_neg]
lemma stretches (A B:Type)[Fintype A][Fintype B](s:Finset B)(x:Alg A):stretch a A B (stake A s x)=stake A s ((a:ℂ)^s.card • x):=by
   rw [markedOut,markedOut,map_mul,map_smul,stretched_f,stretched_m,mul_smul_comm,smul_mul_assoc]
noncomputable def pen : Alg (Keys c N⊕Spine I) →ₐ[ℂ] Alg (Keys c (ample N I)) := (embed (territory N o)).comp (stretch a⁻¹ K S)
noncomputable def banknote : Patio (Keys c N⊕Spine I) →ₐ[ℂ] EvenA c (ample N I):= car (pen N o a) fun x h=> (embed_grade ..).trans (congr_arg _ ((exterior_parity _ x).trans (congr_arg _ h)))
lemma bank_spent (x): Cove.light _ (banknote N o a x)= pen N o a (Cove.light _ x):=rfl
lemma stretch_identity {a:ℝ}(h:a≠0)(A B:Type)[Fintype A][Fintype B](x):stretch a A B (stretch a⁻¹ A B x)=x:=by
   have ht:∀ s:Finset B,True:=by intro _; trivial -- edit
   conv_lhs=> rw [← rewriteR A x,map_sum,map_sum];
   apply Eq.trans _ (rewriteR A x); refine sum_congr rfl fun i _=>?_; rw [stretches,stretches,smul_smul,Complex.ofReal_inv,← mul_pow,mul_inv_cancel₀ (by exact_mod_cast h),one_pow,one_smul]
lemma visible {a:ℝ}(h:a≠0): Injective (pen N o a):=by
   intro i j H; exact (stretch_identity h _ _ i).symm.trans ((congr_arg _ (implant _ H)).trans (stretch_identity h _ _ j)) -- embedding inference
-- solve support inclusion at post.M.Root.Billing.SP.
lemma entitled (Y:Support c)(s:Finset (Spine I))(x:Alg K)(h:x∈region (limits Y))(hp:∀ i∈s,o i.1.1∈Y): pen N o a (stake K s x) ∈ region (limits Y):=by
    rw [pen,AlgHom.comp_apply,stretches,markedOut,map_mul]; apply Subalgebra.mul_mem
    · rw [embed_comp]; apply effects (embed _); swap; · exact Subalgebra.smul_mem _ h _
      intro i hi; rw [embed_atom]; apply marked; apply mem_filter.mpr; change _∧ locationP (shape N i I)∈Y; rw [locus]; exact ⟨mem_univ _,(mem_filter.mp hi).2⟩
    rw [embed_comp]; refine effects (U:=s) (embed _) ?_ _ ?_; swap -- need mono mem subset
    · obtain ⟨w,-,hh,hM⟩:=expression s -- edit
      rw [hM]
      apply Subalgebra.list_prod_mem; intro i hi; obtain ⟨j,rfl⟩:= List.mem_ofFn.mp hi; apply marked; exact (hh ..).mpr ⟨_,rfl⟩
    intro i hi; rw [embed_atom]; apply marked; exact mem_filter.mpr ⟨mem_univ _, hp i hi⟩
end YM.MassiveQCD.Ribbon
