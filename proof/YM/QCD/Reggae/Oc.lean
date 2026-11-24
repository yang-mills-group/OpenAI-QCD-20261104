import YM.QCD.Reggae.Ruma
/-! # admissible reprises & joins. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Reggae
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{p:BudgetPoint}{z u a r t w:ℝ}{i j x:Site c}
open Port AnalyticBridge.VerifiedReset Collection Extra.Iteration Footprint Progress.DirectedRecipe Ovens
variable {ι ι' :Type}(E: Gem c N ι)(F:Gem c N ι')(b:Flavor N)
noncomputable def octave (x:EvenA c N):=x-ocean c N (river c N x)
noncomputable def wade : Gem c N ι:= ⟨E.addr, fun i U=> octave (E.view i U)⟩
noncomputable def weave : Gem c N (ι⊕ι'):= ⟨Sum.elim E.addr F.addr, Sum.elim E.view F.view⟩
lemma fizz (x:EvenA c N):river c N (octave x)=0:=by rw [octave,map_sub, taleP,sub_self]
lemma fiber (q:Quanta E b): Quanta (wade E) b:=by
    intro i hi x; have hv:feeF b ((wade E).view i 1)=feeF b (E.view i 1):=by change meter b (_-_)=_; rw [map_sub]; rw [show meter b (ocean c N _)=0 from reduceF _ _, sub_zero]; rfl
    rw [hv]; exact q i hi x
lemma pilots (h: Crossing E):Quartz (wade E)∧ Crossing (wade E):=by
    refine ⟨⟨fun i=>chooseP _ (h.blank.real i 1),fun i hv q u h1 h2=>?_⟩,⟨⟨?_,?_,?_⟩,?_⟩⟩
    · rw [show ((river c N) ∘ (wade E).view i)=(fun _=>0) from funext fun V=>fizz _]; exact hessian_zero .. -- namespace
    · intro i U k; suffices g : sways (Lat.rotates N k) (octave (E.view i (gauge k U)))=octave (E.view i U) by exact congr_arg Subtype.val g
      have he:sways (Lat.rotates N k) (E.view i (gauge k U))=E.view i U:=Subtype.ext (h.blank.gauge i U k); unfold octave; rw [map_sub,he]; rw [thorough]; rw [←he,mur]
    · intro i U v hv; change sways _ (_-_)=_; rw [map_sub,h.blank.num i U v hv]; exact congr_arg₂ _ rfl (thorough ..)
    · intro i U; change Regal c N (_-_) = _; rw [map_sub,h.blank.real i U,thorough]; rfl
    intro s k d hv; obtain ⟨e,he⟩:=h.rays s k d hv; refine ⟨e, fun i=> ⟨(he i).1,fun V=>?_⟩⟩; change Diode _ _ _ _ (octave _)=octave _; rw [←(he i).2 V,mudDummy]
where
  mudDummy {p:Matrix (Modes c N) (Modes c N) ℂ}(x:EvenA c N): sways p (octave x)=octave (sways p x):=by unfold octave; rw [map_sub,thorough,mur] -- rewrite ordering
lemma passes (hp:Crossing E)(hv:Licence p z u a E)(ht:0≤a) {w:ℝ}(he:w≤z): Licence p w (2*u) a (wade E):=by
    obtain ⟨f,hf,H⟩:= hv.zone; let g i:=2*f i; refine ⟨g,fun i=>?_,fun i=>?_⟩
    · apply budget_mono (budget_scale (show 0 ≤ (2:ℝ) by positivity) (hf i))
      · intro i; split; exact mul_nonneg (mul_nonneg (by positivity) (H i).travel) (Real.exp_pos _).le; exact le_rfl
      intro j; change ite ((E.addr j).site=i) _ _ ≤ _; split; next hx=> dsimp only [g]; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply mul_le_mul_of_nonneg_left _ (H j).travel; exact Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
      next hq=> rw [mul_zero]
    obtain ⟨h1,h2⟩:= spores _ _ _ (H i) (hp.blank.gauge i) ht; have he := (H i).addition ((wealthy N _ _ _ h1 h2 ht).byScalar (-1)); rw [norm_neg,norm_one,one_mul,neg_one_smul,←two_mul] at he; refine Eq.mp (congr_arg (fun U=> Woven _ _ _ _ U _) ?_) he; ext1 U; exact (sub_eq_add_neg ..).symm -- underscores failure
lemma perms (U:Grid c)(ht: Summable (letters E t U)): Patron.total (wade E) t U=octave (Patron.total E t U):=by
    let g:= ocean c N; let p:= river c N; apply HasSum.tsum_eq; apply (ht.hasSum.sub (g.hasSum (p.hasSum ht.hasSum))).congr_fun; intro i; change masked t (E.addr i).support _ U=_; by_cases h: Healthy t (E.addr i).support U
    · unfold letters; rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ h]; rfl
    rw [masked_ne _ _ _ _ h]; unfold letters; rw [masked_ne _ _ _ _ h,map_zero,map_zero,sub_zero]
lemma fibs (h:Quanta E b)(hp:Quanta F b): Quanta (weave E F) b:=fun i hi x=>by cases i; exact h _ hi x; exact hp _ hi x
lemma quip (h:Quartz E)(hp:Quartz F): Quartz (weave E F):=⟨fun i=>by cases i; exact h.face _; exact hp.face _,fun i hi x y he hz=>by cases i; exact h.van _ hi x y he hz; exact hp.van _ hi x y he hz⟩
lemma pilot (h:Crossing E)(hp: Crossing F): Crossing (weave E F):=by
    refine ⟨⟨fun i=>by cases i; exact h.blank.gauge _; exact hp.blank.gauge _,fun i=>by cases i; exact h.blank.num _; exact hp.blank.num _,fun i=>by cases i; exact h.blank.real _; exact hp.blank.real _⟩, ?_⟩
    intro s k g hv; obtain ⟨e,he⟩:= h.rays s k g hv; obtain ⟨e',hh⟩:=hp.rays s k g hv; exact ⟨Equiv.sumCongr e e',fun i=>by cases i; exact he _; exact hh _⟩
lemma guardL (h:Licence p z u a E)(hp:Licence p z r a F): Licence p z (u+r) a (weave E F):=by obtain ⟨j,hj,he⟩:=h.zone; obtain ⟨f,g,hg⟩:=hp.zone; exact ⟨Sum.elim j f,fun i=>Extra.Iteration.Cost.sum (hj i) (g i),fun i=>by cases i; exact he _; exact hg _⟩ -- Cost.sum ambiguous
lemma woven_sum (U:Grid c)(h:Summable (letters E t U))(hp:Summable (letters F t U)): Patron.total (weave E F) t U=Patron.total E t U+Patron.total F t U:=Summable.tsum_sum (f:=letters (weave E F) t U) h hp
end YM.QCD.Reggae
