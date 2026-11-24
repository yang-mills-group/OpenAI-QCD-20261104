import YM.QCD.Reggae.Fresca
/-! # Tax-purchased turn entrants. Keep Quanta & the reduced Hessian. Commute accounting -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Reggae
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{p:BudgetPoint}{z u a r t:ℝ}{i j x:Site c}
open Port AnalyticBridge.VerifiedReset Collection Extra.Iteration Footprint Progress.DirectedRecipe Ovens
variable {ι ι' :Type} (E: Gem c N ι)(b:Flavor N)
structure Quartz (E: Gem c N ι) : Prop where
 face i : mud (E.view i 1)=0
 van i : Nonwrapping (E.addr i).support (E.addr i).site→ ∀ x y, IsAffineDirection (E.addr i).site x→ IsAffineDirection (E.addr i).site y→ logHessian ((river c N) ∘ E.view i) x y=0
lemma toe (x:ℝ): river c N (baker c N x)= -x:=by change -(mud _).re=_; rw [gives]; rfl
lemma taleP (x:ℝ): river c N (ocean c N x)=x:=by unfold ocean; rw [ContinuousLinearMap.neg_apply,map_neg,toe,neg_neg]
-- For ALL winding tags pickups must subtract flats
noncomputable def ostinato (v:Pipes su c)(X:Tap su c)(N:ℕ): Gem c N ℕ:=⟨v.reg,fun i=> (ocean c N) ∘ X.regular i⟩
noncomputable def riff (v:Pipes su c)(X:Tap su c)(N:ℕ): Ruby.Hue c N ℕ:=⟨v.softer,fun i=> baker c N ∘ X.logarithm i⟩
variable (P:Pipes su c)(X:Tap su c)(h:Payments.Fittings X P p)
local notation "S0"=> ostinato P X N
include h
lemma visa : Crossing (S0) :=by
    refine ⟨⟨fun i U k=> ?_, fun i U W hv=> thorough ..,fun i U=> thorough ..⟩,?_⟩
    · suffices g : sways (Lat.rotates N k) (ocean c N (X.regular i (gauge k U)))=ocean c N (X.regular i U) by exact congr_arg Subtype.val g
      rw [show X.regular i (gauge k U)=X.regular i U from (h.regular.smooth i).symmetry k U]; exact thorough ..
    intro s k g hh; obtain ⟨e⟩:=h.moves s.1 s.2; refine ⟨e.ep,fun i=> ⟨?_,?_⟩⟩
    · change P.reg _= rotateL (P.reg i) s; have he:(P.reg (e.ep i)).site=act s (P.reg i).site:= e.reg_site i; have hv:(P.reg (e.ep i)).support=(P.reg i).support.image (act s):=e.reg_support i; cases h1:P.reg (e.ep i) with | mk a b hp=> rw [h1] at he hv; unfold rotateL; congr
    intro V; change Diode N s k g (ocean _ _ (X.regular i (sky s V)))=ocean _ _ (X.regular (e.ep i) V); rw [show X.regular (e.ep i) V=X.regular i (sky s V) from e.valuesE i V]; exact thorough ..
lemma ready_rose : Quartz (S0):=by
    refine ⟨fun i=>?_,fun i h' x y he ht=>?_⟩
    · have he:X.regular i 1=0:=h.regular.at_flat i; change clay c N (ocean c N (X.regular i 1))=_; rw [he,map_zero,map_zero]
    rw [show (river c N) ∘ (S0).view i=X.regular i from funext fun V=> taleP _]; exact h.regular.vanish i h' x y he ht
omit h in
lemma shipX : Quanta (S0) b:=by intro i h' j; rw [show feeF b ((S0).view i 1)=0 from reduceF _ _]; exact map_zero (profile (P.reg i).site j)
lemma readySoft : (riff P X N).Tall p.threshold ∧ (riff P X N).Garish:=by
    refine ⟨⟨fun i V U hh z=> congr_arg (baker c N) (h.looks i V U hh z),fun i=> (baker c N).continuous.measurable.comp (h.reads i),fun i U hh => ?_,fun i U=> gates ..⟩,⟨fun i U k=>?_,fun i U=>through ..,fun i U W hp=>through ..,?_⟩⟩
    · refine h.visits _ _ fun he=>hh ?_; exact (congr_arg (baker c N) he).trans (map_zero _)
    · suffices g : sways (Lat.rotates N k) (baker c N (X.logarithm i (gauge k U)))=baker c N (X.logarithm i U) by exact congr_arg Subtype.val g
      rw [h.steady i k U]; exact through ..
    intro s k g hh; obtain ⟨e,h1,h2⟩:=h.carries s.1 s.2; refine ⟨e,h1,fun i U=>?_⟩; change Diode N s k g (baker c N (X.logarithm i _))=baker c N _; rw [show (X.logarithm (e i)) U= _ from h2 U i]; exact through ..
omit h
lemma visor {c':ℕ →ℝ} (U:Grid c)(hv : ∀ i V, ‖X.logarithm i V‖ ≤ c' i)(hh:Ac.Hit P.softer p.B c' (p.supportExponent+1) t) : HasSum (fun i=>(riff P X N).mean i U) (baker c N (∑' i,X.logarithm i U)):=by
    have hs : Summable c':= Loom.fishes P.softer _ hh (fun i => (norm_nonneg _).trans (hv i 1)) (by linarith [p.exponent_pos]) (fun i _=> P.sites i)
    exact (baker c N).hasSum (Summable.of_norm_bounded hs (fun i=> hv i U)).hasSum
lemma rose_sum (U:Grid c)(he:Summable (letters (S0) p.threshold U)): Patron.total (S0) p.threshold U=ocean c N ((P.pours X).additive p U):=by
    let A:= P.pours X; let B:= A.regularOccurrence p
    let F:= letters (S0) p.threshold U; have hh i:river c N (F i)=B i U:=by
       unfold F; change river c N (masked p.threshold (P.reg i).support (ocean c N ∘ _) U)=masked p.threshold (P.reg i).support (X.regular i) U; rw [masker,show river c N ∘ (ocean c N ∘ X.regular i)=X.regular i from funext fun U=>taleP _]
    have hx :Summable fun i=> B i U:=((river c N).summable he).congr hh; have hJ : HasSum F (ocean c N (A.additive p U)):=by
       apply ((ocean c N).hasSum hx.hasSum).congr_fun; intro i; unfold F letters; change masked _ (P.reg i).support _ _=_; by_cases hv: Healthy p.threshold (P.reg i).support U
       · rw [masked_eq _ _ _ _ hv]; change ocean _ _ _= ocean _ _ _ ; exact congr_arg (ocean c N) (masked_eq _ _ _ _ hv).symm
       rw [masked_ne _ _ _ _ hv,show B i U=0 from masked_ne _ _ _ _ hv,map_zero] -- lhs/ref orientation
    exact hJ.tsum_eq
end YM.QCD.Reggae
