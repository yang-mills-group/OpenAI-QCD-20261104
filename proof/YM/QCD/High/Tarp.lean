import YM.QCD.High.Pose
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Scale/add proof. Weaken conditional for E heads. exact HASpanic.
variable {ι' μ:Type}
noncomputable def tint (E:Ruby.Hue c N ι) (x:ℝ): Ruby.Hue c N ι:= ⟨E.bud,fun i=>x • E.mean i⟩
def Wick (E:Gem c N ι):Prop:= ∀ i,Nonwrapping (E.addr i).support (E.addr i).site→mud (E.view i 1)=0 ∧∀ x y, IsAffineDirection (E.addr i).site x→ IsAffineDirection (E.addr i).site y→ logHessian ((river c N) ∘ E.view i) x y=0
lemma wakes (g: Grid c→ EvenA c N) (v:ℝ)(x y): logHessian ((river c N)∘ (v • g)) x y=v*logHessian ((river c N)∘g) x y:=by
    rw [hessian_eq,hessian_eq]; let A:Pot su c:= (river c N)∘g; let f:=germ A; rw [show germ ((river c N)∘ (v • g))= v • f from funext fun i=> (river c N).map_smul ..,fderiv_const_smul_field,show fderiv ℝ (v • fderiv ℝ f)= v • fderiv ℝ (fderiv ℝ f) from (fderiv_const_smul_field (f:=fderiv ℝ f) (𝕜:=ℝ) v)]; rfl
variable (G:Gem c N ι)(Y:Ruby.Hue c N β) (b:Flavor N)
lemma tent (h:Purchases Y p.threshold p.B σ w a)(t:ℝ): Purchases (tint Y t) p.threshold p.B σ (|t| *w) a:=by
    let D:=tint Y t; obtain ⟨f,hf,hp⟩:= h.paint; have he:=h.projection; have hh:=h.life; refine ⟨⟨?_,fun i U=>Patron.dolled _ _ (he.real i U),fun i U=>dated _ _ (he.number i U),?_⟩,⟨?_,?_,?_,?_⟩,fun i=> |t| * f i,?_,?_⟩
    · intro i U k; suffices h:sways (Lat.rotates N k) (t • Y.mean i (gauge k U))=t • Y.mean i U by exact congr_arg Subtype.val h
      rw [eSM _ (phare _),show sways (Lat.rotates N k) (Y.mean i (gauge k U))=Y.mean i U from Subtype.ext (he.gauge i U k)]
    · intro s k d h; obtain ⟨e,hV,hU⟩:=he.travel s k d h; exact ⟨e,hV,fun i U=> (eSM _ (phare _) _ _).trans (congr_arg _ (hU i U))⟩
    · intro i U V hv h'; exact congr_arg (t • ·) (hh.bond i U V hv h')
    · exact fun i=>measurable_const.smul (hh.meas i)
    · intro i U hN hZ; apply hh.non i U _ hZ; intro hh; apply hN; exact (congr_arg (t • ·) hh).trans (smul_zero _)
    · exact fun i U=> Territory.club _ _ _ (hh.lives i U)
    · intro i U; change ‖songT a (t • Y.mean i U)‖≤_; rw [map_smul, norm_smul]; exact mul_le_mul_of_nonneg_left (hf i U) (abs_nonneg _)
    intro U; let g:SumBudget (fun i=> |t| * (if U∈Y.bud i then f i*Real.exp (σ*coverNumber p.B (Y.bud i)) else 0)) (|t| *w):=budget_scale (abs_nonneg _) (hp U); simpa only [tint,mul_assoc,mul_ite_zero] using g -- lemma edit
structure Cameo (G:Gem c N ι)(Y:Ruby.Hue c N β)(p:BudgetPoint)(b:Flavor N)(a r u v:ℝ)(w: Grid c→EvenA c N) :Prop where
 cover : Crossing G
 maskG: Wick G
 atoms: Quanta G b
 waveP: Licence p r u a G
 tax : Purchases Y p.threshold p.B r v a
 eyeG (U:Grid c): HasSum (fun i=> Y.mean i U) (w U- Patron.total G p.threshold U)
lemma laced (x:ℝ)(h: Wick G)(hp: Quanta G b): Wick (linen G x) ∧Quanta (linen G x) b:=by
    refine ⟨fun i hh=> ⟨?_,fun y z hX hY=> ?_⟩,fun i h s=>?_⟩
    · have hz:clay c N (G.view i 1)=0:= (h i hh).1
      change clay c N (x • _)=_; rw [show clay c N (x • G.view i 1)=x • clay c N (G.view i 1) from map_smul ((clay c N).restrictScalars ℝ) ..,hz,smul_zero]
    · change logHessian ((river c N) ∘ (x • G.view i)) y z=_; rw [show logHessian _ y z=_ from (wakes (G.view i) x y z), (h i hh).2 y z hX hY,mul_zero] -- match
    change profile _ _ (meter b (x • G.view i 1))=_; rw [show meter b (x • G.view i 1)=x • meter b (G.view i 1) from map_smul ((meter (c:=c) b).restrictScalars ℝ) ..]; change profile (G.addr i).site s (x • _)=_; rw [show profile _ _ (x • meter b (G.view i 1))=x • profile (G.addr i).site s (meter b (G.view i 1)) from map_smul ((profile (G.addr i).site s).restrictScalars ℝ) ..,show profile _ _ (meter b _)=(0:Spike) from hp i h s,smul_zero] -- no contradiction
variable {q' :ℝ}{v v':Grid c→EvenA c N}{Z':Gem c N ι'}{Y':Ruby.Hue c N μ}
lemma cones (X: Gem c N μ)(S:Ruby.Hue c N ι')(h:Cameo G Y p b a t u r v)(hp:Cameo X S p b a t A θ v')(he:0≤ t)(hv:0 <a): Cameo (weave G X) (Ruby.HJoin Y S) p b a t (u+A) (r+θ) (v+v'):=by
    refine ⟨pilot _ _ h.cover hp.cover,fun j=>?_,fibs _ _ _ h.atoms hp.atoms,guardL _ _ h.waveP hp.waveP,joinsM _ _ h.tax hp.tax,fun U=>?_⟩
    · cases j; exact h.maskG _; exact hp.maskG _
    rw [Pi.add_apply,woven_sum _ _ U (permits _ h.waveP hv he _) (permits _ hp.waveP hv he _),add_sub_add_comm]; exact firmsM _ _ _ _ U (h.eyeG U) (hp.eyeG U)
lemma rigH (i:Grid c)(x:ℝ) (h: Licence p t u a G)(hz:0 ≤t)(ha:0 <a):Patron.total (linen G x) p.threshold i=x • Patron.total G p.threshold i:=by
    apply HasSum.tsum_eq; apply (((permits _ h ha hz i).hasSum).const_smul x).congr_fun; intro s; by_cases hh: Healthy p.threshold (G.addr s).support i; · unfold letters; rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ (show Healthy p.threshold ((linen G x).addr s).support i from hh)]; rfl
    unfold letters; rw [masked_ne _ _ _ _ hh,masked_ne _ _ _ _ (show ¬Healthy p.threshold ((linen G x).addr s).support i from hh),smul_zero]
lemma tideζ (x:ℝ)(h:Licence p t u a G): Licence p t (|x| *u) a (linen G x):=by obtain ⟨f,hf,h⟩:=h.zone; rw [← Real.norm_eq_abs]; exact ⟨fun i=>‖x‖ *f i,fun i=>by simpa only [linen,mul_assoc,mul_ite_zero] using budget_scale (norm_nonneg x) (hf i),fun i=>(h i).byScalar _⟩
lemma chase (x:ℝ)(h:Cameo G Y p b a t u r v)(he:0 ≤ t)(hv:0<a): Cameo (linen G x) (tint Y x) p b a t (|x| *u) (|x| *r) (x • v):=by
    obtain ⟨hp,hq⟩:= laced G b x h.maskG h.atoms; refine ⟨clock G x h.cover,hp,hq,tideζ _ _ h.waveP,tent Y h.tax x,fun U=>?_⟩; rw [Pi.smul_apply,rigH G U x h.waveP he hv, ← smul_sub]; exact (h.eyeG U).const_smul x
lemma spinX {d:Bool}[Fintype ι](h:Saline G p a t u d)(he:Crossing G)(hr:0≤t)(hv:0<a)(hp:2 ≤ c.val)(f :Grid c→EvenA c N)(hf:∀ V,(∑ i,sheer G d p.threshold i V)=f V):
      let X:=air G p.B; let Y:= reef X p.threshold d; let Q:=Φ p.B t c*u; Cameo X Y p b a t Q ((Fintype.card (Site c):ℝ)*Q) f:=by
    intro X Y Q; have hh:=tilts G hr hp h; have he':=feeds G p.B he
    refine ⟨he',fun i h=>(noX G p.B i h).elim,fun i h=>(noX G p.B i h).elim,hh.law,nightG X hh he' hv hr,fun V=>?_⟩
    have hx :∑ i,sheer X d p.threshold i V=f V:= (raisedH G _ _ hp _).trans (hf V); rw [← hx]; exact drumH ..
end YM.QCD.High
