import YM.QCD.Entr.Penny
/-! # exact counterterm projection INCLUDING finite bookkeeping. Structural tariffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume
variable {Γ:Silo c}{A: BankP c}{U:St c}
variable {ι β:Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
lemma boost (h:AnchorT G p a u q)(he:q≤r): AnchorT G p a u r:=by obtain ⟨f,hf,h⟩:=h.peg; exact ⟨f,fun i=>budget_loosen (hf i) he,h⟩
lemma formH (h:AnchorT G p a u q)(hp:AnchorT F p a u r): AnchorT (weave G F) p a u (q+r) :=by
    obtain ⟨f,hf,h⟩:=h.peg; obtain ⟨g,hg,hp⟩:=hp.peg; exact ⟨Sum.elim f g,fun i=>Extra.Iteration.Cost.sum (hf i) (hg i),fun i=>by cases i; exact h _; exact hp _⟩
noncomputable def linen (x:ℝ):Gem c N ι:= ⟨G.addr,fun i=>x • G.view i⟩
lemma clock (x:ℝ)(hp:Crossing G): Crossing (linen G x):=by
    constructor
    · refine ⟨fun i U k=> ?_,fun i U=>dated _ _ (hp.blank.num i U), fun i U=> Patron.dolled _ _ (hp.blank.real i U)⟩
      suffices h : sways (Lat.rotates N k) ((linen G x).view i (gauge k U))=(linen G x).view i U by exact congr_arg Subtype.val h
      exact (eSM _ (phare _) x (G.view i (gauge k U))).trans (congr_arg _ (show sways (Lat.rotates N k) (G.view i (gauge k U))=G.view i U from Subtype.ext (hp.blank.gauge i U k)))
    intro s k g h; obtain ⟨e,hv⟩:=hp.rays s k g h; exact ⟨e,fun i=> ⟨(hv i).1, fun U=> (eSM _ (phare _) _ _).trans (congr_arg _ ((hv i).2 U))⟩⟩
lemma sizeζ (x:ℝ)(h:AnchorT G p a u q):AnchorT (linen G x) p a u (|x| *q):=by
    obtain ⟨f,hf,h⟩:= h.peg; rw [← Real.norm_eq_abs]; refine ⟨fun i=> ‖x‖*f i, fun i=>?_ , fun i=> ⟨(h i).1.byScalar _,fun U=>?_⟩⟩
    · let Y j:= if (G.addr j).site=i then f j*Real.exp (u*coverNumber p.B (G.addr j).support) else 0; have hp := budget_scale (norm_nonneg x) (hf i); simpa only [linen, ← mul_ite_zero,mul_assoc] using hp -- edit
    rw [← measures,show ((linen G x).addr i).site=(G.addr i).site from rfl,show needle _ _ a ((linen G x).view i U)=x • (needle (G.addr i).site N a (G.view i U)) from map_smul ((needle (G.addr i).site N a).restrictScalars ℝ) ..,norm_smul,measures]; exact mul_le_mul_of_nonneg_left ((h i).2 U) (norm_nonneg _)
lemma unitζ (z: SampleX)(x:Site c)(y:ℝ): unitM (linen G y) b x z=y • unitM G b x z:=by
   funext i; by_cases hz:x=(G.addr i).site; swap; · unfold unitM; rw [if_neg (show ¬ x=((linen G y).addr i).site from hz)]; simp only [Pi.smul_apply]; rw [if_neg hz,smul_zero]
   unfold unitM; rw [if_pos (show x=((linen G y).addr i).site from hz)]; simp only [Pi.smul_apply]; rw [if_pos hz]; unfold Stew.lane Stew.mote; by_cases h: Nonwrapping (G.addr i).support (G.addr i).site; · rw [if_pos (show Nonwrapping _ _ from (show Nonwrapping ((linen G y).addr i).support ((linen G y).addr i).site from h)),if_pos h]; change profile _ z (meter _ _)= _; exact map_smul (((profile (G.addr i).site z).comp (meter b)).restrictScalars ℝ) y (G.view i 1)
   rw [if_neg h,smul_zero, if_neg (show ¬ Nonwrapping _ _ from (show ¬Nonwrapping ((linen G y).addr i).support ((linen G y).addr i).site from h))]
lemma tillζ (y:ℝ): till (linen G y) b 0=y • till G b 0:=by funext p; unfold till; rw [unitζ]; change (∑' i,y • unitM G b 0 p i)=y • _; rw [tsum_const_smul'']
lemma tune_add (h:Licence p u q a G)(hp:Licence p u r a F)(he:0<a)(hz:0≤u): till (weave G F) b 0=till G b 0+till F b 0:=by
    obtain ⟨f,hf,h⟩:=h.zone; obtain ⟨j,hJ,hp⟩:=hp.zone; funext s; unfold till; apply Summable.tsum_sum (f:=unitM (weave G F) b 0 s)
    · exact concession G b (costsE G b (sumRide _ _ _ hf (fun i=>(h i).travel) hz) he (fun i=>(h i).sizeU 1 (flat_ok ..)) s) _
    exact concession F b (costsE F b (sumRide _ _ _ hJ (fun i=> (hp i).travel) hz) he (fun i=>(hp i).sizeU 1 (flat_ok ..)) s) _
noncomputable def bandQ : (SampleX→Spike)→L[ℝ]ℝ:=LinearMap.toContinuousLinearMap { toFun:=qMass,map_add':=fun _ _=>rfl,map_smul':=fun z p=> (show (((z • p) none) (0,0) (0,0)).re= _ from by change (z • (p none (0,0) (0,0))).re=_; rw [Complex.smul_re]; rfl) }
noncomputable def bandW : (SampleX→Spike)→L[ℝ]ℝ:=sparkL.comp (LinearMap.toContinuousLinearMap { toFun:=Jot, map_add':=fun _ _=>by dsimp [Jot]; abel,map_smul':=fun z _=>by dsimp [Jot]; rw [smul_sub] }) -- placeholder
lemma awake (p:SampleX→Spike):bandW p=qWave p:= (wake p).symm
lemma hauteur (N:ℕ):∃ K:ℝ,1≤ K ∧∀ (c:Side)(ι:Type)(E:Gem c N ι)(p:BudgetPoint) (u Z v:ℝ), Licence p u Z v E →0 < v→0 ≤ u →∀ b:Flavor N, v^2*|qMass (till E b 0)|≤K*Z ∧ v^2*|qWave (till E b 0)|≤K*Z :=by
    obtain ⟨K,hK,H⟩:= Stew.preMoment; refine ⟨K+K,by linarith,fun c ι E p u Z v h hv hu b=>?_⟩
    obtain ⟨f,hf,H'⟩:= h.zone; have he:=zero_le_one.trans hK; have h:= diligent E b hf H' hv hu hK H; let X:=till E b 0
    refine ⟨(mul_le_mul_of_nonneg_left (crops X).1 (sq_nonneg v)).trans ((h _ _).trans ?_),?_⟩
    · have hh: 0 ≤ Z:= budget_nonneg (hf 0); nlinarith
    apply (mul_le_mul_of_nonneg_left (crops X).2 (sq_nonneg v)).trans; rw [mul_add,add_mul]; exact add_le_add (h _ _) (h _ _)
end YM.QCD.Entr
