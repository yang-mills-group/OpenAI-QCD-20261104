import YM.QCD.High.Stroll
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
open Finch Calm Stem Push.BetaTransport Ring0 Jets.Touch Collection WilsonStartup
variable (b:Flavor N){G:Gem c N ι} {Y:Ruby.Hue c N β}{K:PathData su}{O:Clip}{W: St c}
namespace PrismT
local notation "S0"=>EvenA c N
open Acre Rails Stew.Project
lemma bank (F:Rail c N β)(U:Grid c)(t:ℝ)(h:flags t U=∅):heartK F t U=1:=by
   unfold heartK; rw [tsum_eq_single ∅]
   · rw [Ruby.tK,if_pos ⟨(fun _ hi=> (notMem_empty _ hi).elim),by simp [h]⟩,prod_empty]
   intro i hi; obtain ⟨x,hx⟩:=nonempty_iff_ne_empty.mpr hi; obtain ⟨j,hj⟩:=(F.addr x).alive; unfold Ruby.tK; split; next he=> have hz:i.biUnion (Ruby.oriD F)=∅:=he.2.symm.trans h; exact (Finset.notMem_empty _ (hz ▸ subset_biUnion_of_mem (Ruby.oriD F) hx hj)|>.elim)
   next _=> rfl
lemma ζpt (p:ℝ)(x :Patron.Rail c N β) (U: St c)(W:Pot su c)(V: Grid c)(h':flags p V=∅): scoreV G x p W U V=exp (heartS G p W U V):=by rw [scoreV,bank x V p h',mul_one]
-- normalized.T.Motion.
abbrev glaze (A:S0):ℝ:=Real.log ‖mud A‖
lemma railM (s:ℝ)(q:S0)(he:0<s)(h:mud q≠0): glaze (s • q)=Real.log s+glaze q:=by
    change Real.log ‖clay c N ((s:ℂ) • q)‖= _; rw [map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg he.le]; change Real.log (s*‖mud q‖)=_; rw [Real.log_mul he.ne' (norm_pos_iff.mpr h).ne']
noncomputable def Roll (K:ℕ→Atom su 2)(P:BudgetPoint)(F:PathData su)(O:Clip)(G: Grid c→EvenA c N): Pot su c:= fun x=> Finch.scent K P F O 0 0 N x-glaze (G x)
variable {Z:ℕ→Atom su 2}{νμ:PlaqAxes} {Y':Rail c N β}
local notation "Qp"=> Finch.scent Z p K O
lemma sweet (R: ℕ→Atom su 2) (G:Gem c N ι)(Y:Patron.Rail c N β)(P:ℝ)(A:St c)(V:Grid c)(h:flags p.threshold V=∅): Roll R p K O (scoreV G Y p.threshold (Finch.scent R p K O P 0 N) A) V=P • Push.BetaTransport.kinetic K O p V + Ring0.gaugeF G p V:=by
    let k:= scoreV G Y p.threshold (Finch.scent R p K O P 0 N) A; let σ:=Finch.scent R p K O P 0 N V
    unfold Roll glaze; rw [ζpt _ _ _ _ V h,Coda.term, Complex.norm_exp,Real.log_exp]; change _-(clay c N (baker c N σ+ nozzle c N (A V)+ _)).re=_; rw [map_add,map_add,show clay c N (nozzle c N (A V))=0 from Stew.form_card .., add_zero,show clay c N (baker c N σ)= _ from gives (N:=N) (c:=c) σ, Complex.add_re]; push_cast
    unfold σ; unfold scent Reggae.pulse; change _= _+ - (mud (Patron.total G p.threshold V)).re; rw [channels_split _ (b:=0),channels_split _ (b:=P)]; change _ = P*_+ -((clay c N) _).re; rw [Complex.ofReal_re]; ring -- far.Green.Verb.
variable {A₂ B₂:Pot su c}{d' a' x' v' μ' M' H' :ℝ}(W' : Sheet c)
lemma plusζ (h:PulseS p νμ su A₂ t a v')(hp:PulseS p νμ su B₂ u d z') :PulseS p νμ su (A₂+B₂) (t+u) (a+d) (min v' z'):=by
    refine ⟨lt_min h.upT hp.upT,fun i hi=>?_⟩; rw [glow_plus,add_sub_add_comm]; apply (abs_add_le ..).trans; rw [add_mul]; exact add_le_add (h.fees _ ⟨hi.1,hi.2.trans (min_le_left ..)⟩) (hp.fees _ ⟨hi.1,hi.2.trans (min_le_right ..)⟩)
lemma scaleζ (h:PulseS p νμ su A₂ t a v')(r:ℝ)(he : |r| *a≤ ε):PulseS p νμ su (r • A₂) (r*t) ε v':=by
   refine ⟨h.upT,fun w hw=>?_⟩; rw [glow_scale,←mul_sub,abs_mul]; apply (mul_le_mul_of_nonneg_left (h.fees _ hw) (abs_nonneg _)).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right he hw.1.le
lemma scroll (h:PulseS p νμ su (Push.BetaTransport.kinetic K O p (n:=c)) t a v')(hp:PulseS p νμ su (Ring0.gaugeF G p) u d z')(ht:Lab0 su c p νμ θ)(he:|r| *a ≤ ε): PulseS p νμ su (Roll Z p K O (scoreV G Y' p.threshold (Finch.scent Z p K O r 0 N) W)) (r*t+u) (ε+d) (min θ (min v' z')):=by
    let hf:=plusζ (scaleζ h r he) hp; refine immigrate hf (lt_min ht.1 hf.upT) (min_le_right ..) (fun w hw=>?_); exact pulseAgree p.threshold_le (fun U hu=>sweet _ G Y' r _ _ hu) ht ⟨hw.1,hw.2.trans (min_le_left ..)⟩
variable (f:S0)
abbrev tollM (j:Bool)(b: Flavor N)(A:S0):ℝ:=unitF j c (fumes b A)
lemma spoke (Z:Grid c→ℝ)(G:Gem c N ι)(Y:Rail c N β)(P:BudgetPoint)(W: St c)(t:ℝ) (j:Bool) : tollM j b (scoreV G Y P.threshold Z (W+t • 1) 1) =unitF j c (W 1)+ (if j then 0 else t)+ unitF j c (meter b (Patron.total G P.threshold 1)) :=by
    unfold tollM; rw [ζpt _ _ _ _ 1 (UVNext.CouplingReset.flags_one ..),lively,heartS,map_add (meter (c:=c) b),map_add (meter (c:=c) b),show meter b (baker c N (Z 1))=0 from Reggae.reducible ..,zero_add,show meter b (nozzle c N _)=(W+t • 1) 1 from forceP _ b,map_add]; change unitF j c (_+t • (1:Sheet c)) +_= _; rw [map_add,map_smul,costOne]; split <;> simp
end PrismT
end YM.QCD.High
