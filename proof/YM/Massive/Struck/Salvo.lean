import YM.Massive.Struck.Bounds
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable (Y:Code c N)(b b':Flavor N) (K:Grid c→ℝ) (U:St c)
open High.PrismT
lemma murmurs (z:ℂ)(X:EvenA c N)(hz:z≠0): fumes b (z • X)=fumes b X:=by
    unfold fumes; change (clay c N (z • X))⁻¹ • Stew.meter b (z • X)=_; rw [map_smul,map_smul,smul_eq_mul,_root_.mul_inv_rev,smul_smul,mul_assoc,inv_mul_cancel₀ hz,mul_one]; rfl
abbrev leanM (a:Flavor N) (t:ℝ)(F:ℂ→Pixel c N) (z:ℂ): Sheet c:= fumes a (grow t F z 1)
local notation "P!"=> Jets.Touch.fan L ρ x
-- measures up to pose.Time. flag-free health from P.threshold easy.
variable (hv:P.B=highR L x) (he:Desk Y P b L x ρ)(hf: Fare Y P L x ρ A D) (F:ℂ→Pixel c N)(hF:Wing F Y P x K U)
include hf he hF hv
lemma wire_m (z:ℂ) (hz:‖z‖<1) : leanM b' (Rotary.chartR x) F z=Stew.meter b' (heartS Y.master.P P.threshold K U 1)+ z • Stew.meter b' (sting Y P 1)+ Stew.meter b' (shell Y z P 1):=by
    obtain ⟨a,-,-,-,-,ha⟩:=hF.launch; unfold leanM; rw [(ha z hz).2,Pi.smul_apply,murmurs _ _ _ (ha z hz).1]
    unfold Maternal; rw [ζpt _ _ _ _ _ (UVNext.CouplingReset.flags_one ..),High.PrismT.lively, peel Y _ hv he hf _ _ _ hz.le,map_add,map_add,map_smul]
omit hv hF in
lemma hollow (U:Grid c): Holo (fun z:ℂ=> shell Y z P U)∧∀ (i:ℕ),i<2→ Massive.Filament.bead i (fun z=> shell Y z P U)=0:=by
    let Q i (z:ℂ):= z ^ Y.ad i • (letters Y.high P.threshold U i)
    have hs:Summable (fun i=>‖letters Y.high P.threshold U i‖):= (Stew.permits Y.high hf.high.law (fan_pos ..) (by norm_num) U).norm
    have hp i:Holo (Q i):=by unfold Holo Q; fun_prop
    have h z: shell Y z P U=∑' i, Q i z:=tsum_congr fun _=> wireL ..
    have hQ i (z:ℂ)(hz:‖z‖<1): ‖Q i z‖ ≤ ‖letters Y.high P.threshold U i‖ :=by unfold Q; rw [norm_smul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz.le)
    simp_rw [h]; refine ⟨Complex.differentiableOn_tsum_of_summable_norm hs hp isOpen_ball (fun i z hz=> hQ i _ (mem_ball_zero_iff.mp hz)),fun i hi=> (Holo.all i hp hs hQ).unique (hasSum_zero.congr_fun fun j=>?_)⟩ -- .unique order
    unfold Q; rw [bead_mono,if_neg (ne_of_lt (hi.trans_le (he.bottom j)))]
lemma tull : Holo (leanM b' (Rotary.chartR x) F) :=by
    have hp: Holo (fun z:ℂ=> Stew.meter b' (heartS Y.master.P P.threshold K U 1)+ z • Stew.meter b' (sting Y P 1)+ Stew.meter b' (shell Y z P 1)) :=DifferentiableOn.add (by fun_prop) ((Stew.meter (c:=c) b').differentiable.comp_differentiableOn (hollow Y b he hf _).1)
    exact hp.congr (fun z hz=> wire_m Y b b' K U hv he hf F hF z (mem_ball_zero_iff.mp hz))
lemma axisM : Massive.Filament.bead 1 (leanM b' (Rotary.chartR x) F)=Stew.meter b' (sting Y P 1):=by
    let f z:= shell Y z P (1:Grid c); let C:=Stew.meter b' (heartS Y.master.P P.threshold K U 1); let T:= Stew.meter b' (sting Y P 1); let L:=leanM b' (Rotary.chartR x) F; have hq: L=ᶠ[𝓝 (0:ℂ)] ((fun z=>C+z • T)+(Stew.meter b' ∘ f)):= Filter.mem_of_superset (ball_mem_nhds _ zero_lt_one) fun z hz=> wire_m Y b b' K U hv he hf F hF z (mem_ball_zero_iff.mp hz)
    have hp:= hollow Y b he hf 1; have hx: Holo (Stew.meter b' ∘ f):= (Stew.meter (c:=c) b').differentiable.comp_differentiableOn hp.1
    rw [show Massive.Filament.bead 1 (leanM b' _ F)=Massive.Filament.bead 1 ((fun z=>C+z • T)+(Stew.meter b' ∘ f)) from congr_arg ((Nat.factorial 1:ℂ)⁻¹ • ·) (Filter.EventuallyEq.iteratedDeriv_eq 1 hq)]
    have hi: Holo f:=hp.1; rw [bead_add 1 _ hx zero_lt_one,handset 1 (Stew.meter (N:=N) (c:=c) b') hi zero_lt_one,show Massive.Filament.bead 1 f=0 from hp.2 1 (by omega),map_zero,add_zero,bead_first]; swap; · unfold Holo; fun_prop
    exact HasDerivAt.deriv (by simpa only [one_smul] using (((hasDerivAt_id' (0:ℂ)).smul_const T).const_add C))
lemma fore : Sens (Rotary.chartR x) (P!) b' F= Finch.flagRead b' (P!) (sting Y P 1):=by rw [Finch.flagP]; unfold Sens; rw [show Massive.Filament.bead 1 _=Stew.meter b' _ from axisM Y b b' K U hv he hf F hF]; rfl
omit hv hF he in
lemma trim (z:ℝ)(hz:‖z‖<1): ‖flagRead b' (P!) (shell Y z P 1)‖≤D:= by
   have hh(i:Y.B): ‖(z:ℂ)^(Y.ad i)‖≤1:= by rw [norm_pow, Complex.norm_real]; exact pow_le_one₀ (norm_nonneg _) hz.le
   obtain ⟨f,hf,h⟩:= (frozen Y.high _ hh hf.high.law).zone; exact sector_pay b' (wind Y.high _) hf (by norm_num) h (fan_pos L ρ x) -- binds E?
-- high powers untruncated at real radius ≲ε.Parameter.M output. 'mark=False high OK' measured via actual flags not approxim projection. order error. norm estimate.Currency.
lemma guardT (z:ℝ)(hz:‖z‖<1): ‖ (P!)^2*(flagW (leanM b' (Rotary.chartR x) F z)-flagW (fumes b' (origin Y P K U 1))) - z*Sens (Rotary.chartR x) (P!) b' F‖ ≤ D:=by
   let M₀:= heartS Y.master.P P.threshold K U 1; have hM: fumes b' (origin Y P K U 1)=Stew.meter b' M₀:=by unfold Library.origin; rw [ζpt _ _ _ _ _ (UVNext.CouplingReset.flags_one ..)]; exact High.PrismT.lively ..
   rw [hM, wire_m _ _ _ _ _ hv he hf F hF z ((Complex.norm_real z).trans_lt hz),fore Y b b' K U hv he hf F hF]
   have hh := trim Y b' hf z hz
   refine (Eq.trans_le (congr_arg Norm.norm (show _=flagRead b' (P!) (shell Y z P 1) from ?_)) hh)
   rw [Finch.flagP,Finch.flagP]
   -- additivity real
   let L': Sheet c→L[ℝ]ℝ:= by exact (Fintype.card (Site c):ℝ)⁻¹ • (Complex.reCLM.comp ((stowL c).restrictScalars ℝ))
   have hp(X:Sheet c): flagW X=L' X:=by change _= (Fintype.card (Site c):ℝ)⁻¹ *(stow X).re; rw [Finch.far]; field_simp
   let Q:=Stew.meter b' (sting Y P 1); let R:= Stew.meter b' M₀; let F:=Stew.meter b' (shell Y z P 1); simp_rw [hp]; rw [Complex.coe_smul]; change (P!)^2*(L' (R+z • Q+ F)- L' R) - z*((P!)^2*L' Q)=(P!)^2*L' F; rw [map_add L',map_add L',map_smul]; change (P!)^2*( _+ z*L' Q+_-_) - _=_; ring
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.guardT
#print axioms YM.QCD.Struck.Library.axisM
