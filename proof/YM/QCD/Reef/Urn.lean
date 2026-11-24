import YM.QCD.Reef.Poise
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
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
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace IV
open MeasureTheory Sector Globe
lemma harmless (P:StepData c f)(hp:β>0): 1 ≤ Sector.prefactor P su β:=by
    unfold Sector.prefactor; apply one_le_pow₀; apply le_trans inv_one.symm.le; apply inv_anti₀ (P.penaltyZ_pos β); unfold StepData.penaltyZ
    have h : Continuous (P.penaltyWeight (G:=su) β):=by unfold StepData.penaltyWeight; fun_prop
    apply (integral_mono (f:=P.penaltyWeight β) (μ:=su.probHaar) (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const (1:ℝ)) ?_).trans (le_of_eq (by simp)) -- arg?
    intro x; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (by have h:=P.kernel.penalty_pos; exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hp]) h.le) (su.price_range _).1
lemma weight_rate (X:ℝ)(he:(m:ℝ) ≤ Fintype.card (Site c)*u) (hp:0<X)(ht:X ≤1) (hz:X≤ y): expo (-(u*Real.log X)) c ≤ y^m:=by
    apply le_trans _ (pow_le_pow_left₀ hp.le hz m); nth_rw 2 [← Real.exp_log hp]; rw [← Real.exp_nat_mul]; unfold expo; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonpos_right he (Real.log_nonpos hp.le ht)] -- nth
lemma minimal (Ñ:ChartRatio su)(h:LocalRatio Ñ)(v:ℝ)(hp:0<v):∃ Z:ℝ,∀ (c f:Side)(U:StepData c f)(p:ℝ),0<p→p≤v→∀ F:Forest U.ratio,expo Z f≤ Fare.solar F Ñ p:=by
   let X:= Real.sqrt (2*Real.pi)*gStep v; have hx:0<X:= mul_pos (by positivity) (inv_pos.mpr (Real.sqrt_pos.2 hp)); let T:= min X 1; let P:=min Ñ.scale 1; let u:= 4*(Fintype.card su.ColorIndex:ℝ)
   let a:= -(u*Real.log T); let b:= -(4*Real.log P); refine ⟨a+b,fun c f U p he hv F=>?_⟩; have h': Fintype.card F.Free ≤ Fintype.card (Site f)*4:=by
       have hh:Fintype.card (Edge (Site f))=Fintype.card (Site f)*4:=Fintype.card_prod ..|>.trans (by simp [Axis]); exact (Fintype.card_le_of_injective _ (Subtype.val_injective (p:=fun i=>i∉ F.trunks))).trans hh.le
   have hp : expo a f≤ (Real.sqrt (2*Real.pi)*gStep p)^Fintype.card (Precision.Key F su):=by
       apply weight_rate T _ (lt_min hx zero_lt_one) (min_le_right ..) ((min_le_left ..).trans (mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.2 he) (Real.sqrt_le_sqrt hv)) (by positivity))); unfold u Precision.Key; rw [Fintype.card_prod]; push_cast; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h') (Nat.cast_nonneg _)
   unfold Fare.solar; rw [show expo (a+b) f=expo a f*expo b f from ?_]; refine mul_le_mul (hp.trans (le_mul_of_one_le_left ((Real.exp_pos _).le.trans hp) (harmless U he))) (weight_rate P (by exact_mod_cast h') (lt_min h.scale zero_lt_one) (min_le_right ..) (min_le_left ..)) (Real.exp_pos _).le (mul_nonneg (prefactor_pos p).le ((Real.exp_pos _).le.trans hp))
   unfold expo; rw [mul_add,Real.exp_add]
noncomputable def bear (L:Side):ℝ:= (L.val:ℝ)^4
lemma bear_pos : 0< bear L:= by unfold bear; exact pow_pos (by exact_mod_cast L.property) _
lemma tourC : (Fintype.card (Site (finC O B (j+1) k)):ℝ)=Fintype.card (Site (finC O B j k))*bear O.L:=by rw [site_card, site_card,powerV]; push_cast; rw [mul_pow]; rfl -- site ns?
lemma tour_c : expo x (finC O B (j+1) k)=expo (bear O.L*x) (finC O B j k):=by unfold expo; rw [tourC]; congr 1; ring
lemma reb (τ: Policy Q T'.top N)(he:∀ u,x≤u→Shade O.L τ.t u) :∃ Y:ℕ→ℝ,∀ (B:SparkMesh)(k i:ℕ),(let u:=run O.L (tallyK O.L x (i+1));∀ p:ℝ,u/2≤p→p≤2*u → TourV Y O B k i ≤ Fare.solar (hint O B k i T') Q.table p):=by
     let u i:= run O.L (tallyK O.L x (i+1)); have hu (i:ℕ):0<u i:=(he _ (matters ..)).value; choose K H using fun i:ℕ=> minimal Q.table Q.table_exists (2*u i) (by specialize hu i; positivity)
     refine ⟨fun i=>bear O.L*K i,fun B k i=>?_⟩; intro t p h₀ h₁; unfold TourV; rw [← tour_c]; exact H i _ _ _ p ((half_pos (hu i)).trans_le h₀) h₁ _
noncomputable def leafZ (n:ℕ):ℝ:= 2*((Fintype.card Lat.Fiber:ℝ)* n)
lemma leafZ_pos (p:Flavor n):0<leafZ n:=by unfold leafZ; have he:0<(n:ℝ):= Nat.cast_pos.mpr (by have h:=p.isLt; omega); apply mul_pos (by norm_num) (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) he)
lemma gain_p (ht:0<x):gain x c N=expo (-(leafZ N*Real.log x)) c:=by
    unfold Rain.gain expo leafZ; nth_rw 1 [← Real.exp_log ht]; rw [←Real.exp_nat_mul]; congr 1; simp only [Cove.Keys,Modes,Lat.Row,Flavor,Fintype.card_fin,Fintype.card_prod,Pairs,Fintype.card_sum]; push_cast; ring
noncomputable def toga (T:Policy Q T'.top N)(o: Target.Order su W)(P:Patch)(y x:ℝ):ℝ:= -(bear P.L*(Fintype.card Lat.Fiber:ℝ)*N*Real.log T.X.Q)+y+bear P.L*(4*Fintype.card su.ColorIndex)*o.ample/2+flowM P.L (run P.L x)
lemma goodness (T:Policy Q T'.top N)(hT:0<T.X.Q) : glossy (RushK O B k j T') T o (hint O B k j T') O.L (expo y (finC O B j k)) x=expo (toga T o O y x) (finC O B j k):=by
    unfold glossy toga expo; nth_rw 1 [← Real.exp_log hT]; rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ←Real.exp_add,←Real.exp_add,←Real.exp_add]; congr 1; simp only [Tubular,Pressure.Bond,Edge,Axis,Lat.Row,Nat.cast_mul,Fintype.card_prod,Fintype.card_fin,Nat.cast_ofNat]; rw [tourC]; ring
lemma gainQ (O:Patch)(v:ℕ→ℝ)(p:ℕ→ℝ)(G₀:ℕ→ℝ)(K: Policy Q T'.top N)(hK:0<K.X.Q): gain (1/4) (finC O B j k) N*(glossy _ K o (hint O B k j T') O.L (TourV p O B k j) (tallyK O.L x j) / (TourV v O B k j)*(TourV G₀ O B k j)) =expo ((-(leafZ N*Real.log (1/4)))+(toga K o O (p j) (tallyK O.L x j)- v j+G₀ j)) (finC O B j k):=by unfold TourV; rw [goodness B K hK,gain_p (by norm_num : 0<(1/4:ℝ))]; unfold expo; rw [← Real.exp_sub,←Real.exp_add,← Real.exp_add]; ring_nf
end IV
end Rails
end YM.QCD.Acre
