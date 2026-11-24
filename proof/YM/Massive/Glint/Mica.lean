import YM.QCD.Reef.Galong
import YM.Massive.Glint.Base
import YM.Massive.Struck.Twinkle
/-! Transport orientation under phase-diagonal masses to near-zero momentum comparison. Extends `QCD/Reef/Galong.lean`: keep estimates on origin jets around one actual unmark-geometry history. -/
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
open Nola Sway OrbitG NormedSpace Creek Grove MeasureTheory
namespace IV
variable {z a' θ:ℝ}
lemma spice (Z: Gem c N I)(hp: CrossP Z)(he:Summable (letters Z P.threshold (1:Grid c))): Globe.Mica (Patron.total Z P.threshold 1):=by
    let f i:= Z.view i 1; have hv(i): letters Z P.threshold 1 i=f i:= masked_eq _ _ _ _ (flat_ok ..) -- supply
    have hX(p q:EvenA c N) : p+q=q+p:=add_comm ..
    let R:= Patron.total Z P.threshold 1
    have hz(A: OrbitG (Modes c N))(p:Equiv.Perm I)(he':∀ i,A.passL (f i)=f (p i)): A.passL R= R:=by
        have hx:= (he.hasSum.map A.passL (phare A)); have ht: HasSum (letters Z P.threshold (1:Grid c)∘p) (A.passL R):=hx.congr_fun (fun i=>by change letters Z _ _ _= A.passL (letters Z _ _ i); rw [hv,hv,he'])
        exact (p.hasSum_iff.mp ht).unique he.hasSum -- orientation
    refine ⟨fun i h=> hz (trade (flute _ (diagonal i))) (Equiv.refl _) (fun j=> hp.num j 1 i h),fun i=>hz (trade (Lat.rotates N (fun _=> i))) (Equiv.refl _) (fun j=> ?_),fun p t k h=>?_,hz _ (Equiv.refl _) (fun i=> hp.real i 1)⟩
    · apply Subtype.ext; have hh:= hp.gauge j 1 (fun _=>i); rw [show Lattice.gauge (fun _=> i) (1:Grid c)=1 from ?_] at hh; exact hh
      ext1 i; simp [Lattice.gauge]
    obtain ⟨u,hv⟩:=hp.rays p k t h; exact hz _ u (fun i=>by have hh:= (hv i).2 1; rw [Globe.t_one] at hh; exact hh)
variable {ht t:ℝ}
lemma fromGem (D:Gem c N I)(h: Licence P θ u t D)(C:ℝ)(V:Grid c)(ht:∀ A:Support c,Nola.tell A m ≤ C*Real.exp (θ*coverNumber P.B A))(hV:0<t)(hr:0≤θ)(hC:0 ≤ C): Globe.GrassA (Patron.total D P.threshold V) t m (C*u):=by
    let F:= letters D P.threshold V; have hs:= Stew.permits D h hV hr V
    obtain ⟨f,H,hx⟩:=h.zone; let Y i:= f i* Real.exp (θ*(coverNumber P.B (D.addr i).support:ℝ)); let d:= (Fintype.card (Site c):ℝ)
    have hY: SumBudget Y (d*u):=by
         have hz:= budget_over univ _ (fun _=>u) (fun x hx=>H x); simp_rw [sum_const,card_univ,nsmul_eq_mul] at hz
         refine budget_mono hz (fun i=> mul_nonneg (hx i).travel (Real.exp_pos _).le) fun i=>?_ ; simp only [sum_ite_eq,mem_univ, ↓reduceIte]; exact le_rfl
    have h' i: band locationP (F i).val t m ≤ C*Y i:=by
         unfold F letters; by_cases hk:Healthy P.threshold (D.addr i).support V
         · rw [masked_eq _ _ _ _ hk]; apply (Nola.bandPay locationP _ t hV (D.addr i).support m (show _ from (hx i).gated V)).trans; exact (mul_le_mul ((Stew.shot (Stew.lens _) _ _ hV).trans ((hx i).sizeU V hk)) (ht _) (zero_le_one.trans (tell_one ..)) (hx i).travel).trans_eq (by unfold Y; ring)
         rw [masked_ne _ _ _ _ hk,show (0:EvenA c N).val=0 from rfl,band_zero]; exact mul_nonneg hC (hY.1 i)
    change band locationP (Cove.light _ (∑' i,F i)) t m≤ _; exact (bandSerial _ _ _ hV (hs.hasSum.map (Cove.light _) (lightC _)) (budget_mono (budget_scale hC hY) (fun i=> sum_nonneg fun j _=> grains locationP _ hV j) h')).trans (le_of_eq (by ring))
open Struck Library
-- Mica on EvalE at real amplitude
variable (Y0:Code c N)(hp: Desk Y0 P b' L x θ)
omit hp
lemma reelWind (G:Gem c N I)(W:I→ℕ) (h: CrossP G)(hc:∀ (p:Strut c)(k:Spike)(g: Site c→ℂ), Strut.Warrant p g k→ ∃ e: Equiv.Perm I,∀ i,W (e i)= W i ∧ G.addr (e i)= Patron.rotateL (G.addr i) p ∧∀ U, Diode N p k g (G.view i (Strut.sky p U))=G.view (e i) U)(z:ℝ): CrossP (Library.wind G (fun i=>(z:ℂ)^W i)):=by
   let P:=fun i=>(z:ℂ)^W i; let f:=Library.wind G P; refine ⟨fun i=> Carrier.shadeColor (G.view i) (P i) (h.gauge i),fun i U=> Pith.phase_c _ _ (h.num i U),fun i U=> ?_,?_⟩
   · let v:= (z^W i); change Regal _ _ (P i • _) = _; have hp:= h.real i U; rw [show f.view i U=P i • _ from rfl,show P i=(v:ℂ) from (Complex.ofReal_pow ..).symm,Complex.coe_smul, eSM _ (OrbitG.phare _) v, hp] -- simplify maybe RHS not f.view
   intro p k g h; obtain ⟨e,hv⟩:=hc p k g h; refine ⟨e,fun i=>⟨(hv i).2.1,fun U=> ?_⟩⟩; change Diode _ _ _ _ (P i • _) = P (e i) • _; have hh:= (hv i).2.2 U; rw [show P (e i)=P i by unfold P; rw [(hv i).1],show Diode N p k g (P i • _)= P i • Diode N p k g _ from Pith.complexFactor ..,hh] -- fill implicitly?
lemma CWjoin (G:Gem c N I)(X:Gem c N J')(h:CrossP G)(hp:CrossP X):CrossP (weave G X):= (Carrier.lurkWeave G X (fun _=>0) (fun _=>0) (Carrier.fromG G 0 h) (Carrier.fromG X 0 hp)).1
include hp
lemma blockPhase (z:ℝ): CrossP (Y0.EvalE z):=by
   have hr {J:Type}(G: Gem c N J)(h: CrossP G): CrossP (Library.wind G fun _=>(z:ℂ)):=by
        have hl:= reelWind G (fun _=>1) h (fun p k g he=>by obtain ⟨e,hx⟩:= h.rays p k g he; exact ⟨e,fun i=>⟨rfl,hx i⟩⟩) z; simpa only [pow_one] using hl
   have hs:= hp ; exact CWjoin _ _ (Carrier.crossP _ (Carrier.sym _ hs.base).1) (CWjoin _ _ (hr Y0.canonical (Pith.rentCross c _)) (CWjoin _ _ (hr Y0.low hs.arg) (reelWind Y0.high _ hs.eve hs.carries z))) -- names
end IV
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.IV.fromGem
#print axioms YM.QCD.Acre.Rails.IV.blockPhase
