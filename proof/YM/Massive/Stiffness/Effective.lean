import YM.Massive.Mass.Terminal
import YM.Massive.Stiffness.Series
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
open Nola Sway OrbitG NormedSpace Creek Grove MeasureTheory
namespace Reference
variable {z a' θ:ℝ}
open YM.Massive (Stiffness.body Stiffness.action)
open YM.Pert
open YM.Massive.Stiffness (fullLog classicalPath)

-- temporarily use Reg.price at the field's other exponent
noncomputable def replacement (p:BudgetPoint) (t:ℝ) (h:0<t) := {p with supportExponent:=t, exponent_pos:=h}
lemma reprise {Y':Lattice.Support c}{Z' : Grid c → ℝ} (hp: P.Regular Y' Z')(a:ℝ)(ha:0<a):
    (replacement P a ha).Regular (Y':Lattice.Support c) (Z': Grid c → ℝ):= ⟨hp.sites,hp.borel,hp.symmetry,hp.smooth,hp.hasDerivs⟩ -- autoImplicit!

variable (Fv: Voice c N)

def correction := fullLog (fun i=> river c N ∘ Fv.P.view i)

variable (X0:Pixel c N) (E : SunR Ω) (v:Train j) (D : PathData su) (B : Clip)
variable (hp : Enn P b' L x η (1/8) (duo Fv.P Fv.K))
variable (hk : P.B = highR L x)
variable (he : X0 = u • red Fv.P Fv.K E P₀ v P D B θ β b 0)
include hp
noncomputable abbrev ℘ (P:BudgetPoint): BudgetPoint := replacement P (1/8) (by norm_num)
lemma summableF (V: Grid c) : Summable (letters Fv.P P.threshold V):= by
  -- fromCoat cap m=0 tell
  apply (IV.fromCoat b' Fv hp (m:=0) (U:=V) 1 (fun a=>?_) zero_le_one).1
  simp only [Nola.tell,pow_zero,one_mul]; apply Real.one_le_exp; positivity

-- directions don't need the b=clip too. interfere `smaller` temp?
def testWave (g:su.Color) (b:Bool)(i j:Axis) : Directions su c := Kinetic.wave g b i j
include hk
lemma pay (g:su.Color)(hG:‖g‖=1)(hn:4 ≤ c.val) (b:Bool) (i j:Axis):
    let v: Directions su c := testWave g b i j; let f:= correction Fv ∘ AnalyticBridge.VerifiedReset.line v;
    |iteratedDeriv 2 f 0|≤(Fintype.card (Site c):ℝ)*(Full.mesh c^3 * Kinetic.geomE (℘ P) * Jets.Touch.chip L x)
    ∧ ∀ v': Directions su c, ContDiffAt ℝ 2 (correction Fv ∘ AnalyticBridge.VerifiedReset.line v') 0:=by
    obtain ⟨k,w,h,hm⟩:= hp; let q:= ℘ P; let E i:= river c N ∘ Fv.P.view i; let A:=Fv.P.addr
    have hx i :P.Regular (A i).support (E i) ∧ P.supBounds (A i).site (A i).support (E i) (k i):= spores _ _ _ (hm i).1 (fun V g=> h.pan.refr.main i V g) (fan_pos L η x).le
    have hp i : q.supBounds (A i).site (A i).support (E i) (k i):= (hx i).2
    have hs i : q.Regular (A i).support (E i):= reprise (hx i).1 _ _
    have he: SumBudget (fun i=> q.mass (A i).support (k i)) ((Fintype.card (Site c):ℝ)*Jets.Touch.chip L x):=by
         have hr:= h.fillP.χ; let p:= Jets.Touch.chip L x; have hz:=budget_over univ _ (fun _=>p) (fun i hi=>hr i); simp_rw [sum_const,card_univ,nsmul_eq_mul] at hz
         refine budget_mono hz (fun i=> mul_nonneg (Real.exp_pos _).le (hx i).2.1) (fun i=>?_); simp only [sum_ite_eq, mem_univ,↓reduceIte]; unfold BudgetPoint.mass q ℘ replacement; change Real.exp ((1/8:ℝ)*coverNumber P.B (A i).support)*k i≤ _; rw [hk]; exact (mul_comm ..).le
    apply And.intro (Massive.Stiffness.series simple hs hp (fun i hi=> ((hm i).2 hi).base.mute hi) he g hG hn b i j).2
    intro v; exact (Massive.Stiffness.rays_smooth hs hp (Summable.of_nonneg_of_le (fun i=> (hp i).1) (fun i=> q.loMass _ _ (hp i).1) he.2.1) v).of_le (le_trans (by norm_num : (2:WithTop ℕ∞)≤((6:ℕ):ℕ∞)) (by exact_mod_cast q.order_ge))
omit hk

lemma river_full {U:Grid c} (hz:flags P.threshold U=∅) :
    mud (Patron.total Fv.P P.threshold U)= -((correction Fv U:ℝ):ℂ):=by -- .re implicit
   have hx:= summableF b' Fv hp U; let V i:= (river c N) (Fv.P.view i U); let w : Fv.ι→ EvenA c N:= letters Fv.P P.threshold U
   have he(i:Fv.ι): w i=Fv.P.view i U:= masked_eq _ _ _ _ (by unfold Healthy; rw [hz];simp)
   have hm(i): clay c N (w i)= -((V i:ℝ):ℂ):=by rw [he]; obtain ⟨p,q,h,_⟩:= hp; have hx: Regal c N (Fv.P.view i U)= Fv.P.view i U:= (h.pan.real _).ease i; change mud (Fv.P.view i U)= _; simpa only [V,Complex.ofReal_neg] using Reggae.realP hx
   have h': HasSum (fun i=>clay c N (w i)) (mud (Patron.total Fv.P P.threshold U)) := (clay c N).hasSum hx.hasSum
   change _= - ((↑(∑' i,V i)):ℂ); rw [← h'.tsum_eq]; simp_rw [hm]
   rw [tsum_neg,Complex.ofReal_tsum]

-- identity for full germ neighborhood
include he
variable (hx:0<u)
include hx
omit hx in
lemma intensity {U:Grid c} (h: flags P.threshold U=∅):
    Massive.Stiffness.body (Cove.light _ ∘ X0) U=(u:ℂ) * (↑(Real.exp (Finch.scent E.Z.page P D B β 0 N U - correction Fv U)):ℂ):=by
   let G:= scent (c:=c) E.Z.page P D B β 0 N; let C : St c:= FieldB Ω E c θ P₀ v + b • 1; let K:= heartS Fv.P P.threshold G C U
   have he' : X0 U=u • exp K:=by rw [he]; unfold red; rw [Pi.smul_apply, High.PrismT.ζpt _ _ _ _ _ h];
   change mud (X0 U)=_
   rw [he',show mud (u • exp K)= (u:ℂ)*mud (exp K) from map_smul (clay c N) (u:ℂ) _, Coda.term]; congr 1; rw [Complex.ofReal_exp]; apply congr_arg
   rw [Complex.ofReal_sub]; unfold K heartS; change clay c N _= _; rw [map_add,map_add,show clay c N (nozzle _ _ _)=0 from Stew.form_card ..,add_zero, show clay c N (baker c N (G U))=(↑(G U):ℂ) from Reggae.gives .., show clay c N (Patron.total Fv.P P.threshold U)= _ from river_full b' Fv hp h]; abel
lemma negative {U:Grid c} (h: flags P.threshold U=∅): Massive.Stiffness.action (Cove.light _ ∘ X0) U= -Real.log u + classicalPath B D β U + (N:ℝ)* Extra.Iteration.action E.Z.page U+ correction Fv U:=by
   unfold Massive.Stiffness.action; rw [intensity P₀ b' Fv X0 E v D B hp he h,← Complex.ofReal_mul, Complex.ofReal_re, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
   unfold scent Reggae.pulse classicalPath; rw [PhysicalNext.Repeat.Pane.crystalline _ _ _ _ _ h]; ring -- check
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.negative
