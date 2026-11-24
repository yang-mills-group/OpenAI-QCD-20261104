import YM.Massive.Spire.Prospect
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
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
namespace Stratum.Spire
open Rails
open Fog.Mist YM.Massive.Stratum
variable {cB:ℝ} {α β N₁:ℝ} {θ:ℝ} {c f C L:Side}
namespace Client
variable {R:Rock j}{F₀:Flavor N}{χ:Chi} (P₀: Client j R N F₀ χ)
local notation "Gₚ"=> passportM j P₀.good
variable (A:AtlasH R (passportM j P₀.good) P₀.guide.table) (X:∀ i, SlotH P₀ θ A i)
abbrev precursor (x:ℝ)(i:ℕ):=fallback (A.length i) (A.scale x i)
lemma season (x:ℝ)(i:ℕ): run (A.length i) (precursor P₀ A x i)= A.scale x i:= fall ..
lemma second (x:ℝ)(i:ℕ): run (A.length i) (A.scale x i)=A.scale x (i+1) :=(A.eras ..).symm
open AtlasH
abbrev Live (x:ℝ): Prop:=∀ i, Book.Alive P₀ (A.path i) (X i) (precursor P₀ A x i)

structure Terrace (B:SparkMesh)(x:ℝ)(n:ℕ) where
  ground: Live P₀ A X x
  mesh:ℕ→SparkMesh
  W:Survey A mesh n
  straight : Align A B mesh n
  firsts :∀ i:ℕ,i<n →∀ j:Stars, (mesh i).n j.val= stellar (head (A.length i) (X i).k0 (A.scale x i)) j.val
  real_cap :∀ i:ℕ,i<n →∀ j:ℕ,2*style (A.length i) (X i).k0 (A.scale x i)< ((mesh i).n (j+5)).val

lemma occupies (x:ℝ)(n:ℕ)(h:Live P₀ A X x):∀ᶠ k:ℕ in atTop, Nonempty (Terrace P₀ A X (accord k) x n):=by
   filter_upwards [plane A n (fun i=> (X i).k0) (A.scale x)] with k hk
   obtain ⟨S,hs,hS⟩:=hk
   have hh(i:ℕ)(hi:i < n): reachM (A.path i).patch (S i):=by
      have hx:= (h i).structureM; rw [season] at hx
      intro j; exact (sisterP (J:= (A.path i).patch) hx (hS i hi).1 j).2.2
   obtain ⟨g⟩:= A.elevates S hh; exact ⟨⟨h,S,g,hs,fun i hi=>(hS i hi).1,fun i hi=> (hS i hi).2⟩⟩
variable {S b0:SparkMesh}
def From (U:Cabin A (i+1)):= (A.boat i).applaud.near.keep (A.boat i).applaud.rates U.spin
def To (U:Cabin A i):= (A.boat i).applaud.far.keep (A.boat i).applaud.rates U.spin
namespace Terrace
variable (B: SparkMesh) (T: Terrace P₀ A X B x n)
abbrev originF (i:ℕ):SunR (A.marine i):=From P₀ A (T.W.state (i+1))
abbrev ending (i:ℕ):SunR (A.marine i):=To P₀ A (T.W.state i)
abbrev stepper (i:ℕ): Flight j j:= A.sail (T.W.state (i+1))
set_option quotPrecheck false
local notation "y₀"=>precursor P₀ A x i
local notation "c₁" => T.W.state (i+1)
local notation "c₀" => T.W.state i
local notation "ζi"=>stepper P₀ A X B T i
local notation "pai"=> (X i).policy
local notation "hx'"=> A.length i
local notation "λi"=> A.scale x i
local notation "Ωᵢ"=> A.marine i
local notation "TZ"=> R.Z.top.clip
local notation "Nq"=> R.Z.bind
local notation "φi"=> P₀.h
lemma stays {H H':ℝ}{K:Bed}{Z:PathData su}{u v:ℝ}{p:Clip}(h:Enjoy K p u v H Z)(hv:H ≤ H'):Enjoy K p u v H' Z:= by
   rcases h with ⟨hh,hT⟩; exact ⟨{hh with two:= budget_loosen hh.two hv},hT⟩

lemma available (hi:i < n)(R₁ R₂:BudgetPoint)(hx:Now (A.length i) R₁ R.Z.top (run (A.length i) (precursor P₀ A x i)))(hy:Now (A.length i) R₂ R.Z.top (precursor P₀ A x i))(hp:costZone A x (i+1) β)(hs: |α| ≤ roofK (A.length i) P₀.θ P₀.κ (run (A.length i) (precursor P₀ A x i))) :
     ∃ (U: Tube su ((stepper P₀ A X B T i).visit R.Z.bind (A.next (B.n k) i))),
        U.up=(T.W.state (i+1)).path ∧ U.down=(T.W.state i).path ∧ U.low= R.Z.top.clip ∧ U.high=R.Z.top.clip ∧
     ∃ (Z:Badge (passportM j P₀.good) (X i).policy R₁ R₂ (X i).o χ U (originF P₀ A X B T i) α (run (A.length i) (precursor P₀ A x i)) (1/8) β (X i).μ (X i).C) (Y: Gem (A.ring (B.n k) i) N (LayerQ (A.ring (B.n k) i))), Stowable _ (X i).policy Z Y (ending P₀ A X B T i) F₀ (T.W.gauge i) (T.W.price i) P₀.V P₀.U P₀.h P₀.κ θ P₀.A3:=by
   let V:= T.W.steps i hi
   let Q:= c₁; let G:= c₀; let M:= T.mesh i; let Z:= A.path i; let S:= A.sail Q; let P:= A.length i; let Λ:= stance P₀ A i; let K:= (A.boat i).applaud
   have hT := V.birth; let D:= T.W.gauge i; let E:= T.W.price i; let Y:= run (A.length i) (precursor P₀ A x i)
   have hs': |D| ≤ |betaFare P R.D|:=by
      have he:= V.terrace.toll; have hf:= Gauge.slopeConstant_pos simple; have hg: 0≤ Real.log P.val:= Real.log_nonneg (by exact_mod_cast P.pos); apply (punctuate _ _ _ (show |D+su.slopeConstant*Real.log P.val| ≤ R.D from (le_add_of_nonneg_right zero_le_one).trans he)).trans; rw [abs_of_nonneg (mul_nonneg hf.le hg)]; apply le_trans _ (le_abs_self _); simp [betaFare,creditΓ,P]
   have hΩ: |D+(N:ℝ)*E|≤ Vows R.D N P Ωᵢ:=by
     have he:|E|≤(A.marine i).b:= (V.birth.bill)
     refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_of_nonneg (by positivity:(0:ℝ)≤N)]; exact le_trans (add_le_add hs' (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) (by positivity))) (by unfold Vows; linarith)
   obtain ⟨c,h⟩:= hp; rw [← second P₀,← season P₀ A x i] at c h; rw [← (X i).theta] at hs
   have hv₁: ∀ j:Stars,M.n j.val= stellar (head P (X i).k0 Y) j.val:=by rw [show Y=λi from season ..]; exact T.firsts i hi
   have hv₂:2*style P (X i).k0 Y <(M.n (k+5)).val:=by rw [show Y=λi from season ..]; exact T.real_cap i hi k
   obtain ⟨a,Y',hY⟩:= (T.ground i).productive.earnsP R₂ R₁ hy hx Q.wing M V.arm Q.bed G.bed Q.path G.path D V.terrace V.qual (Q.quarry _) (G.quarry _) (stays Q.priced (le_max_left ..)) (stays G.priced (le_max_right ..)) (k+5) R.lawful.flour _ _ E V.birth hv₁ hv₂ hs' hΩ α β c h hs
   let A0:=moodH R.Z.bind (A.sail Q) R.Z.top.clip V.arm Q.path G.path M (k+5)
   have hr:A.ring (B.n k) i = M.n (k+5):= (T.straight.keeps i hi k).symm
   have he:A.ring (B.n k) (i+1) = high (A.sail Q) M (k+5):=Subtype.ext (by
      change (A.ring (B.n k) (i+1)).val=(high (A.sail Q) M (k+5)).val; rw [A.next,hr]; rfl)
   let f₀:=originF P₀ A X B T i; let g₀:=ending P₀ A X B T i
   have hx (f c:Side)(h:f=high (A.sail Q) M (k+5))(hz:c=M.n (k+5))(hp:f.val=c.val*P.val):∃ (U:Tube su (S.visit R.Z.bind hp)), U.up=Q.path∧U.down=G.path∧U.low=TZ∧U.high=TZ∧∃ (Z:Badge (passportM j P₀.good) (X i).policy R₁ R₂ (X i).o χ U f₀ α Y (1/8) β (X i).μ (X i).C) (X':Gem c N (LayerQ c)), Stowable _ _ Z X' g₀ F₀ D E P₀.V P₀.U P₀.h P₀.κ θ P₀.A3:=by
        subst f c; exact ⟨A0,rfl,rfl,rfl,rfl,a,Y',hY⟩
   exact hx _ _ he hr _
end Terrace
end Client
end Stratum.Spire
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.Spire.Client.Terrace.available
