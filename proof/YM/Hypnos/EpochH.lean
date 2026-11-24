import YM.Hypnos.Cwm
import YM.VStages.Votaries
import YM.VStages.TreesW
import YM.VStages.Through
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:Rock j}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (Y:Metros P J θ F₀ χ)(T:TrackQ (gate:=gate) Y)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (W0:∀ i:ℕ,SlotQ Y tol T i)

variable {S b0:SparkMesh}
namespace Affair
open LicenseM
variable (B:SparkMesh) (X:Affair Y T W0 B x n) {β:ℝ}
set_option quotPrecheck false
local notation "y₀"=>clockQ Y T x i
local notation "c₁" => X.W.state (i+1)
local notation "c₀" => X.W.state i
local notation "ζi"=>stepper Y T W0 B X i
local notation "pai"=> (W0 i).policy
local notation "hx'"=> T.spacing i
local notation "λi"=> T.scale x i
local notation "Ωᵢ"=> (T.beam i).fare
local notation "TZ"=> (P.stage (T.level i)).clip
local notation "Gq"=> (P.stage (T.level (i+1))).clip
local notation "Nq"=> K
local notation "Ki"=> (Y (T.node i))
local notation "Pq"=> J (T.level i)
local notation "Pv"=> J (T.level (i+1))
lemma knellsH (hΓ:HourV (Y (T.node i)) (W0 i) (clockQ Y T x i)) (hi:i < n)(R₁ R₂:BudgetPoint)(hx:Now (T.spacing i) R₁ (P.stage (T.level (i+1))) (run (T.spacing i) (clockQ Y T x i)))(hy:Now (T.spacing i) R₂ (P.stage (T.level i)) (clockQ Y T x i))(hp:ArcTime T x (i+1) β)(hs: |α| ≤ roofK (T.spacing i) θ (Ki).κ (run (T.spacing i) (clockQ Y T x i))) :
     ∃ (U: Tube su ((ζi).visit Nq (T.next (B.n k) i))),
        U.up=(X.W.state (i+1)).path ∧ U.down=(X.W.state i).path ∧ U.low= TZ ∧ U.high=Gq ∧
     ∃ (Z:Manifest Pv Pq pai R₁ R₂ (W0 i).o χ U (starting Y T W0 B X i) α (run (T.spacing i) (clockQ Y T x i)) (1/8) β (W0 i).μ (W0 i).C) (L₀: Gem (T.ring (B.n k) i) N (LayerQ (T.ring (B.n k) i))), SliceRows.Stamp U∧2*(radiusB (run (T.spacing i) (clockQ Y T x i))+1)<(T.ring (B.n k) (i+1)).val ∧ |α| ≤ wink (T.spacing i) (run (T.spacing i) (clockQ Y T x i)) ∧ Stamen (city P (T.node i)) (ζi) K (T.next (B.n k) i) U (run (T.spacing i) (clockQ Y T x i)) β ∧ Knells Pv Pq pai Z L₀ (closing Y T W0 B X i) F₀ (X.W.gauge i) (X.W.spin i) (Ki).V (Ki).U (Ki).h (Ki).κ tol (Ki).A3:=by
   let V:= X.W.steps i hi
   let Q:= c₁; let G:= c₀; let M:= X.mesh i; let Z:= T.flight i; let S:= T.sail Q; let L:= T.spacing i; let Λ:= stanceQ Y T i; let K':= (T.ticket i).applause
   have hT := V.birth; let D:= X.W.gauge i; let E:= X.W.spin i; let Y':= run (T.spacing i) (clockQ Y T x i)
   let R:= P.slope (T.node i)
   have hs': |D| ≤ |betaFare L R|:=by
      have he:= V.terrace.toll; have hf:= Gauge.slopeConstant_pos simple; have hg: 0≤ Real.log L.val:= Real.log_nonneg (by exact_mod_cast L.pos); apply (punctuate _ _ _ (show |D+su.slopeConstant*Real.log L.val| ≤ R from (le_add_of_nonneg_right zero_le_one).trans he)).trans; rw [abs_of_nonneg (mul_nonneg hf.le hg)]; apply le_trans _ (le_abs_self _); simp [betaFare,creditΓ,L]
   have hΩ: |D+(N:ℝ)*E|≤ Vows R N L Ωᵢ:=by
     have he:|E|≤((T.beam i).fare).b:= (V.birth.bill)
     refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_of_nonneg (by positivity:(0:ℝ)≤N)]; exact le_trans (add_le_add hs' (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) (by positivity))) (by unfold Spire.Client.Vows; linarith)
   obtain ⟨c,h⟩:= hp; rw [engaged Y T,← augmented Y T i x] at c h
   have hv₁: ∀ j:Stars,M.n j.val= stellar (head L (W0 i).k0 Y') j.val:=by rw [show Y'=λi from augmented ..]; exact X.firsts i hi
   have hv₂:2*style L (W0 i).k0 Y' <(M.n (k+5)).val:=by rw [show Y'=λi from augmented ..]; exact X.real_cap i hi k
   obtain ⟨a,A0,hY⟩:= hΓ.earnsP R₂ R₁ hy hx Q.wing M V.prices Q.bed G.bed Q.path G.path D V.terrace V.delta V.throughoutIn V.throughoutOut (rank_ge _) (Spire.Client.Terrace.stays Q.priced (le_max_left ..)) (Spire.Client.Terrace.stays G.priced (le_max_right ..)) (k+5) (P.retail _).growth _ _ E V.birth hv₁ hv₂ hs' hΩ α β c h (show |α|≤ roofK L (W0 i).policy.t (Y (T.node i)).κ Y' from by rw [(W0 i).theta]; exact hs)
   let A:=moodQ K (T.sail Q) Gq TZ V.prices Q.path G.path M (k+5)
   have hr:T.ring (B.n k) i = M.n (k+5):= (X.aligned.keeps i hi k).symm
   have he:T.ring (B.n k) (i+1) = high (T.sail Q) M (k+5):=Subtype.ext (by
      change (T.ring (B.n k) (i+1)).val=(high (T.sail Q) M (k+5)).val; rw [Track.next,hr]; rfl)
   let f₀:=starting Y T W0 B X i; let g₀:=closing Y T W0 B X i
   have hx (f c:Side)(h:f=high (T.sail Q) M (k+5))(hz:c=M.n (k+5))(hp:f.val=c.val*L.val):∃ (U:Tube su (S.visit K hp)), U.up=Q.path∧U.down=G.path∧U.low=TZ∧U.high=Gq∧∃ (Z:Manifest Pv Pq pai R₁ R₂ (W0 i).o χ U f₀ α Y' (1/8) β (W0 i).μ (W0 i).C) (X':Gem c N (LayerQ c)), SliceRows.Stamp U ∧ 2*(radiusB (run (T.spacing i) (clockQ Y T x i))+1)< f.val ∧ |α| ≤ wink (T.spacing i) (run (T.spacing i) (clockQ Y T x i)) ∧ Stamen (city P (T.node i)) S K hp U Y' β ∧ Knells Pv Pq pai Z X' g₀ F₀ D E (Ki).V (Ki).U (Ki).h (Ki).κ tol (Ki).A3:=by
        subst f c; exact ⟨A,rfl,rfl,rfl,rfl,a,A0,hY⟩
   exact hx _ _ he hr _
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.knellsH
