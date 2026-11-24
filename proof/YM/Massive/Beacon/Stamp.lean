import YM.QCD.Cabin.Bend
import YM.QCD.Fall.Bend
import YM.Massive.Beacon.Wake
import YM.Massive.Beacon.Cycle
import YM.QCD.Fall.Steppes
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
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ A3 tol β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
variable (A:Voice c N) (F₀: Flavor N) (B: SparkMesh) {M':ℕ→ SparkMesh}



-- n final; actual.Step.
variable {E:ℕ→SunR Ω}{X:ℕ→ℝ}{T:ℕ→Towers J.L}
variable (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E X T x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)

set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k

-- transport relation after.Less.C.Coordinate

include hΓ
lemma packetV (hu:i < n)(hP:Now J.L R T'.top (delay J n i x)) (hR: Now J.L P T'.top (delay J n (i+1) x))(hm:|b| ≤ roofK J.L τ.t κ (delay J n i x))(hβ:run J.L (delay J n i x)/2 ≤ β)(hv:β ≤2*run J.L (delay J n i x)) : ∃ (T:Tube su ((Pike J i).visit T'.bind (lift0 (t:=k) B hu))), T.up=g.path i ∧ T.down=g.path (i+1) ∧ T.low=T'.top.clip ∧ T.high=T'.top.clip ∧ ∃ (X':Badge (passportM J.J J.order_cut) τ R P o χ T (E i) b (run J.L (delay J n (i+1) x)) (1/8) β μ z) (T₀:Gem (towerQ J B n (i+1) k) N (LayerQ (towerQ J B n (i+1) k))), Stowable _ τ X' T₀ (E (i+1)) F₀ (g.costP i) (X i) s₀ A' H κ tol A3:=by
   have hD:= next_delay J x hu; rw [← hD] at hm hβ hv hP; obtain ⟨Z,Y,hZ⟩:= hΓ.posed i k hu P R hR hP b β hβ hv hm
   have hr:(towerQ J B n (i+1) k)=(M' i).n (k+5):=(hΓ.payment i k).symm
   let S:= Pike J i; have he: (towerQ J B n i k)=high S (M' i) (k+5):=Subtype.ext ((show (towerQ J B n i k).val=_ from (lift0 B hu).trans (by rw [hr]; exact (divides0 S (M' i) _).symm)))
   have hx (f c:Side)(hv:f=high S (M' i) (k+5))(hp:c=(M' i).n (k+5))(hx:f.val=c.val*J.L.val) : ∃ (T:Tube su ((Pike J i).visit T'.bind hx)), T.up=g.path i ∧ T.down=g.path (i+1) ∧ T.low=T'.top.clip ∧ T.high=T'.top.clip ∧ ∃ (X':Badge (passportM J.J J.order_cut) τ R P o χ T (E i) b (run J.L (delay J n (i+1) x)) (1/8) β μ z) (T₀:Gem c N (LayerQ c)), Stowable _ τ X' T₀ (E (i+1)) F₀ (g.costP i) (X i) s₀ A' H κ tol A3:=by
       subst f c; exact ⟨PulsePass.moodle g T i (k+5),rfl,rfl,rfl,rfl,Z,Y,hZ⟩
   exact hx _ _ he hr _
-- general lemma pack at Moor actual height input. Already casts beta and m through synth.Attic.
namespace Reference
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- β bary.
lemma packageT (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*X i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)(hi:i<n): ∃ (T:Tube su ((Pike J i).visit T'.bind (lift0 (t:=k) B hi))), T.up=g.path i ∧ T.down=g.path (i+1) ∧ T.low=T'.top.clip ∧ T.high=T'.top.clip ∧ ∃ (X':Badge (passportM J.J J.order_cut) τ (Pt i) (Pt (i+1)) o χ T (E i) (U1 i) (run J.L (delay J n (i+1) x)) (1/8) (V1 i) μ z) (T₀:Gem (towerQ J B n (i+1) k) N (LayerQ (towerQ J B n (i+1) k))), Stowable _ τ X' T₀ (E (i+1)) F₀ (g.costP i) (X i) s₀ A' H κ tol A3:=by
    obtain ⟨⟨hh,hv⟩,hη,hA,hP⟩:= hZ.costs _ hi.le; exact packetV F₀ B g hΓ hi (hZ.clock i) (hZ.clock (i+1)) hA hh hv
-- Meas. holds with exact w prescalep. or Φ sthate. Reuse.
local notation "X!"=> g.costP i+ N* X i
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*X i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol) (hi:i<n)
include hZ hi
omit hΓ
lemma investor : |V1 i+(g.costP i+ N*X i)|+1 ≤ billT J n i x (g.costP i+ N*X i):=by
   let α:=g.costP i+N*X i; let β:=hatG J n i x; have hh:= (hZ.costs i hi.le).1
   obtain ⟨hk,h⟩:=hh; change _ ≤ 2*|β|+|α|+1
   refine add_le_add (le_trans (abs_add_le ..) (add_le_add ?_ le_rfl)) le_rfl
   apply abs_le.mpr; constructor
   · have h1:= neg_le_abs β; have hh:= abs_nonneg β; change β/2 ≤_ at hk; linarith
   exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
lemma warmthAt {T:Tube su ((Pike J i).visit T'.bind (lift0 (t:=k) B hi))}(hf:T.down=g.path (i+1)):
   Measured T.down T'.top.clip Δ (Pt (i+1)) F₀ (towerQ J B n (i+1) k) (vest (towerQ J B n (i+1) k) N (W1 i) (fort (Pike J i) T'.bind (lift0 B hi) N (V1 i) (Q1 i))) (FieldB Ω (E (i+1)) (towerQ J B n (i+1) k) (haloK J.L (delay J n (i+1) x)) (passportM J.J J.order_cut) (Pike J i).land) (E (i+1)).Z.page J.L (delay J n (i+1) x) τ.t s₀ (billT J n i x (g.costP i+N*X i)) (rangeG J n (i+1) κ τ.t x) tol (V1 (i+1)) (U1 (i+1)):=by
   rw [hf]; have h:= (hZ.warmth i hi).2; rw [(hZ.warmth i hi).1] at h; exact h
include hΓ
lemma w_inv : |W1 i-1|≤tol+tol+tol^2:=by
    obtain ⟨T,hA,hQ,hP,hB,Y,Wp,H'⟩:= packageT F₀ B g hΓ hZ hi
    let w:= W1 i; have hξ:= next_delay J x hi; let l:= delay J n (i+1) x; obtain ⟨A,q,hq,hU,hY⟩:= (hZ.costs i hi.le).2.2.2
    rw [← hξ] at hU
    obtain ⟨p,Γ,h1,h2,h3,h4,h5,hΓ1,⟨F⟩⟩:= H'.ride A.ι A.β (duo A.P A.K) hU
    let Z:=Flight.visit (Pike J i) T'.bind (lift0 (t:=k) B hi); obtain ⟨Z₁⟩:= Tree.select Z.ratio Z.patch.odd_side
    have hY': Q1 i = q • red A.P A.K (E i) (passportM J.J J.order_cut) (Pike J i).wing (Pt i) T.up T'.top.clip (haloK J.L (run J.L l)) (V1 i) (U1 i) 0:=by rw [hA]; unfold l; rw [hξ]; exact hY
    obtain ⟨A₁,v,hW,h₁,h₂,h₃,h₄,hp',hz,hI⟩:= produce T (passportM J.J J.order_cut) A F₀ Y Wp F Z₁ (warmthAt F₀ B g hZ hi hQ) hY' (investor F₀ B g hZ hi) (hZ.vocals i hi).1 hq hB
    rw [hp']; let t:= powerU F.toReliefR.R4 Wp F₀; have hv :0≤tol:=(abs_nonneg _).trans h₄; change 0<t at h₁; change |t-1|≤tol at h₃
    have hh: (v-1)* (t-1)+((v-1)+(t-1))=v*t-1:=by ring
    rw [← hh]; refine (abs_add_le ..).trans ?_; rw [abs_mul, add_comm _ (tol^2)]; exact add_le_add ((mul_le_mul h₄ h₃ (abs_nonneg _) hv).trans_eq (pow_two _).symm) ((abs_add_le ..).trans (add_le_add h₄ h₃))
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.packageT
