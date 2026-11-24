import YM.VStages.CalmQ
import YM.VStages.SquareM
import YM.QCD.Glass.Encore
import YM.Massive.Tuner.Square
import YM.VStages.TotemW
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
namespace Affair
open Function High PrismT MeasureTheory Sq Grass Stew.Project
set_option quotPrecheck false
variable {Pt:ℕ→BudgetPoint} {Δ:PlaqAxes} (B: SparkMesh) (T: Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
local notation "q₀"=> clockQ P₀ A x i
local notation "Y₁"=> T.W.state (i+1)
local notation "Y₀"=> T.W.state i
local notation "ϕi"=> stepper P₀ A X B T i
local notation "Lₜ"=> A.spacing i
local notation "CK"=> fun i:ℕ=> A.ring (B.n k) i
local notation "Kq"=> K
local notation "Cₚ"=> (P.stage (A.level i)).clip

variable {𝔇:Set Twin}
abbrev caller (i:ℕ):ℝ:= T.W.delta A N i
abbrev centre (i:ℕ):ℝ:= central x (T.W.delta A N) i
abbrev Hails (i:ℕ)(v:ℝ):= Track.Hub A T.W x N i v
lemma forward (i:ℕ): centre P₀ A X B T (i+1)+caller P₀ A X B T i = centre P₀ A X B T i:=by unfold centre caller central; rw [succeeding]; abel
lemma widen (i:ℕ):height_R (i+1)=height_R i+3:=by unfold height_R; push_cast; ring

structure LinkT (i:ℕ)(V V₁ M w:ℝ)(F:Pixel (A.ring (B.n k) i) N)(V':Pixel (A.ring (B.n k) (i+1)) N):Prop where
    real : 0 < w
    small : w≤ 4
    band : |w-1| ≤2*tol+tol^2
    step : |V-V₁-caller P₀ A X B T i|≤2
    lift : F=downF P₀ A X B T i k w V₁ V'
    body : ∀ U, advanceF (stepper P₀ A X B T i) K (A.next (B.n k) i) V' V₁ U=gBody (A.ring (B.n k) i) w (F U)
    quarter : 1/4 ≤ unitF true (A.ring (B.n k) i) (field P₀ A X B T i k 1)
    theoremG : event P₀ A X B T Pt Δ i k F (Z.φ i) (Z.μ i) (Z.Ξ i) V M
structure WithMap (i:ℕ)(D:Set Twin)(V M:ℕ→Twin→ℝ)(F:∀ i,Twin→Pixel (A.ring (B.n k) i) N) (U:Twin→ Twin) :Prop where
    live : MapL (centre P₀ A X B T i) (height_R i) (MassBox P₀ A x i) D (V i) (M i) U
    reaches : Reach D (F i)
    opens : ContinuousOn (V i) D
    original (v:Twin)(h:v∈D): F n v=CodeG _ N (V n v) (M n v)
    budgets (v:Twin)(hv:v∈D)(j:ℕ)(h:i≤j)(hx:j≤n): Hails P₀ A X B T j (V j v) ∧ |M j v| ≤ MassBox P₀ A x j ∧ SupportH P₀ A X B T Pt j k (F j v) (V j v) (M j v)
    freight (v:Twin)(hv:v∈D)(j:ℕ)(h:i≤j)(hx:j<n): ∃ W:ℝ, LinkT P₀ A X B T Z j (V j v) (V (j+1) v) (M j v) W (F j v) (F (j+1) v)
variable (hp: entire P₀ A x Pt)(hc:Calm P₀ A X x)
variable (hy:∀ i≤n,∀ β:ℝ,Hails P₀ A X B T i β →ArcTime A x i β)
include hp hc hy
set_option maxHeartbeats 730000 in
lemma rests (hi:i<n){D:Set Twin}(V M:ℕ→Twin→ℝ)(F:∀ i,Twin→Pixel (A.ring (B.n k) i) N){U:Twin→Twin}
    (h:WithMap P₀ A X B T Z (i+1) D V M F U):∃ D' V' M' F' U', WithMap P₀ A X B T Z i D' V' M' F' U':=by
   have hm:=hc.kind
   have hv :0 < MassBox P₀ A x i:=(hm i).warms.pos
   let β(v):= V (i+1) v
   have hh(y:Twin)(hx:y∈ D):= h.budgets y hx (i+1) le_rfl hi
   choose! w p q H using fun i' (hx:i'∈D)=> descends P₀ A X B T Pt hc.growth (hp _) (hp _) (hy _ hi _ (hh i' hx).1) hi (hh i' hx).2.1 hv (F _ i') (hh i' hx).2.2 (Z.vetted _ hi)
   let Y v:=downF P₀ A X B T i k (w v) (β v) (F (i+1) v); let b':= caller P₀ A X B T i; let t v:=β v+b'+q v
   have h₀(y)(hx:y∈D): LinkT P₀ A X B T Z i (t y) (β y) (p y) (w y) (Y y) (F (i+1) y):=by
        obtain ⟨hu,h1,h2,h3,h4,h5,h6,h7,h8⟩:= H y hx; refine ⟨hu,h1,h2,?_,rfl,h6,h7,h8⟩; unfold t b' at *; rw [show β y+_+_-β y-_= q y by ring]; exact h3
   have hs:=(solarQ (K:=Kq) (N:=N) (S:=stepper P₀ A X B T i) (h:=A.next (B.n k) i) h.live.clans h.reaches (A.ticket i).owns h.opens)
   have hZ:= Z.vetted i hi
   obtain ⟨ht,hP,hY,hW⟩:= garnet (T.W.state i).sun.Z.page (T.W.state i).path (P.stage (A.level i)).clip Δ F₀ w _ hs (Xs:=Y) (E:=t) (fun i=>rfl) (fun i hi=> ⟨(h₀ i hi).theoremG,(H i hi).1,(h₀ i hi).quarter⟩) hZ.gift
   let a:= centre P₀ A X B T i; let z:= height_R i
   have ha: centre P₀ A X B T (i+1)+b'=a:= forward ..; let r:= MassBox P₀ A x i
   have ht' (y:Twin)(hy:y∈D):=abs_le.mp (H y hy).2.2.2.1
   obtain ⟨Z',U,h',hU⟩:= hullT U h.live (zen i) hv ht hP (w:=a) (fun y hy=> by
      unfold t β; constructor <;> intro he <;> rw [he] <;> linarith only [ha,widen i,(ht' y hy).1,(ht' y hy).2]) (fun y hy=>(H y hy).2.2.2.2.2.1)
   subst Z'
   let V':=update V i t; let M':= update M i p; let F':=update F i Y
   refine ⟨_,V',M',F',U, by unfold V' M'; simpa only [update_self] using hU, ?_, ?_,?_,?_,?_⟩
   · unfold F'; rw [update_self]; exact hY.mono fun v h=> ⟨h.1.1,h.2⟩
   · unfold V'; rw [update_self]; exact ht.mono fun v h=>h.1
   · intro v h'; unfold V' M' F'; rw [update_of_ne hi.ne',update_of_ne hi.ne',update_of_ne hi.ne']; exact h.original v h'.1
   · intro b h' l h1 h2; unfold V' M' F'; by_cases hl:l=i
     · subst l; rw [update_self,update_self,update_self]; exact ⟨h'.2.1,h'.2.2,(H b h'.1).2.2.2.2.1⟩
     rw [update_of_ne hl,update_of_ne hl,update_of_ne hl]; exact h.budgets _ h'.1 _ (by omega) h2
   · intro b h' l h1 h2; unfold V' M' F'; by_cases hl:l=i
     · subst l; simp only [update_self,update_of_ne (show i+1 ≠ i by omega)]; exact ⟨w b,h₀ b h'.1⟩
     simp only [update_of_ne hl,update_of_ne (show l+1≠i from (by omega))]; exact h.freight b h'.1 l (by omega) h2
set_option maxHeartbeats 260000 in
lemma anchors :∃ V M F, WithMap P₀ A X B T Z n Set.univ V M F id:=by
    let x':= centre P₀ A X B T n; let u:=height_R n; let g:= MassBox P₀ A x n; let t (i:Twin):=x'+u*Sq.tail i; let s (i:Twin):=g* mast i; let Q (j:ℕ)(i):= CodeG (A.ring (B.n k) j) N (t i) (s i)
    have hC: Continuous t:=by unfold t; fun_prop
    refine ⟨fun _=>t,fun _=>s,Q,⟨isClosed_univ,continuous_id,(fun i hi=>(hi (Set.mem_univ _)).elim),fun i _=>⟨rfl,rfl⟩,fun i b _=> rfl⟩,primeT hC (show Continuous s from (by unfold s; fun_prop)),hC.continuousOn,fun _ _=>rfl,fun v _ i hi hp'=>?_,fun _ _ i hi ht=>by omega⟩
    have hh:= le_antisymm hp' hi; subst i
    have he :0<g:=(hc.kind n).warms.pos
    have hx:Hails P₀ A X B T n (t v):=by
         unfold t; apply abs_le.mpr; change -(u)≤ x'+u*_ - x' ∧ x'+u*_ -x' ≤u; have hp:= Sq.shore v; have hh:= zen n; have ht:= abs_le.mp hp.1; constructor <;> nlinarith only [hh, ht.1, ht.2,mul_le_mul_of_nonneg_left ht.1 hh.le,mul_le_mul_of_nonneg_left ht.2 hh.le]
    exact ⟨hx,(by rw [show |s v|= g*|mast v| by rw [show |s v|= _ from abs_mul _ _, abs_of_nonneg he.le]]; exact mul_le_of_le_one_right he.le (Sq.shore _).2),(prim P₀ A X hc B T hp (t v) (s v) (hy n le_rfl _ hx) k).1⟩ -- Args
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
