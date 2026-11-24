import YM.Intag.Folio
import YM.VStages.RideW
import YM.Magi.Sig
import YM.Pods.Temple
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open MassiveQCD.Cupola MassiveQCD.Cape MassiveQCD.Cape.LampV MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden
open scoped BigOperators Classical
namespace Folio
-- casts RHS.Public itinerary.
variable {p q l p' q':Side}(e:p=p')(h:q=q')(U:Ratio p q)(V:Ratio p' q')(A:Ratio p p)
noncomputable def exit_h (e:p=p') : Site p→Site p':= by rw [←e]; exact id
include e h in
lemma counts : U.count=V.count:=by subst p' q'; rw [ratioUnique U V]
lemma self (V:Ratio p p)(x:Site p): V.parent x=x:=by
     let v:=V.count; have hh : p.val*1=p.val*V.count.val:=by rw [mul_one]; exact V.exact_size
     have hp:V.count.val=1:= (Nat.mul_left_cancel (p.pos) hh).symm
     apply YM.Next.Rank.Station.owner; unfold Ratio.embed; rw [hp,one_smul,wrap_lift]; simp
lemma wraps (x:Cover): exit_h e (wrap p x) = wrap p' x:=by subst p'; rfl
lemma parental (x:Site q) : exit_h e (U.parent x)= V.parent (exit_h h x):=by subst p' q'; rw [ratioUnique U V]; rfl
variable {I:Type}[Fintype I](X:I→Site p)
lemma passage {k:ℕ} (H:Fires X k): Fires (exit_h e ∘ X) k:=by subst p'; exact H
lemma verse (Z:Finset (Finset I)) (u:I→Site l){k B:ℕ}(hv:ClusteredE u Z k B X): ClusteredE u Z k B (exit_h e∘X):=by subst p'; exact hv
open MassiveQCD.Play
lemma vital (k:ℕ)(i:Finset I)(ht:Ac.Spark (Camp.Ray X k) i):Ac.Spark (Camp.Ray (exit_h e ∘ X) k) i:=by subst p'; exact ht
end Folio
end YM.Intag
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
variable {c f C F L:Side} {J:Patch} {j k n m i l n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {K:KernelChoices}
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "SCp"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) 6)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow 6) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

namespace Lobby
open MassiveQCD
namespace GlacierX
open Massive.Patria.Hub Massive.Patria.Depth
open Craft YM.Intag YM.Intag.Column YM.Intag.Folio -- Ker?
local notation "R2"=> B.n k
local notation "S2"=> ladder P₀ A
-- x mark positions any lift ALL.Al.Need genuine fires.Seams witness; account over interval exactly. no Step.P omission.
variable {I₀:Type}[Fintype I₀]
noncomputable def putE {i:ℕ} (x:I₀→ Cover)(j:ℕ) : I₀→Site (A.ring (B.n k) j) :=if h:j ≤ i then exit_h (rungs P₀ A _ _) ∘ ((viewW S2 R2 h).parent ∘ (wrap ((ladder P₀ A).side (B.n k) i) ∘ x)) else fun _=>0
variable (xh:I₀→ Cover)
local notation "PL" j:arg=> putE (i:=i) P₀ A B xh j
local notation "IV"=> IntagGalo
lemma arrived: putE (i:=i) (k:=k) P₀ A B xh i= wrap (A.ring (B.n k) i) ∘ xh:=by
     funext p; unfold putE; rw [dif_pos (show i ≤ i from le_rfl)]; simp only [Function.comp_apply,Folio.self,YM.Intag.Folio.wraps]
-- proofs. Mark parent.E.Step using slice ratio unique. Applies real UNITY.
lemma relies (hj:j < i): putE P₀ A B xh (k:=k) (i:=i) j=((stepper P₀ A X B T j).visit K (A.next (B.n k) j)).ratio.parent ∘ putE (i:=i) P₀ A B xh (j+1):=by
     let U:= Flume.sliceL ((ladder P₀ A).step j) ((ladder P₀ A).sides_next R2 j); funext t; unfold putE; rw [dif_pos hj.le, dif_pos (show j+1≤ i from hj)]
     simp only [Function.comp_apply]; rw [Next.Rank.Station.parent_nested U (viewW S2 R2 hj) _ ((ladder P₀ A).step j |>.odd) (viewOdd ..)]; exact parental ..
-- costs Core geom. with invariant layout T on f i.
open Massive Massive.Lyre Cupola Cape Cape.LampV
variable {p:ℕ}(hv:p ≤ i)(hr:Even ((ladder P₀ A).side (B.n k) p).val)
variable (z1 : Site ((ladder P₀ A).side (B.n k) i)) (f:I₀→ Site ((ladder P₀ A).side (B.n k) p)) (M a1 a2 b₁:ℕ)
local notation "c'" i:arg=> (S2).side R2 i
variable (hP:∀ t, (wrap ((ladder P₀ A).side (B.n k) i) (xh t))∈ (Massive.Romance.mural (viewW (ladder P₀ A) (B.n k) hv) hr z1).margin (f t) M)(hf:Fires f a1)
include hP hf
lemma credited (hk:p≤ j)(hl:j ≤ i)(hm:a1*625 ≤ b₁): Fires (putE (i:=i) P₀ A B (k:=k) xh j) b₁:=by
      unfold putE; rw [dif_pos hl]; exact passage _ _ (Intag.Film.ports (viewW S2 R2 hk) (viewW S2 R2 hl) _ (viewOdd ..) _ f hr (viewOdd S2 R2 hv) _ hP hf hm)
variable (hj:p ≤ j)(he':j ≤ i)
local notation "Gj"=> PL j
include he'
lemma visions {B₁:ℕ}(hm: (ratioTo (ladder P₀ A) i j)*(B₁*B₁+1) ≤2*M): ClusteredE f (ink f) a1 B₁ (putE (i:=i) P₀ A B (k:=k) xh j):=by
     unfold putE; rw [dif_pos he']; exact verse _ _ _ _ (Folio.films _ _ _ _ hf _ _ (viewW S2 R2 he') z1 _ (viewOdd ..) (viewOdd ..) hP hm) -- test
omit hP hf
open Play
lemma shades {B₁:ℕ} (hp:∀ t q,f t=f q→ separation (wrap ((ladder P₀ A).side (B.n k) i) (xh t)) (wrap _ (xh q)) ≤ ratioTo (ladder P₀ A) i j) (ht:0<B₁): ∀ i'∈ ink f, i'.Nonempty→ Ac.Spark (Play.Camp.Ray (putE (i:=i) P₀ A B (k:=k) xh j) (baseTZ B₁)) i':=by -- syntax
     unfold putE; rw [dif_pos he']; exact fun i1 h hi'=> vital _ _ _ i1 (Folio.lit _ _ (wrap (c' i)∘ xh) (viewW S2 R2 he') (viewOdd ..) hp ht _ h hi')
end GlacierX
end Lobby
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.GlacierX.relies
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.GlacierX.arrived
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.GlacierX.visions
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.GlacierX.credited
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.GlacierX.shades
