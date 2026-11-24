import YM.VStages.TravelY
import YM.VStages.Foster
import YM.VStages.PonderY
import YM.VStages.VistaW
import YM.Massive.Aperture.Calendar
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
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)

open Rails.Kin
local notation "ϕi"=>stepper P₀ A X B T i
/-!
# Precinct for the absolute marker in the measured varying-stride schedule

Here the family at height i travels with the weights at precisely that same step,
at the unperturbed solution of the shooting problem. Trimming notation is just for
the estimates, not for changing any law between heights. No claim of physical
measurements yet.
-/
abbrev Precinct (k n:ℕ):=∀ (i:ℕ),LanternT (A.ring (B.n k) n) N (A.ring (B.n k) i)
variable (Y: Precinct P₀ A B k n)

abbrev crossway (k:ℕ)(s: LanternT (A.ring (B.n k) n) N (A.ring (B.n k) (i+1))) := (Kin.travelQ N (W i) (ϕi) Kz (A.next (B.n k) i) (V (i+1)) (staysL P₀ A X B T i)).comp s
structure Keeps :Prop where
   into : ∀ (u:EvenA (A.ring (B.n k) n) N) , ⇑(Y n u)=(fun i=> F n i*u)
   walks : ∀ i≤ n, Tied (Y i) ∧ (⇑(Y i 1)=F i) ∧ mud (g0 (Y i))≠0
   progress : ∀ i:ℕ, i<n → Y i=crossway (i:=i) P₀ A X B T V W k (Y (i+1))
include hp hX hc
omit hX hc in
lemma shining (hi:i≤n) : mud (F i 1) ≠0:=by
   obtain ⟨M,z,hz,hM,hh⟩:= (hp.window i hi).2.2.2.2
   exact (readingIdentity (J (A.level i)) F₀ _ M _ _ _ _ _ _ _ hz _ hh).2
lemma awakens : ∃ Y:Precinct P₀ A B k n, Keeps P₀ A X B T V W F Y :=by
   obtain ⟨Y,hY,hE⟩:= presence (F n) (soul P₀ A X B T Z V U W F hp hX hc)
   let G:Precinct P₀ A B k n:= fun i=> if h:i≤ n then Nat.decreasingInduction (motive:=fun j (_:j≤n)=> LanternT (A.ring (B.n k) n) N (A.ring (B.n k) j)) (fun i _ S=> crossway (i:=i) P₀ A X B T V W k S) Y h else 0
   have hn:G n=Y:=by unfold G; rw [dif_pos le_rfl,Nat.decreasingInduction_self]
   have hg:∀ (i:ℕ), i<n→ G i=crossway (i:=i) P₀ A X B T V W k (G (i+1)):=by
       intro i hi; unfold G; rw [dif_pos hi.le,dif_pos (show i+1≤n from hi),Nat.decreasingInduction_succ_left _ _ (show i+1≤n from hi)]
   refine ⟨G,by rw [hn]; exact hY,?_,hg⟩ -- dep Keeps constructor
   intro i hi
   suffices hx:Tied (G i)∧(⇑(G i 1))=F i by
        refine ⟨hx.1,hx.2, ?_⟩; rw [g0,hx.2]; exact shining P₀ A X B T Z V U W F hp hi -- rewrite g0 elaboration
   induction hi using Nat.decreasingInduction with
   | self=> rw [hn,hY]; exact ⟨hE,funext (fun i=>mul_one (F n i))⟩
   | of_succ i hi ih=> rw [hg i hi]; refine ⟨matNext (S:=stepper P₀ A X B T i) (h:=A.next (B.n k) i) (staysL P₀ A X B T i) _ ih.1,?_⟩; change downF P₀ A X B T i k (W i) (V (i+1)) (⇑(G (i+1) 1))=_; rw [ih.2]; exact (hp.relay i hi).lift.symm
omit hp hX hc
abbrev family (u:Flavor N→ℝ)(α:ℝ)(i:ℕ):= Kin.experimental (Y i) u α
local notation "yF"=>family P₀ A B Y
variable (hh: Keeps P₀ A X B T V W F Y)
include hh
lemma bare_fam (u:Flavor N→ℝ)(s:ℝ) : family P₀ A B Y u s n=Aperture.spun (F n) s u:=by funext z; exact hh.into _
lemma neutral (hi:i ≤n)(u:Flavor N→ℝ)(s:ℝ) : family P₀ A B Y u s i 0=F i:= (Kin.experimentalV (Y i) u _).trans (hh.walks i hi).2.1
lemma hops (u:Flavor N→ℝ)(s:ℝ)(hi:i<n) : family P₀ A B Y u s i= Bank.LeapY (stepper P₀ A X B T i) Kz (A.next (B.n k) i) (family P₀ A B Y u s (i+1)) (V (i+1)) (W i):=by unfold family; rw [hh.progress i hi]; rfl
lemma trailPath (u:Flavor N→ℝ)(s:ℝ)(hi:i<n) :∀ z:ℂ, Cove.light _ ∘ (yF u s i z)= transfer (A.flight i) K (A.next (B.n k) i) (V (i+1)) (W i) (Cove.light _ ∘ (yF u s (i+1) z)):=by
   intro z; unfold family; rw [hh.progress i hi]; exact Kin.actualQ N (W i) (stepper P₀ A X B T i) Kz _ _ (staysL P₀ A X B T i) (Y (i+1) _)
include hp hX hc
lemma starts (u:Flavor N→ℝ)(s y:ℝ) : Cove.light _ ∘ (yF u s n (y:ℂ))=⇑((⟨V n,0,Aperture.splitR u (U n) (s*y)⟩: Regulator (A.ring (B.n k) n) N).density):=by
   funext i; rw [Aperture.prized,Function.comp_apply,bare_fam P₀ A X B T _ _ _ Y hh,Complex.ofReal_mul]; exact Aperture.visible _ u i (F n) (V n) (U n) (soul P₀ A X B T Z V U W F hp hX hc i) (((s:ℂ)*y):ℂ)
noncomputable def covering (u:Flavor N→ℝ)(v s:ℝ): Massive.Run (Suburb.ladder P₀ A) n (B.n k) N:= Massive.Scheme.run _ _ V W (Aperture.splitR u (U n) (v*s)) n
lemma exact_cov (i:ℕ)(u:Flavor N→ℝ)(v s:ℝ)(he:i≤n): (covering (n:=n) (k:=k) P₀ A B V U W u v s).density i = transit (Suburb.rungs P₀ A _ _).symm (Cove.light _ ∘ family P₀ A B Y u v i (s:ℂ)):=by
   let S:= Suburb.ladder P₀ A; let X':=S.run (B.n k) V W (Aperture.splitR u (U n) (v*s)) n; let G:= S.wilson (B.n k) V (Aperture.splitR u (U n) (v*s)) n
   induction he using Nat.decreasingInduction with
   | self=>
       have he : X'.density n= ⇑G.density:=by change ⇑(S.toStop (B.n k) V W n n G.density)=_; rw [Massive.Scheme.entrance]; rfl
       change X'.density _=_; rw [he,starts P₀ A X B T Z V U W F hp hX hc Y hh]; unfold G
       suffices M:∀ f:Side,∀ (h:A.ring (B.n k) n=f), ((⟨V n,0,Aperture.splitR u (U n) (v*s)⟩: Regulator f N).density).toFun= transit h ⇑((⟨V n,0,Aperture.splitR u (U n) (v*s)⟩:Regulator _ N).density) by exact M _ _
       intro f h; subst f; rfl
   | of_succ i hi ih=>
       change X'.density _=_; have hv : X'.density i= transfer (A.flight i) K _ (V (i+1)) (W i) (X'.density (i+1)):= Massive.Run.Carried.eqn (S.carried (B.n k) _ _ G.density (Aperture.splitR u (U n) (v*s))) (m:=i) (by omega) hi
       change X'.density _=_ at ih; rw [hv,ih]; suffices H:∀ f c:Side,∀ (h:f.val=c.val*(A.spacing i).val)(hF:A.ring (B.n k) (i+1)=f)(hC:A.ring (B.n k) i=c), transfer (A.flight i) K h (V (i+1)) (W i) (transit hF (Cove.light _ ∘ family P₀ A B Y u v (i+1) (s:ℂ)))= transit hC (Cove.light _ ∘ family P₀ A B Y u v i (s:ℂ)) by exact H _ _ _ _ _
       intro f c h hF hC; subst f c; exact (trailPath P₀ A X B T _ _ F Y hh u v hi (s:ℂ)).symm
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.awakens
