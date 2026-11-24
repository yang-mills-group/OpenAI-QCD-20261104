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
variable (E:RiseBook P₀)
variable (he:Views P₀ A X E x)
open Massive.Filament
include he
omit he
abbrev Banner (k:ℕ)(Pt:ℕ→BudgetPoint)(V:ℕ→ℝ)(i:ℕ): Grid (A.ring (B.n k) i)→ℝ:= scent (T.W.state i).sun.Z.page (Pt i) (T.W.state i).path (P.stage (A.level i)).clip (V i) 0 N
abbrev basisR (k:ℕ)(U:ℕ→ℝ)(i:ℕ): St (A.ring (B.n k) i):= field P₀ A X B T i k+U i • 1
abbrev Sails (Pt: ℕ→BudgetPoint)(k:ℕ)(X' : Arrow N)(i:ℕ)(F:ℂ→ Pixel (A.ring (B.n k) i) N)(s:ℝ):=
     Ladder F (Pt i) (A.spacing i) X' F₀ θ (clockQ P₀ A x i) s (dab P₀ A E i) (fees P₀ A E i) (Banner P₀ A X B T k Pt V i) (basisR P₀ A X B T k U i)
-- analogous consuming the From currency. not necessarily literally the same Sails when i<n.
abbrev FromS (Pt: ℕ→BudgetPoint)(k:ℕ)(X': Arrow N)(i:ℕ)(F:ℂ→Pixel (A.ring (B.n k) (i+1)) N)(s:ℝ):=
     Ladder F (Pt (i+1)) (A.spacing i) X' F₀ θ (run (A.spacing i) (clockQ P₀ A x i)) s (dab P₀ A E (i+1)) (fees P₀ A E (i+1)) (Banner P₀ A X B T k Pt V (i+1)) (basisR P₀ A X B T k U (i+1))
abbrev corridor (i:ℕ)(x:ℝ):= Conductor.Quant.crest (A.spacing i) (clockQ P₀ A x i) (fees P₀ A E i) (1/4)
lemma ville (i:ℕ): corridor P₀ A E (i+1) x =Quant.crest (A.spacing i) (run (A.spacing i) (clockQ P₀ A x i)) (fees P₀ A E (i+1)) (1/4):=by
    have h:=Suburb.terminal P₀ A (i+1) x; rw [notch,start_clock] at h; unfold corridor Quant.crest; rw [Spire.chip_at h]
variable (e:ℕ)
variable (M₀:Arrow N)
include he hp hX
lemma boots (Y:ℂ→Pixel (A.ring (B.n k) n) N)(s:ℝ)(hs:0<s)(hF:Y= Aperture.spun (F n) s M₀.tip)(h:s*Aperture.wealthy (A.spacing n) θ (clockQ P₀ A x n)≤ corridor P₀ A E n x) : Sails P₀ A X B T V U E Pt k M₀ n Y (s*Aperture.wealthy (A.spacing n) θ (clockQ P₀ A x n)):=by
    let y:= clockQ P₀ A x n; let L:= A.spacing n; let n':= A.ring (B.n k) n; let Ω:= Fog.Mist.rate (A.town n).1; let p:= Pt n; let β:= V n; let τ:= (X n).policy
    obtain ⟨hβ,hψ⟩ := (books P₀ A X E he n).start; obtain ⟨_,h1,hW⟩:= orbitR P₀ A X E he n
    have ht:=waking P₀ A (hX n); obtain ⟨ha,hb⟩:= (hp.window n le_rfl).2.1; rw [← augmented P₀ A n] at ha hb
    obtain ⟨hE,hG,h_u,hq⟩:= hβ.watch p n' ht _ ha hb
    let D₁:=T.W.state n; let G:= birthV n' p N (P.stage (A.level n)).clip β;
    -- F n root births match the actual ladder stamp
    let V':= Affair.Zest P₀ A X B T Pt n k G β (U n)
    have hz:F n=V':=by
       have hv:=T.W.price
       rw [hp.bare]; funext i; unfold CodeG; rw [Function.comp_apply]
       have he:Cove.light _ (V' i)=primalD n' N β (U n) i:=by
          unfold V' Affair.Zest quoteF Rails.red; rw [hv.root,vacT hv.blank]; refine voiceBorn _ _ _ _ _ _ _ ?_ F₀ h_u hG; rw [hv.top]; exact defrost _ hv.zen hv.zit i
       rw [show QCD.Acre.Rails.primalD _ _ (V n) (U n) i= _ from he.symm,callH] -- verify
    rw [hz] at hF -- score defeq
    let φ:=Rotary.chartR y; have hφ:0<φ:=by linarith only [(Rotary.spring L (tallR P₀ A n) y hW.root).1]
    have hT : Sails P₀ A X B T V U E Pt k M₀ n Y (s*Aperture.wealthy L θ y):=by
         have hu : s*Aperture.wealthy L τ.t y ≤ corridor P₀ A E n x :=by rw [show τ.t=θ from (X n).theta]; exact h
         have hψ' : s*Aperture.wealthy L τ.t y=(fan L τ.t y)^2*(s*φ):=by unfold φ Aperture.wealthy; ring
         rw [hψ'] at hu
         have hb: Ladder Y (Pt n) L M₀ F₀ τ.t y (s*Aperture.wealthy L τ.t y) (dab P₀ A E n) (fees P₀ A E n) (Banner P₀ A X B T k Pt V n) (basisR P₀ A X B T k U n):=by
             rw [hψ'];
             exact bootLeg L (b':=F₀) G Y M₀ hβ ht hE hW.root (hψ p ht) hq s (s* Rotary.chartR y) _ _ (mul_pos hs hφ) rfl (tallR P₀ A n) h1.stampD.le (mul_pos h1.outE hW.seed) hu hF
         rw [show τ.t=θ from (X n).theta] at hb; exact hb
    exact hT
-- earning gallop using these Measured at exactly current clockQ
omit he hp hX in
lemma basket (i k:ℕ) : FieldB ((A.beam i).fare) (starting P₀ A X B T i) (A.ring (B.n k) (i+1)) (haloK (A.spacing i) (run (A.spacing i) (clockQ P₀ A x i))) (J (A.level (i+1))) (stepper P₀ A X B T i).wing=Affair.field P₀ A X B T (i+1) k:=by unfold Affair.field; rw [start_clock,notch]; rfl
set_option maxHeartbeats 580000 in
lemma leg (Y' :ℂ→ Pixel (A.ring (B.n k) (i+1)) N)(Y:ℂ→ Pixel (A.ring (B.n k) i) N)(s:ℝ)
    (hi:i<n)(ht:2*tol+tol^2≤1/2)(hu:Y' 0=F (i+1))(hY:Y=Bank.LeapY (stepper P₀ A X B T i) Kz (A.next (B.n k) i) Y' (V (i+1)) (W i)) (hs:StampBook P₀ A X E B k n x)(hv:FromS P₀ A X B T V U E Pt k M₀ i Y' s)(hc:s ≤ corridor P₀ A E (i+1) x)
    : Quant.LadderStep (A.spacing i) Y (Pt i) M₀ F₀ (Banner P₀ A X B T k Pt V i) (basisR P₀ A X B T k U i) (clockQ P₀ A x i) θ (fees P₀ A E i) (dab P₀ A E i) s:=by
    obtain ⟨qα,h',h2⟩:= orbitR P₀ A X E he i
    let q:= clockQ P₀ A x i; let L:= A.spacing i; let H:=run L q
    have hx:=hp.window (i+1) hi; have hR:=birthBook P₀ A (hX (i+1)); have hQ:= waking P₀ A (hX i)
    have hm:=hx.2.2.2.1; rw [wages] at hm
    obtain ⟨RP,h₁,h₂,hL,hH,Yβ,Wβ,h⟩:= available (k:=k) P₀ A X B T hi (Pt (i+1)) (Pt i) hR hQ hx.2.1 hm
    let φ:= stepper P₀ A X B T i; let c:=A.ring (B.n k) i
    let F':= F i; let z:= FieldB ((A.beam i).fare) (closing P₀ A X B T i) c (haloK L q) (J (A.level i)) φ.land; let τ:= (X i).policy; let Em:= closing P₀ A X B T i; let Fstep:= Bank.LeapY φ Kz (A.next (B.n k) i) Y' (V (i+1)) (W i); let Pβ:= hp.relay i hi
    have hfield:z=field P₀ A X B T i k:= field_eq P₀ A X B T hi k
    have heq:Fstep 0= F i:=by change downF P₀ A X B T i k (W i) (V (i+1)) (Y' 0)=_; rw [hu]; exact Pβ.lift.symm
    have hMeas: Measured RP.down (P.stage (A.level i)).clip Δ (Pt i) F₀ c (Fstep 0) z Em.Z.page L q τ.t (P₀ (A.node i)).V (Affair.fare P₀ A X B T i) (roofK L τ.t (P₀ (A.node i)).κ q) tol (V i) (U i):=by
        rw [hfield,h₂,heq]; exact ⟨Z.φ i,Z.μ i,Z.Ξ i,Pβ.theoremG,Z.vetted i hi⟩
    obtain ⟨h_u,h_v⟩:= abs_le.mp (Pβ.band.trans ht)
    unfold FromS Banner basisR at hv
    -- don't rewrite through all ${Φ}
    let EmIn:= starting P₀ A X B T i
    have hr := regrade hR (A.level i)
    have hp: Ladder Y' (Pt (i+1)) L M₀ F₀ τ.t H s (dab P₀ A E (i+1)) (fees P₀ A E (i+1)) (scent EmIn.Z.page (Pt (i+1)) RP.up (P.stage (A.level (i+1))).clip (V (i+1)) 0 N) (FieldB (A.beam i).fare EmIn _ (haloK L H) (J (A.level (i+1))) φ.wing+U (i+1) • 1):=by
        rw [show τ.t=θ from (X i).theta]; rw [← h₁,← basket P₀ A X B T i k] at hv; exact hv
    rw [ville] at hc; rw [hY]; unfold basisR Banner; have hm:= Bank.ponderY RP (J (A.level (i+1))) (J (A.level i)) F₀ Yβ Wβ Y' hQ (investment P₀ A X B T hx.2.1) hMeas h h' M₀ hR hr h2 (by linarith only [h_u]) (by linarith only [h_v]) (hs.ready i hi _ _ _ φ (A.next (B.n k) i) rfl hQ hr) (tallR P₀ A i) hH rfl hp hc
    rw [← h₂,← hfield]; rw [(X i).theta] at hm; exact hm
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.leg
