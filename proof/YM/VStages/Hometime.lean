import YM.VStages.Flung
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
namespace Affair
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Calm P₀ A X x)
local notation "OC"=> fun i=>A.ring (B.n k) i
lemma orbitTall (v:Side)(i:ℕ): v.val ≤ (A.ring v i).val:= Nat.le_mul_of_pos_right _ (A.den i).pos
lemma orbitEven (B:Side)(i:ℕ)(hb:Even B.val): Even (A.ring B i).val:= Even.mul_right hb _
include hp hX hc
lemma soul (W: Grid (A.ring (B.n k) n)):Cove.light _ (F n W)=primalD (A.ring (B.n k) n) N (V n) (U n) W:=by
   rw [hp.bare]; exact (prim P₀ A X hc B T hX _ _ (hp.window n le_rfl).2.1 k).2 W
-- need prop hX hc includes!

omit hp hc hX
lemma staysL (i:ℕ): (stepper P₀ A X B T i).patch.Branches K su:= (A.ticket i).owns
include hp hX hc
lemma realpath (hN:Even N)(i:ℕ)(he:i≤ n): Continuous (F i)∧ Rain.realP (F i)∧ ProperF (F i):=by
    induction he using Nat.decreasingInduction with
    | self=>
      have hk:=soul P₀ A X B T Z V U W F hp hX hc; let U':= (⟨V n,0,U n⟩:Cut ((OC) n) N); obtain ⟨hu,hv,-⟩:=dawning U' rfl hk hN; exact ⟨hu,hv,garbs hk⟩
    | of_succ i hi h=>
      let S:=stepper P₀ A X B T i; obtain ⟨he,hT,hU⟩:= h; have hh:= hp.relay i hi; let Q:= hh.body; let W':= F (i+1); let X':= F i; have hW:= (A.ticket i).owns
      exact ⟨(Rain.marchingQ S (A.next (B.n k) i) W' _ hW he _ X' hh.real Q).1, sunlightQ S _ _ _ _ W' _ hh.real hW he Q hT,marchPQ (S:=S) _ _ _ _ hW hU he hh.real Q⟩

lemma minorR (i:ℕ) (hi:i<n)(hE:Even N)(hx:1<(A.ring (B.n k) i).val):
  (((stepper P₀ A X B T i).visit K (A.next (B.n k) i)).penaltyZ (V (i+1)) su)^spare ((OC) i)*(cBer (F i) 1).re ≤ (Cvol (F i)).re:=by
   obtain ⟨hF,hG,h⟩:= realpath P₀ A X B T Z V U W F hp hX hc hE (i+1) hi
   obtain ⟨hp',hV',h'⟩:= realpath P₀ A X B T Z V U W F hp hX hc hE i hi.le
   have hy:= hp.relay i hi; let hj:= hy.body
   let s:=stepper P₀ A X B T i; let u:= V (i+1); let S:= s.visit Kz (A.next (B.n k) i); let n':= A.ring (B.n k) (i+1); let c:= A.ring (B.n k) i
   have hk: s.patch.Branches K su:= (A.ticket i).owns
   let p (j:Grid n'):= (cBer (F (i+1)) j); let q (x:Grid c):= cBer (F i) x; let Ky:=gain (W i)⁻¹ c N; let L:ℝ:= (S.penaltyZ u su)^spare c
   have hh(U:Grid c): S.push u (fun j=> (p j).re) U=Ky*(q U).re:=by
         have hv: (ber _ (advanceF s Kz (A.next (B.n k) i) (F (i+1)) u U)).re= _ := (IV.voicingQ hk _ hF hG _ U).2
         apply hv.symm.trans; rw [show advanceF s Kz _ (F (i+1)) u U=gBody c (W i) (F i U) from hj U]; change (ber _ (Cove.light _ (wearK c N _ _))).re=_; rw [Rain.crestP]; simp; rfl
   have hI: Integrable p (prior su n'):= ((peakW n' N).continuous.comp hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hf: GaugeInvariant (S.push u (fun j=>(p j).re)):=by
       intro k U; rw [hh,hh,show q (Lattice.gauge k U)=q U from ?_]; change ber _ (Cove.light _ _) = _; rw [← no_jac N k,h'.gauges]; rfl
   have hv:=Massive.Pressure.Average.smooth hx su u S (zero_le_one.trans (hp.window (i+1) hi).2.2.1) hk (fun j => (p j).re) hI.re (fun j => (hG j).2) hf (1:Grid c)
   rw [hh 1,show (∫ j,(fun j=>(p j).re) j ∂prior su n') =(Cvol (F (i+1))).re from integral_re hI,(Rain.marchingQ s _ (F (i+1)) Kz hk hF u _ hy.real hj).2, Complex.smul_re, smul_eq_mul] at hv
   change L*(q 1).re ≤_; rw [mul_left_comm] at hv; exact le_of_mul_le_mul_left hv (show 0<Ky from pow_pos (inv_pos.mpr hy.real) _)
end Affair
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Affair.minorR
