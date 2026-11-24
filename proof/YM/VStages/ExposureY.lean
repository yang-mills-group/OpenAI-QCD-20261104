import YM.VStages.Yarn
import YM.VStages.RegisterY
import YM.VStages.Wardpost
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
open Rails.Kin Massive.Filament
variable (M₀:Arrow N) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

include he
lemma realY (i:ℕ) : 1 ≤ clockQ P₀ A x i:=by obtain ⟨Q,h,hW⟩:=orbitR P₀ A X E he i; exact hW.root
lemma realX (i:ℕ) : 0 < dial P₀ A x i:= zero_lt_one.trans_le (scalePay P₀ A (realY P₀ A X E he) _)
lemma positive (i:ℕ) : 0 < corridor P₀ A E i x:=by
   obtain ⟨Q,h,hW⟩:= orbitR P₀ A X E he i; exact mul_pos (pow_pos (by norm_num) _) (mul_pos h.outE hW.seed)
lemma goal_cap (i:ℕ) : corridor P₀ A E i x ≤ least (A.spacing i)*corridor P₀ A E (i+1) x:=by
   obtain ⟨Q,h,hW⟩:=orbitR P₀ A X E he i; rw [ville]; unfold corridor Quant.crest
   let d:= fees P₀ A E i; let d':= fees P₀ A E (i+1); let g:= Jets.Touch.chip (A.spacing i) (clockQ P₀ A x i); let f:= Jets.Touch.chip (A.spacing i) (run (A.spacing i) (clockQ P₀ A x i)); let T:= least (A.spacing i)
   have hh : 2*d ≤ T*d':=by apply le_trans _ h.lead; nlinarith only [show 0≤d from h.outE.le,mul_nonneg (sq_nonneg Q) (show 0 ≤ d from h.outE.le)]
   have hx :d*g ≤ T*d'*f:= (mul_le_mul_of_nonneg_left hW.warm h.outE.le).trans (by linarith only [mul_le_mul_of_nonneg_right hh (show 0 ≤ f from hW.shoot.le)]) -- maybe change
   linarith only [hx]
lemma realφ (i:ℕ):0 < Rotary.chartR (clockQ P₀ A x i):= by linarith only [scaleRay P₀ A (realY P₀ A X E he) i]
lemma revport (Z₀:ℂ→ Pixel (A.ring (B.n k) (i+1)) N)(s:ℝ)(hv:Sails P₀ A X B T V U E Pt k M₀ (i+1) (Struck.Library.grow (dial P₀ A x (i+1)) Z₀) s): FromS P₀ A X B T V U E Pt k M₀ i (Struck.Library.grow (dial P₀ A x i) Z₀) s:=by
    have h:= Suburb.terminal P₀ A (i+1) x; rw [notch,start_clock] at h; exact Spire.Moraine.porter h Z₀ (scaleRay_eq P₀ A (realY P₀ A X E he) i).symm _ _ _ _ hv
omit he
abbrev HatWalk (u:Flavor N→ℝ)(r x:ℝ)(i:ℕ) := Library.grow (dial P₀ A x i) (family P₀ A B Y u r i)
local notation "Hy"=> HatWalk P₀ A B Y
abbrev creditsY (x:ℝ)(i:ℕ):= dial P₀ A x i * Kin.profit (A.spacing i) (Y i) θ (clockQ P₀ A x i) M₀.tip M₀.head
local notation "TQ"=>creditsY P₀ A B M₀ Y x
-- hat altitude equality
lemma walks0 (i:ℕ)(q r:ℝ)(u:Flavor N→ℝ) : (HatWalk P₀ A B Y u r q i)= family P₀ A B Y u (r*dial P₀ A q i) i := by
   funext z x'; unfold HatWalk Library.grow family Kin.experimental; rw [Complex.ofReal_mul,mul_assoc]
include hh
lemma pricing (r:ℝ)(hi:i≤n): hear (A.spacing i) (HatWalk P₀ A B Y M₀.tip r x i) θ (clockQ P₀ A x i) M₀.head=r*creditsY P₀ A B M₀ Y x i:=by
    rw [walks0]; unfold family creditsY; rw [Kin.goldBook _ _ _ _ _ (hh.walks i hi).2.2,mul_assoc]
lemma pinnedY (r:ℝ)(hi:i≤n)(hN:2≤ N)(h:(∑ b,M₀.tip b)=0) :
    let Z₁:= HatWalk P₀ A B Y M₀.tip r x i; Pinned Z₁ (Rotary.chartR (clockQ P₀ A x i)) (fan (A.spacing i) θ (clockQ P₀ A x i)) M₀ (hear (A.spacing i) Z₁ θ (clockQ P₀ A x i) M₀.head):=by
    rw [walks0]; exact Kin.arcT _ _ (hh.walks i hi).2.2 (hh.walks i hi).1 _ h hN _
abbrev beginQ (x:ℝ):= dial P₀ A x n*Aperture.wealthy (A.spacing n) θ (clockQ P₀ A x n)
include he hX hp
lemma glimpse (r:ℝ)(hr:0<r)(ht:r*beginQ (n:=n) P₀ A x ≤ corridor P₀ A E n x): Sails P₀ A X B T V U E Pt k M₀ n (HatWalk P₀ A B Y M₀.tip r x n) (r*beginQ (n:=n) P₀ A x):=by
     unfold beginQ at ht ⊢; rw [← mul_assoc] at ht ⊢; rw [walks0]; exact boots P₀ A X B T Z V U W F hp hX E he M₀ _ _ (mul_pos hr (realX P₀ A X E he n)) (bare_fam P₀ A X B T _ _ _ Y hh _ _) ht  -- argument order he M
lemma worthy : creditsY P₀ A B M₀ Y x n=beginQ (n:=n) P₀ A x ∧ 0 < beginQ (n:=n) P₀ A x:=by
     let q:= beginQ (n:=n) P₀ A x; let t:= corridor P₀ A E n x; have hp':0< q:= mul_pos (realX P₀ A X E he n) (mul_pos (sq_pos_of_pos (fan_pos ..)) (realφ P₀ A X E he n)); let p:=t/q; have ht:0<p:= div_pos (Melt.positive P₀ A X E he n) hp'; have h:p*q=t:=div_mul_cancel₀ _ hp'.ne'
     have hY:=(glimpse P₀ A X B T Z V U W F hp hX E M₀ he Y hh p ht h.le).shape M₀.head -- order glimpse
     rw [M₀.has_one,mul_one] at hY; exact ⟨mul_left_cancel₀ ht.ne' ((pricing P₀ A X B T V W F M₀ Y hh p (show n≤n from le_rfl)).symm.trans hY),hp'⟩

variable (ht:2*tol+tol^2≤1/2)(hN:2≤ N)(hθ:(∑ i,M₀.tip i)=0)(hs:StampBook P₀ A X E B k n x)
include hN hθ ht hs
-- proof of corridor, each step uses EFFECTIVE z chart in its own angle.
abbrev PaidY (Pt:ℕ→BudgetPoint)(i:ℕ)(r:ℝ):= Sails P₀ A X B T V U E Pt k M₀ i (HatWalk P₀ A B Y M₀.tip r x i) (r*creditsY P₀ A B M₀ Y x i)
abbrev Dues (x:ℝ)(i:ℕ): Prop:= let v:=creditsY P₀ A B M₀ Y x i; let s:=creditsY P₀ A B M₀ Y x (i+1); let L:=A.spacing i; least L*s≤ v ∧ v ≤ most L*s
structure Paying (Pt:ℕ→BudgetPoint)(i:ℕ) :Prop where
   base : 0<creditsY P₀ A B M₀ Y x i
   cap :∀ j,i ≤ j→ j ≤ n→∀ v:ℝ,0<v→ v*creditsY P₀ A B M₀ Y x i≤ corridor P₀ A E i x → PaidY P₀ A X B T V U E M₀ Y Pt j v ∧ v*creditsY P₀ A B M₀ Y x j≤ corridor P₀ A E j x
   berth : ∀ j,i ≤ j→ j < n→ Dues P₀ A B M₀ Y x j
local notation "Φg"=>Paying P₀ A X B T V U E M₀ Y Pt
omit hN hθ ht hs in
lemma beginsQ : Paying P₀ A X B T V U E M₀ Y Pt n :=by
   obtain ⟨h1,h2⟩:= worthy P₀ A X B T Z V U W F hp hX E M₀ he Y hh
   refine ⟨by rw [h1]; exact h2,fun l hl hv v h hh' =>?_,fun _ h hh=>by omega⟩
   have hb:= le_antisymm hv hl; subst l; refine ⟨?_,hh'⟩; unfold PaidY; rw [h1] at hh' ⊢; exact glimpse P₀ A X B T Z V U W F hp hX E M₀ he Y hh v h hh'
set_option maxHeartbeats 700000 in
lemma passY (hi:i < n)(h:Paying P₀ A X B T V U E M₀ Y Pt (i+1) ): Paying P₀ A X B T V U E M₀ Y Pt i :=by
   let t:=corridor P₀ A E (i+1) x; let Q:=clockQ P₀ A x i; let s:= TQ (i+1); let p:= TQ i; let L:= A.spacing i; let L':= least L; let L'' := most L
   have hs':0<s:=h.base; let v:= t/s; have hv:0<v:=div_pos (Melt.positive P₀ A X E he (i+1)) hs'; have h_t:v*s=t:=div_mul_cancel₀ _ hs'.ne'
   have hz (b:ℝ)(h_b:0<b)(hS:b*s≤ t): L'*(b*s)≤ b*p∧ b*p ≤ L''*(b*s)∧ PaidY P₀ A X B T V U E M₀ Y Pt i b :=by
      have hH:= h.cap (i+1) le_rfl hi b h_b hS; let H:= Hy M₀.tip b x i; let G:= Fz b (i+1); let F':= Library.grow (dial P₀ A x i) G
      have hg:F' 0= F (i+1):=by unfold F' Library.grow; rw [mul_zero]; exact neutral P₀ A X B T V W F Y hh hi _ _
      have hu:H= Bank.LeapY (stepper P₀ A X B T i) Kz (A.next (B.n k) i) F' (V (i+1)) (W i):=by
             unfold H HatWalk; rw [hops P₀ A X B T V W F Y hh M₀.tip b hi]; rfl
      let s':= hear L H θ Q M₀.head; have h₁:= leg P₀ A X B T Z V U W F hp hX E he M₀ F' H (b*s) hi ht hg hu hs (revport P₀ A X B T V U E M₀ he G _ hH.1) hS
      have hh':b*p=s':=(pricing P₀ A X B T _ _ F M₀ Y hh b hi.le).symm
      change _ ∧ _ ∧ Sails P₀ A X B T V U E Pt k M₀ i H (b*p); rw [hh']; exact ⟨h₁.growth _ M₀.has_one rfl,h₁.mass,h₁.leg (pinnedY P₀ A X B T _ _ F M₀ Y hh b hi.le hN hθ)⟩
   obtain ⟨hy,hk,-⟩:= hz v hv h_t.le
   have hg:L'*s≤p:=le_of_mul_le_mul_left (show v*(L'*s)≤ v*p from by linarith only [hy]) hv
   have hL:0<L':=potential L
   refine ⟨(mul_pos hL hs').trans_le hg,fun j hq hj r hr hε=>?_,fun j hq hj=>?_⟩
   · have h':= le_trans (show r*p ≤ _ from hε) (goal_cap P₀ A X E he i); change r*p ≤ L'*t at h'
     have hx:r*s ≤ t:=le_of_mul_le_mul_left (a:=L') (by linarith only [h', mul_le_mul_of_nonneg_left hg hr.le]) hL

     rcases eq_or_lt_of_le hq with hl|hl; · subst j; exact ⟨(hz r hr hx).2.2,hε⟩
     exact h.cap j hl hj r hr hx
   rcases eq_or_lt_of_le hq with hl|hl; · subst j; exact ⟨hg,le_of_mul_le_mul_left (show v*p≤ v*(L''*s) from by linarith only [hk]) hv⟩
   exact h.berth j hl hj
lemma flightY (i:ℕ)(hi:i ≤ n): Paying P₀ A X B T V U E M₀ Y Pt i :=by
   induction hi using Nat.decreasingInduction with
   | self=> exact beginsQ P₀ A X B T Z V U W F hp hX E M₀ he Y hh
   | of_succ i hi ih=> exact passY P₀ A X B T Z V U W F hp hX E M₀ he Y hh ht hN hθ hs hi ih
structure Shot (Pt:ℕ→ BudgetPoint)(v r:ℝ):Prop where
   beam : 0<v
   request : v*creditsY P₀ A B M₀ Y x 0=r
   leg : ∀ i:ℕ,i ≤ n→ PaidY P₀ A X B T V U E M₀ Y Pt i v ∧ v*creditsY P₀ A B M₀ Y x i≤ corridor P₀ A E i x
   swell :∀ i:ℕ,i<n→ Dues P₀ A B M₀ Y x i
lemma sights (r:ℝ)(hr:0<r)(hw:r≤corridor P₀ A E 0 x):∃ v:ℝ, Shot P₀ A X B T V U E M₀ Y Pt v r:=by
   obtain ⟨h1,h2,h3⟩:= flightY P₀ A X B T Z V U W F hp hX E M₀ he Y hh ht hN hθ hs 0 (by omega)
   let v := r / (TQ 0); have ht: v*(TQ 0)=r:=div_mul_cancel₀ _ h1.ne'; have hv:0<v:=div_pos hr h1; exact ⟨v,hv,ht,fun i hi=> h2 i (by omega) hi v hv (ht.trans_le hw),fun i=> h3 i (by omega)⟩
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.sights
