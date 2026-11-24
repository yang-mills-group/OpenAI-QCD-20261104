import YM.Profiles.Counts
import YM.VStages.Votaries
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
namespace Counter
open Work.E09 Next.Rank -- unknown
namespace Economies
open Reference.Sharp Asymptotics
open Finset
variable (θκ:ℝ) (hX:∀ i:ℕ,Cave (A.spacing i) (clockQ P₀ A x i) θ)
local notation "St"=> Counter.stampR P₀ A
local notation "B" t=>radiusB (A.scale x t)
local notation "Λ"=> su.slopeConstant
noncomputable def ray (i:ℕ) :ℝ:=Real.log ((A.spacing i).val:ℝ)
lemma fluence (h:j≤k): Real.log ((St j k):ℝ)= A.measure k-A.measure j:=by
   rw [Track.measure,Track.measure,stamps P₀ A h,Nat.cast_mul,Real.log_mul (by positivity) (show (↑(St j k):ℝ)≠0 from by exact_mod_cast (stamp_g P₀ A h).ne')]; ring
lemma shadeL (n:ℕ) :ray P₀ A n≤ ray P₀ A 0 + Real.log 3*n:=by
    induction n with
    | zero=>simp
    |succ n ih=>
       let Z:=fun i=>((A.spacing i).val:ℝ); have hZ(i):0 < Z i:=by unfold Z; positivity -- Side.
       have hd:(A.spacing (n+1)).val ≤3*(A.spacing n).val:=by simp_rw [Track.spacing,A.length_eq]; exact (A.nexts n).2.2.2
       have h: ray P₀ A (n+1) ≤ ray P₀ A n + Real.log 3:= by
           change Real.log (Z _) ≤ Real.log (Z n)+ Real.log 3; rw [add_comm (Real.log _), ← Real.log_mul (by norm_num) (hZ n).ne']; exact Real.log_le_log (hZ _) (by unfold Z; exact_mod_cast hd)
       push_cast; nlinarith only [ih,h]
lemma anyRay (e:ℝ)(he:0<e):∀ᶠ i in atTop, ray P₀ A i ≤ e* A.measure i:= (A.outlay (ray P₀ A 0) (Real.log 3) e he).mono fun i h=> (shadeL P₀ A i).trans h
-- arbitrary final C threshold on step.Lat.Power variant. measure slope USER Ln;
lemma endless (x:ℝ): Tendsto (Track.scale A x) atTop atTop:=tendsto_atTop_add_const_left _ x (A.long.const_mul_atTop (Gauge.slopeConstant_pos simple)) -- lemma name
lemma futureBudget (e:ℝ)(he:0<e) :∀ᶠ i in atTop, (Track.scale A x i)^(1/2:ℝ) ≤ e*A.measure i:=by
   have hs:=Gauge.slopeConstant_pos simple; let a:= e/(2*Λ); have ha:0<a:=by unfold a; positivity
   have hf : ∀ᶠ y:ℝ in atTop, y ^ (1/2:ℝ) ≤ a*y:=by
       filter_upwards [(Real.tendsto_sqrt_atTop).eventually_ge_atTop (1/a),eventually_ge_atTop (0:ℝ)] with y hy h; rw [←Real.sqrt_eq_rpow, ← Real.sq_sqrt h] -- rw both.O use dim.S
       rw [Real.sqrt_sq (Real.sqrt_nonneg y)]; nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).1 hy) (Real.sqrt_nonneg y)]
   filter_upwards [(endless P₀ A x).eventually hf,(A.long.atTop_mul_const hs).eventually_ge_atTop x] with i hi ht
   change x ≤ A.measure i * Λ at ht; have h:Λ*A.measure i ≥ x:=mul_comm Λ (A.measure i) ▸ ht
   exact hi.trans ((mul_le_mul_of_nonneg_left (show Track.scale A x i≤2*Λ*A.measure i from (add_le_add_left h (Λ*A.measure i)).trans (by linarith)) ha.le).trans_eq (by unfold a; field_simp))
lemma radiusTiny (e:ℝ)(he:0<e):∀ᶠ i in atTop, (B i:ℝ)^2 ≤ e* A.measure i:=by
   have h:=(radiusB_small (1/2) (by norm_num) 2).bound (show (0:ℝ)<1 by norm_num)
   filter_upwards [(endless P₀ A x).eventually h,futureBudget (x:=x) P₀ A e he,(endless P₀ A x).eventually_gt_atTop 0] with i hf hp hx; rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),one_mul] at hf; exact hf.trans hp
lemma packSmall (M:ℕ)(e:ℝ)(he:0<e) :∀ᶠ i:ℕ in atTop, Real.log (Rapture.packN (A.spacing i) (clockQ P₀ A x i) M:ℝ) ≤ e*A.measure i:=by
   let a:=e/3; have ha:0<a:=by unfold a; positivity
   filter_upwards [anyRay P₀ A a ha, radiusTiny P₀ A (x:=x) (a/((M:ℝ)+1)) (by positivity), A.outlay 1 0 a ha] with i h1 h2 h3; let q:ℝ:=(B i:ℝ); let L:ℝ:=(A.spacing i).val; have hm:0<L:=by unfold L; positivity
   have hp:0 < ((M:ℝ)*q^2+1):=by positivity
   have hV : ((Rapture.packN (A.spacing i) (clockQ P₀ A x i) M):ℝ) ≤ L*((M:ℝ)*q^2+1):=by
       unfold Rapture.packN; push_cast; have hx:1 ≤ L:= (by unfold L; exact_mod_cast (A.spacing i).property); rw [augmented P₀]; nlinarith only [hx]
   apply le_trans (Real.log_le_log (by unfold Rapture.packN; push_cast; positivity) hV); rw [Real.log_mul hm.ne' hp.ne']; change Real.log L ≤ _ at h1; have hh:q^2*((M:ℝ)+1) ≤ a*A.measure i:=by
       apply (le_div_iff₀ (by positivity : 0<((M:ℝ)+1))).1; exact h2.trans_eq (by ring) -- le_div_iff.
   have ht:=Real.log_le_sub_one_of_pos hp; have hx0:=sq_nonneg q; unfold a at *; linarith only [h1,hh,ht,hx0,h3]
-- last level under side.St.Valid Lean 
include hX
noncomputable abbrev maturity (j M:ℕ):= Nat.find (rises P₀ A hX j M) -- rises ambiguous
local notation "J'" j:arg M:arg=> maturity P₀ A hX j M
lemma canyonJ (M:ℕ) : Tendsto (fun j=> maturity P₀ A hX j M) atTop atTop:= by refine tendsto_atTop.2 fun i=>?_ ; filter_upwards [eventually_ge_atTop i] with j h; exact h.trans (post P₀ A hX M _ rfl).1
lemma levelGain (e:ℝ)(he:0<e) (M:ℕ):∀ᶠ i:ℕ in atTop, A.measure (J' i M) ≤ (1+e)* A.measure i:=by
    let a:=e/(1+e); have ha: 0<a:=by unfold a; positivity
    filter_upwards [(canyonJ P₀ A hX M).eventually (packSmall P₀ A (x:=x) M a ha)] with i h
    let u:= J' i M; have hh:=post P₀ A (j:=i) hX M u rfl; have hS:0< (↑(St i u):ℝ):=by exact_mod_cast stamp_g P₀ A hh.1
    have hg:= (Real.log_le_log hS (show (↑(St i u):ℝ) ≤(Rapture.packN _ _ _ :ℝ) by exact_mod_cast hh.2.2)).trans h
    rw [fluence _ _ hh.1] at hg
    unfold a at hg; change A.measure u -A.measure i ≤ e/(1+e)* _ at hg; field_simp at hg; nlinarith only [hg]
end Economies
end Counter
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Counter.Economies.levelGain
