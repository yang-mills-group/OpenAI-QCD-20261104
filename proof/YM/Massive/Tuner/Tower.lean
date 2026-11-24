import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Tuner.Limits
import YM.Massive.Pressure.Major
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)


/-!
Bpressure analogue. `K` a lower-margin expense (large positive), `A` majorant size.
uniform over the x (β) tail, *all* k on the M from the initial DomainF, *all* steps
in these positive-common-mass histories. Include actual lower and upper as used in E.
Use `#` exactly: spare = 3 v + 1, rich = 3 v - 3. In particular bounds may be used
without paying a `log(h)` in every volume degree. On passing to the large x gates,
the torus populations can also pay the last few powers when wanting bounds with matched
power `3v`; here state with the displayed actual powers. Never assume the precision
needed to do a stability argument on perturbing the *entire* mass ray has been achieved
just by this positive-common-mass lower.
-/
variable {n0 : ℕ} {B₀ : Side} {J : Patch}
variable (L : HaarBudget su)

variable {D'' θc:ℝ}
variable (hG:Gated θc T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0) (hk:O.Branches T'.bind su)(hN:Even N)
variable (hg:Invoice g Q.table V₁ T₁ σ η α D Λ)
variable (hH:∀ y,x≤y→Heat b' T' O B₀ A D'' Ω κ τ'.t y a d Λ)
variable (hF:B.n k=B₀*O.L^j)(hx:4 ≤ (B.n k).val)(he:Even (B.n k).val)
include hG hH
lemma costs (i:ℕ)(hi:i≤n) : 1 ≤ V i ∧ |U i|≤1:=by
  obtain ⟨hz,_,hb,h⟩:= hG.costs i hi; let hp:= hH _ (matters O.L x (n-i)); exact ⟨le_trans (by have hh : 2≤ hatG O n i x:=hp.enough; linarith : (1:ℝ)≤ hatG O n i x/2) hz.1,hb.trans hp.range_⟩
include hN hk hF hx he
include hg
set_option quotPrecheck false
private lemma paid (i:ℕ)(hi:i≤n)(M:Voice (towerQ O B n i k) N)(z:ℝ)(hz:0<z)
    (hp:Enn (P' i) b' O.L (delay O n i x) τ'.t (1/8) (duo M.P M.K))
    (hy:A0 i=z • songBody B M g (P' i) (X i) x (V i) (U i) (k:=k) (i:=i) (T':=T')) : NormPrices L T' (gaugeSize O.L (delay O n i x)) A D'' (A0 i) z:=by
   have hn:4 ≤ (towerQ O B n i k).val:=by unfold towerQ; rw [feetM,PNat.mul_coe]; exact hx.trans (Nat.le_mul_of_pos_right _ (O.L^(n-i):Side).property)
   have h0 := hH (delay O n i x) (matters ..); let q:=gaugeSize O.L (delay O n i x)
   obtain ⟨hβ,_,hM,-⟩:= hG.costs i hi
   obtain ⟨h1,h2,-⟩:=proper B b' g A0 hG hk hN i hi; apply NormPrices.byRoots L _ _ _ (lt_of_lt_of_le (by decide) hn) hz.le h0.g_pos _ h1
   · intro Z; rw [show A0 i Z=z • songBody B M g (P' i) (X i) x (V i) (U i) (k:=k) (i:=i) (T':=T') Z from congr_fun hy Z,norm_smul,Real.norm_of_nonneg hz.le]
     exact mul_le_mul_of_nonneg_left (h0.high _ _ (hG.clock i) M hp (tile O i) _ _ _ _ (hg.he _ hi).1 hM hβ.1 hβ.2 _) hz.le
   let W:=L.small*q^su.lieDim; let d0:=Real.exp (-(T'.bind.penalty*2))
   have hb : 0≤ V i:= zero_le_one.trans (costs _ _ _ _ hG hH i hi).1
   have hw : 0≤ W:= mul_nonneg L.positive.le (pow_nonneg h0.g_pos.le _); have hD : 0 ≤ W*d0:=mul_nonneg hw (Real.exp_pos _).le
   cases i with
   | zero=>
     have htB : Even (towerQ O B n 0 k).val:=by unfold towerQ; rw [feetM,PNat.mul_coe]; exact Even.mul_right he _
     have ht : V 0*q^2 ≤ 2:=by
       let u:=run O.L (delay O n 0 x); have hx':V 0 ≤ 2*u:=hβ.2; have hh:u*q^2=1:=h0.exact_; linarith only [mul_le_mul_of_nonneg_right hx' (sq_nonneg q),hh]
     apply le_trans _ (size_start (passportM O.J O.order_cut) b' L q h0.g_pos h0.g_le hb ht htB hn _ M h0.fan_ hp h0.chip (hG.clock 0).ball (X 0) _ _ _ _ (U 0) z (costs _ _ _ _ hG hH 0 hi).2 hz hy (hG.begin)) -- needs J argument
     exact mul_le_mul (mul_le_mul_of_nonneg_left (Globe.earns h0.cap) hz.le) (pow_le_pow_left₀ hD (mul_le_of_le_one_right hw (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg T'.bind.penalty_pos.le zero_le_two)))) _) (pow_nonneg hD _) (mul_pos hz (Real.exp_pos _)).le -- prod shape
   | succ i=>
     have hc : towerQ O B n (i+1) k = B₀*O.L^(j+(n-(i+1))) :=by unfold towerQ; rw [feetM,hF,pow_add,mul_assoc]
     have hB : z*Globe.expo D'' (towerQ O B n (i+1) k) ≤ (cBer (A0 (i+1)) 1).re:= h0.low _ (P' (i+1)) M hp (tile O (i+1)) _ _ (V (i+1)) _ hM _ hc z _ hz hy h2
     have hv:0≤V i:=zero_le_one.trans (costs _ _ _ _ hG hH i (by omega)).1
     have hk':V i*q^2≤4:=by
         let Q':=delay O n (i+1) x; let u:=run O.L Q'; have ht:u*q^2=1:=h0.exact_
         have hh:hatG O n i x ≤ 2*u:=by unfold hatG; rw [← next_delay O x hi]; exact h0.adjacent
         have he:V i ≤ 4*u:=by linarith only [(show V i ≤2*hatG O n i x from (hG.costs i (by omega)).1.2),hh]
         linarith only [ht,mul_le_mul_of_nonneg_right he (sq_nonneg q)]
     let Z:= ((Pike O i).visit T'.bind (lift0 B (t:=k) hi)).penaltyZ (V i) su
     apply le_trans _ (minor B b' g A0 hG hk hN i hi (by omega) hv); rw [mul_comm]; -- check
     exact mul_le_mul (pow_le_pow_left₀ hD (Massive.Pressure.noiseZ L ((Pike O i).visit T'.bind (lift0 B (t:=k) hi)) h0.g_pos h0.g_le hv hk') _) hB (mul_pos hz (Real.exp_pos _)).le (pow_pos (StepData.penaltyZ_pos ..) _).le -- position

lemma pressured : Regular L θc A D'' T' Q B b' x κ τ' g P' X Y D W' k V U Wv A0 :=by
   have H i hi:= proper B b' g A0 hG hk hN i hi
   refine { hG with truepath:=fun i hi=>(H i hi).2.2, flows:=fun i hi=>(H i hi).1, real:=fun i hi=>(H i hi).2.1, mass:=fun i hi=> (costs _ _ _ _ hG hH i hi).2,beta:=fun i hi=>(costs _ _ _ _ hG hH i hi).1, leg:=?_,solvent:=?_ }
   swap
   · intro i hi; obtain ⟨_,_,_,M,z,hz,hM,h⟩:=hG.costs i hi; exact ⟨M,z,hz,hM,h,paid _ _ _ _ L hG hk hN hg hH hF hx he i hi M z hz hM h⟩
   intro i hi; obtain ⟨_,_,_,M,z,hz,hM,h⟩:=hG.costs i hi; apply lt_of_lt_of_le _ (paid _ _ _ _ L hG hk hN hg hH hF hx he i hi M z hz hM h).lower; have hp:=L.positive; have hq := (hH (delay O n i x) (matters ..)).g_pos; unfold Globe.expo; positivity
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.pressured
