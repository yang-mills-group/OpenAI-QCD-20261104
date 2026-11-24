import YM.Talis.Peak
import YM.Differ.Humming
import YM.Bard.Reel
import YM.Magi.Band
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
variable {S:Flight j j}{K:KernelChoices}{hBP:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K hBP)}
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
-- lengths relative to start s; harvest Warm births Marathon. Reserve one after.F. Note measurement.Rf=L^(2*h*τν). EP lengths ℓ= j.B via u→ z.
variable (ν a δ H:ℕ) (z:ℝ)
noncomputable abbrev WTop (L:Side)(ν H:ℕ)(z:ℝ):= measureV L ν z ^ H
noncomputable def Jc (L:Side)(ν H:ℕ)(z:ℝ):= distV L ν z*(2*H)
noncomputable abbrev bookA (L:Side)(ν H a:ℕ)(z:ℝ):= Jc L ν H z+distV L a z
noncomputable abbrev disc (δ:ℕ)(z:ℝ):= distV L δ z
noncomputable abbrev rollA (L:Side)(ν H a δ:ℕ)(z:ℝ):=disc L δ z+bookA L ν H a z
-- `bookB` total stage to read; merge distance `bookB−δ`; ℓ distance `bookB ź`
noncomputable abbrev bookB (L:Side)(ν H u:ℕ)(z:ℝ):= Jc L ν H z - distV L u z
variable {L}
lemma joy (z:ℝ):1 ≤ WTop L ν H z:= one_le_pow₀ (uniformV ..)
section
variable (L)
local notation "Kc"=> Jc L ν H
local notation "Ω"=> WTop L ν H z
local notation "Lp"=> (L.val:ℝ)
lemma winT : Lp^(Kc z)=Ω^2:=by unfold Jc WTop measureV; rw [pow_mul]; nth_rw 1 [mul_comm]; rw [pow_mul] -- order maybe
lemma wins : Lp^(bookA L ν H a z)= Ω^2*EV a z:=by unfold bookA; rw [pow_add,winT]
lemma rolls : Lp^(rollA L ν H a δ z)= EV δ z * ((Ω)^2*EV a z) :=by rw [rollA,pow_add,wins]
lemma prunes (hu:τ a z≤ Jc L ν H z): Lp^(bookB L ν H a z)= Ω^2/EV a z:=by
    rw [eq_div_iff (χone L z a|>.ne')]; change _ * Lp^ (τ a z)=_; rw [←pow_add,show _- _+_=_ from Nat.sub_add_cancel hu,winT] -- binder abbrev
lemma spanB (hu:τ a z≤Jc L ν H z)(hd:disc L δ z ≤bookB L ν H a z): Lp^(bookB L ν H a z - disc L δ z)= Ω^2/(EV a z*EV δ z):=by
    rw[← div_div,←prunes L ν a H z hu,eq_div_iff (χone L z δ|>.ne')]; change Lp^(_- _) * Lp^(disc L δ z) =_; rw[←pow_add,Nat.sub_add_cancel hd]
-- cost aging any possible gearT in this journey + widths after. Include `Kj=T0+rollA`, one after for Vest.
structure FloorA (L:Side)(ν H a δ:ℕ)(z:ℝ):Prop where
    sold : 1 ≤ ticksV L z
    early : 0 < disc L δ z
    mid : 0 < bookA L ν H a z
    seats : rollA L ν H a δ z+1 ≤distV L (ν+1) z
variable {ν δ a H}
lemma rippleA (hδ:δ ≤ν)(ha:a ≤ν) :∀ᶠ z in atTop, FloorA L ν H a δ z:=by
   filter_upwards [(buysV L).eventually_ge_atTop (1+2*H+2)] with z hx; let k:=ticksV L z; let n:= k^ν; have hk:1 ≤ k:=(by omega); have hn:1≤ n:= one_le_pow₀ hk; have ht:k^a>0:= one_le_pow₀ hk; refine ⟨hk,by exact pow_pos (show 0<k from hk) _,by unfold bookA; exact Nat.add_pos_right _ ht,?_⟩
   change k^δ+(n*(2*H)+k^a)+1 ≤ k^(ν+1); rw[pow_succ]; have hA:k^a ≤ n:= pow_le_pow_right₀ hk ha; have hh:k^δ ≤ n:= pow_le_pow_right₀ hk hδ
   calc
       _ ≤ n*(1+2*H+2) :=by simp only [Nat.mul_add,Nat.mul_one]; omega
       _ ≤ n*k:=Nat.mul_le_mul_left n hx
lemma cliff {c d:ℕ}(hp:c<d):∀ᶠ z:ℝ in atTop,τ c z<τ d z:=by filter_upwards [(buysV L).eventually_ge_atTop 2] with x hx using (pow_lt_pow_right₀ (show 1<ticksV L x from by omega) hp) -- name
variable (H) {e u u':ℕ}
structure FloorB (L:Side)(ν H δ e u:ℕ)(z:ℝ) : Prop where
    stop : distV L e z < Jc L ν H z
    lives: distV L u z < Jc L ν H z
    prep : bookB L ν H e z < bookB L ν H u z -disc L δ z
    book : disc L δ z < bookB L ν H u z
    rent : bookB L ν H u z - bookB L ν H e z ≤ distV L e z
lemma rippleB (he:e<ν)(hu:u < e)(hd:δ<e)(hH:0<H) :∀ᶠ z in atTop, FloorB L ν H δ e u z:=by
    let d:=max u δ
    filter_upwards [(buysV L).eventually_ge_atTop 3,cliff L he] with z hx he'; let k:=ticksV L z; have hv:τ u z+ disc L δ z < τ e z:=by
           have hk:1≤ k:=(by omega); have hq:0 < k^d:=pow_pos (by omega) _; change k^u+k^δ<k^e; have hl:d+1 ≤ e:=by unfold d; omega
           apply lt_of_lt_of_le ?_ (pow_le_pow_right₀ hk hl); rw[pow_succ]; calc
                 _ ≤ k^d * 2:=by have hy:k^u ≤ k^d:=pow_le_pow_right₀ hk (le_max_left ..); have hy':k^δ≤ k^d:=pow_le_pow_right₀ hk (le_max_right ..); omega
                 _ < k^d *k:= Nat.mul_lt_mul_of_pos_left (by omega) hq
    have hp:τ e z < Jc L ν H z:= he'.trans_le (Nat.le_mul_of_pos_right _ (by omega)); constructor <;> (try unfold bookB)<;> omega
end
section meter
variable {b d:ℕ}{c:Side}
open Suburb.Melt.Lobby.LeaseV Counter
variable (L)
set_option quotPrecheck false
-- all clock phases on IntervalE. stamp exact.
variable (Jv: IntervalE P₀ A L x z b k)
include Jv
local notation "Lp"=> (L.val:ℝ)
lemma scaleV (hb:b ≤ i)(hd:d ≤ k)(hi:i ≤ d): stampR P₀ A i d=L.val^(d-i):=by
     induction hi with
     | refl=> rw [stampR,Nat.sub_self,pow_zero,Nat.div_self (A.den _).pos]
     | step h ih=> rw [stamp_t P₀ A h, ih (by omega),Jv.starts _ (hb.trans h) (by omega), Nat.succ_sub h,pow_succ]
lemma earnsV (hb:b ≤ i)(hd:d ≤ k)(hi:i ≤ d): A.measure d-A.measure i=Real.log (Lp^(d-i)):=by
    have he:= stamps P₀ A hi; rw[scaleV P₀ A L z Jv hb hd hi] at he -- syntax
    simp only [Track.measure,he,Nat.cast_mul,Nat.cast_pow]; rw[Real.log_mul (show ((A.den i).val:ℝ)≠0 by positivity) (show Lp^(d-i)≠0 by positivity)]; ring
lemma paceV (hb:b ≤ i)(hd:d ≤ k)(hi:i ≤ d): Counter.Hymn.damping P₀ A H d i= (Lp^(d-i))^(-Counter.Hymn.pitchD H):=by
    unfold Counter.Hymn.damping; rw [earnsV P₀ A L z Jv hb hd hi,Real.rpow_def_of_pos (by positivity)]; ring_nf
end meter
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.rippleA
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.spanB
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.paceV
