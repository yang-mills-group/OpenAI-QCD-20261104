import YM.Massive.Stratum.Gondola
/-!
# Telescoping the unmasked/free-ledger fermion shifts for mixed lengths

Error only in terms of the **two** endpoint setups rather than summing
large expenses at every seam. Occurs before proceeding to actual-masked
presentations. See the scope of `Raft.deed`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores Revolve Rudder Eyrie
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {j n i k:ℕ}{Q:Rock j}{J:Plan j}{p:ChartRatio su} (Y:AtlasH Q J p) {F:Towers (Y.length i)}{m:SparkMesh}
local notation "Qq" => Q.Z.top.clip
local notation "Kq" => Q.Z.bind
local notation "u₀" => Q.Z.top.width
open AtlasH
open Fog.Voyage
abbrev flavorWeight (F:ℕ):= Pearl.chargeF*(F:ℝ)
def registerG (s:ℕ→ℝ)(i:ℕ):ℝ:= ∑ j∈Finset.range i,s j
-- will omit alpha eL.T.W.
lemma succeeding (s i): registerG s (i+1)= registerG s i+s i:=Finset.sum_range_succ ..
@[simp] lemma originG (s): registerG s 0=0:=by simp[registerG]

structure Align (Y:AtlasH Q J p)(B:SparkMesh)(S:ℕ→SparkMesh)(n:ℕ):Prop where
  keeps i : i<n →∀ k, (S i).n (k+5)=Y.ring (B.n k) i
lemma ringing (B:SparkMesh)(i:ℕ):Tendsto (fun k=>Y.ring (B.n k) i) atTop atTop:=by
   refine tendsto_atTop.2 fun t=>?_ ;filter_upwards [(B.cofinal.eventually_ge_atTop t.val)] with k hk; exact hk.trans (show (B.n k).val ≤ (Y.ring (B.n k) i).val from Nat.le_mul_of_pos_right _ (Y.orbit i).pos)
lemma sums_log (B:Side)(i:ℕ):Real.log ((Y.ring B i).val:ℝ)=Real.log (B.val:ℝ)+ Y.measure i:=by
   change Real.log ((↑(B.val*(Y.orbit i).val)):ℝ)= _; rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]; rfl

def relic:su.Color:= EuclideanSpace.single Fog.lodging 1
theorem beacon : ‖relic‖=1:= Raft.lodging_st

-- Pose endpoint budget for arbitrary schedule type.
def stamp (J:Plan j)(V:Town):ℝ:= let W: Mist.Ledger:= V.1; |Classical.choose (Raft.calibrated J relic beacon W.1.1.live W.1.2.live W.1.1.bill W.1.2.bill)|
lemma stamp0 (J:Plan j)(V:Town):0 ≤ stamp J V:=abs_nonneg _
namespace AtlasH.Survey
variable {T:ℕ→SparkMesh}
variable (P:Survey Y T n) {R:SparkMesh}

def price_R (x:Side)(i:ℕ): ℝ:= let V:= P.state i;
    readP (rollG J V.wing V.spin.powerG (Y.ring x i)) relic
variable (R)
lemma price_bound (i:ℕ): ∀ᶠ k in atTop, |P.price_R Y (R.n k) i-Pearl.chargeF*(Real.log ((R.n k).val:ℝ)+ Y.measure i)| ≤ stamp J (Y.towns i):=by
  let W:= (Y.towns i).1
  have h:= Classical.choose_spec (Raft.calibrated J relic beacon W.1.1.live W.1.2.live W.1.1.bill W.1.2.bill)
  filter_upwards [(ringing Y R i).eventually h] with k hi
  let he:= (P.state i).spin; rw [← sums_log]; exact (hi he.X he.Y (P.state i).wing).trans (le_abs_self _)

variable (hp:Align Y R T n)
include hp
lemma ascending (hl:i < n): Tendsto (fun k=> P.price_R Y (R.n k) (i+1)-P.price_R Y (R.n k) i) atTop (𝓝 (P.price i)):=by
    let W:= P.steps i hl
    let Z:=W.terrace.back; let X:=P.state (i+1); let V:=P.state i
    have h':= W.birth; let B:=Y.marine i; have H₁:= (Y.boat i).applaud; let R':= H₁.rates
    let O₁:= H₁.near.keep R' X.spin; let O₂:= H₁.far.keep R' V.spin
    have hT := deed J J Z (W.terrace.avenue (X.quarry Y) (V.quarry Y) W.qual Q.lawful.flour) relic O₁.X O₁.Y O₂.X O₂.Y O₁.Z O₂.Z beacon R'.hr R'.hc R'.hs R'.hd R'.ht R'.fit Q.Z.width h'.limbs R'.hw R'.hl h'.price
    apply (hT.comp (tendsto_add_atTop_nat 5)).congr'; apply Eventually.of_forall; intro k
    have hx:(Smoke.localG Z (k+5)) = Y.ring (R.n k) (i+1):=by
      let F:= Y.sail X
      apply Subtype.ext; change ((T i).n (k+5)).val * (Y.length i).val=(Y.ring (R.n k) (i+1)).val
      rw [Y.next,hp.keeps i hl k]
    have hr: Z.chain.n (k+5)=Y.ring (R.n k) i:=hp.keeps i hl k
    change readP (rollG J X.wing X.spin.powerG (Smoke.localG Z (k+5))) relic-readP (rollG J (Y.sail X).land V.spin.powerG (Z.chain.n (k+5))) relic=_
    rw [hx,hr,show (Y.sail X).land=V.wing from W.lands]; exact rfl

lemma aloft (hk:i+k≤ n) : Tendsto (fun j=>P.price_R Y (R.n j) (i+k)- P.price_R Y (R.n j) i) atTop (𝓝 (registerG P.price (i+k)- registerG P.price i)):=by
    induction k with
    | zero=> simp
    | succ k ih=>
      have h:i+k<n:=by omega
      rw [← Nat.add_assoc,succeeding]; convert (ih h.le).add (ascending Y P R hp h) using 1; · ext; abel
      congr 1; ring
lemma full (hk:i ≤ k)(hn:k ≤ n): Tendsto (fun j=>P.price_R Y (R.n j) k-P.price_R Y (R.n j) i) atTop (𝓝 (registerG P.price k-registerG P.price i)):=by
    obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le hk; exact aloft Y P R hp hn
lemma account (hk:i≤ k)(hn:k≤ n): |registerG P.price k-registerG P.price i-Pearl.chargeF*(Y.measure k-Y.measure i)|≤ stamp J (Y.towns i)+ stamp J (Y.towns k):=by
    apply le_of_tendsto ((full Y P R hp hk hn).sub_const _ |>.abs)
    filter_upwards [price_bound Y P R i, price_bound Y P R k] with z hz hw
    refine le_trans (le_of_eq (show |P.price_R Y (R.n z) k-P.price_R Y (R.n z) i-_|=|(P.price_R Y (R.n z) k-Pearl.chargeF*(Real.log ((R.n z).val:ℝ)+Y.measure k))-(P.price_R Y (R.n z) i-Pearl.chargeF*(Real.log ((R.n z).val:ℝ)+Y.measure i))| from ?_)) ?_
    · ring_nf
    exact (abs_sub ..).trans ((add_le_add hw hz).trans_eq (add_comm ..))
omit hp in
lemma land (hk:i≤n): |registerG P.gauge i+su.slopeConstant*Y.measure i|≤ Q.D*i:=by
  induction i with
  | zero=> simp[Y.origin_cost]
  | succ i ih=>
      have h: i<n:= hk
      rw [succeeding,Y.era,mul_add]; have hh:=ih h.le
      have ht: |P.gauge i+su.slopeConstant*Real.log ((Y.length i).val:ℝ)| ≤ Q.D:=by
         have hx:= (P.steps i h).terrace.toll; simp_rw [sail,gears] at hx; linarith
      push_cast; rw [mul_add,mul_one,show registerG P.gauge i+_+(_+_)= registerG P.gauge i+su.slopeConstant* Y.measure i+(P.gauge i+su.slopeConstant* Real.log ((Y.length i).val:ℝ)) from (by ring)]
      exact (abs_add_le ..).trans (add_le_add hh ht)
omit hp in
def spin (F:ℕ)(i:ℕ):ℝ := P.gauge i+F*P.price i
lemma sum_toll (F:ℕ)(hn:i≤ n): |registerG (P.spin Y F) i+ betaQ F * Y.measure i|≤ Q.D*i+F*(stamp J (Y.towns 0)+stamp J (Y.towns i)):=by
    have he : |registerG P.price i - Pearl.chargeF*Y.measure i|≤ stamp J (Y.towns 0)+ stamp J (Y.towns i):=by simpa [Y.origin_cost] using (account Y P R hp (show 0 ≤ i from by omega) hn)
    have h : (registerG P.gauge i+su.slopeConstant*Y.measure i)+F*(registerG P.price i-Pearl.chargeF*Y.measure i)= registerG (P.spin Y F) i+betaQ F*Y.measure i:=by unfold registerG spin betaQ; rw [Finset.sum_add_distrib,← Finset.mul_sum]; ring
    rw [← h]; refine (abs_add_le ..).trans (add_le_add (land Y P hn) (?_)); rw [abs_mul, abs_of_nonneg (by positivity:(0:ℝ)≤F)]; exact mul_le_mul_of_nonneg_left he (by positivity)
end AtlasH.Survey
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.AtlasH.Survey.sum_toll
