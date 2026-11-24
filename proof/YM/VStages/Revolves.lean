import YM.VStages.Passage
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
 (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ
open Fog.Voyage
variable {P J} {d:ChangeQ→ℕ} (Y:Track P J p d)
namespace Track
lemma spacing_price : Tendsto (fun i=> (Y.spacing i).val) atTop atTop:=by
    simp_rw [spacing,Y.length_eq]; exact Y.openL
def den (Y:Track P J p d) : ℕ→Side
  | 0=>1
  | i+1=> Y.den i * (Y.spacing i)
abbrev ring (R:Side)(i:ℕ):= R*Y.den i
@[simp] lemma at_zero : Y.den 0=1:=rfl
theorem next (R:Side) (i:ℕ): (Y.ring R (i+1)).val=(Y.ring R i).val*(Y.spacing i).val:=by rw [ring,den,← mul_assoc,PNat.mul_coe]

def measure (i:ℕ):= Real.log ((Y.den i).val:ℝ)
abbrev scale (x:ℝ)(i:ℕ):= x+su.slopeConstant*Y.measure i
lemma origin_cost: Y.measure 0=0:=by simp[measure]
lemma era (i:ℕ): Y.measure (i+1)=Y.measure i+ Real.log ((Y.spacing i).val:ℝ):=by unfold measure; rw [den,PNat.mul_coe,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
lemma atBirth (x:ℝ): Y.scale x 0=x:=by simp[scale,Y.origin_cost]
lemma eras (x:ℝ) (i:ℕ):Y.scale x (i+1)= betaF su (Y.scale x i) (Y.spacing i):=by
   change _=_+_; unfold scale; rw [era]; ring
-- `x` + scale.clock
lemma bounded (i:ℕ):1≤(↑(Y.den i).val:ℝ):=by exact_mod_cast (Y.den i).pos
lemma per_len (i:ℕ):2 ≤(↑(Y.spacing i).val:ℝ):=by exact_mod_cast (show 2 ≤(Y.spacing i).val from (by have h:= (Y.flight i).coarse; exact (show 2≤3 from by decide).trans h))
lemma measure_nn (i:ℕ):0 ≤ Y.measure i :=Real.log_nonneg (Y.bounded i)
lemma measure_strict:StrictMono Y.measure:=strictMono_nat_of_lt_succ (fun i=>by rw [era]; exact lt_add_of_pos_right _ (Real.log_pos (by linarith [Y.per_len i])))
lemma measure_pos (i:ℕ)(he:0< i):0<Y.measure i:= by rw [←origin_cost Y]; exact measure_strict Y he
private lemma unbounded : Tendsto (fun i=>Real.log ((Y.spacing i).val:ℝ)) atTop atTop:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp Y.spacing_price)
lemma ample (A:ℝ):∃ b:ℝ,∀ i:ℕ,A*(i:ℝ) ≤Y.measure i+b:=by
  obtain ⟨n,h⟩:= eventually_atTop.mp (Y.unbounded.eventually_ge_atTop |A|)
  refine ⟨|A| *(n:ℝ), fun i=>?_⟩
  have ht:= le_abs_self A
  induction i with
  | zero=> rw [Nat.cast_zero,Y.origin_cost,mul_zero]; positivity
  | succ i ih=>
      by_cases hh:n≤ i
      · rw [Nat.cast_add,Nat.cast_one,era]; linarith [h i hh]
      have hi:i+1 ≤ n:= lt_of_not_ge hh
      have hp: (↑(i+1):ℝ) ≤ (n:ℝ) := by exact_mod_cast hi
      exact (mul_le_mul ht hp (by positivity) (abs_nonneg _)).trans (le_add_of_nonneg_left (Y.measure_nn _))
lemma funds (A B:ℝ):∀ᶠ i:ℕ in atTop, A+B*(i:ℝ)≤Y.measure i:=by
  obtain ⟨b,h⟩:= ample Y (B+1); filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (A+b)] with i hi; linarith [h i]
lemma long : Tendsto Y.measure atTop atTop:=tendsto_atTop.2 fun A=> by simpa using Y.funds A 0
lemma outlay (A B:ℝ)(v:ℝ)(hv:0<v): ∀ᶠ i:ℕ in atTop,A+B*(i:ℝ)≤v*Y.measure i:=by
   filter_upwards [Y.funds (A/v) (B/v)] with i hi; apply (div_le_iff₀ hv).1 ?_ |>.trans_eq (mul_comm ..)
   rw [add_div,mul_div_right_comm]; exact hi
lemma freedom (A B:ℝ)(v:ℝ)(hv:0<v):∀ᶠ x:ℝ in atTop,∀ i:ℕ,A+B*(i:ℝ) ≤ x +v*Y.measure i:=by
  obtain ⟨b,h⟩:=ample Y (B/v);
  filter_upwards [eventually_ge_atTop (v*b+A)] with x hx i
  have hl:B*(i:ℝ) ≤(Y.measure i+b)*v:= ((div_le_iff₀ hv).1 (by rw [mul_div_right_comm]; exact h i))
  linarith
-- relative startup fee with any stride-dependent offset (eg $δ_G(L)$) can be requested at setup.
lemma funded (A B:ℝ):∀ᶠ x in atTop,∀ i:ℕ,A+B*(i:ℝ) ≤ Y.scale x i:= freedom Y A B _ (Gauge.slopeConstant_pos simple)
-- currencies Survey coherence.
structure Align (Y:Track P J p d)(B:SparkMesh)(S:ℕ→SparkMesh)(n:ℕ):Prop where
  keeps i : i<n →∀ k, (S i).n (k+5)=Y.ring (B.n k) i
lemma ringing (B:SparkMesh)(i:ℕ):Tendsto (fun k=>Y.ring (B.n k) i) atTop atTop:=by
   refine tendsto_atTop.2 fun t=>?_ ;filter_upwards [(B.cofinal.eventually_ge_atTop t.val)] with k hk; exact hk.trans (show (B.n k).val ≤ (Y.ring (B.n k) i).val from Nat.le_mul_of_pos_right _ (Y.den i).pos)
lemma sums_log (B:Side)(i:ℕ):Real.log ((Y.ring B i).val:ℝ)=Real.log (B.val:ℝ)+ Y.measure i:=by
   change Real.log ((↑(B.val*(Y.den i).val)):ℝ)= _; rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]; rfl

abbrev expenses (i):= stamp (J (Y.level i)) (Y.town i)
namespace Survey
variable {T:ℕ→SparkMesh}
variable (V:Survey Y T n) {R:SparkMesh}

def price_R (x:Side)(i:ℕ): ℝ:= let A:= V.state i;
    readP (rollG (J (Y.level i)) A.wing A.sun.powerG (Y.ring x i)) relic
variable (R)
lemma price_bound (i:ℕ): ∀ᶠ k in atTop, |V.price_R Y (R.n k) i-Pearl.chargeF*(Real.log ((R.n k).val:ℝ)+ Y.measure i)| ≤ expenses Y (i):=by
  let W:= (Y.town i).1
  have h:= Classical.choose_spec (Raft.calibrated (J (Y.level i)) relic beacon W.1.1.live W.1.2.live W.1.1.bill W.1.2.bill)
  filter_upwards [(ringing Y R i).eventually h] with k hi
  let he:= (V.state i).sun; rw [← sums_log]; exact (hi he.X he.Y (V.state i).wing).trans (le_abs_self _)

variable (hp:Align Y R T n)
include hp
lemma ascending (hl:i < n): Tendsto (fun k=> V.price_R Y (R.n k) (i+1)-V.price_R Y (R.n k) i) atTop (𝓝 (V.spin i)):=by
    let W:= V.steps i hl
    let Z:=W.terrace.back; let X:=V.state (i+1); let E:=V.state i
    have h':= W.birth; let B:=(Y.beam i).fare; have H₁:= (Y.ticket i).applause; let R':= H₁.rates
    let O₁:= H₁.near.keep R' X.sun; let O₂:= H₁.far.keep R' E.sun
    have hT := deed (J (Y.level (i+1))) (J (Y.level i)) Z (W.terrace.avenue W.throughoutIn W.throughoutOut W.delta (P.retail _).growth (rank_ge (Y.level i))) relic O₁.X O₁.Y O₂.X O₂.Y O₁.Z O₂.Z beacon R'.hr R'.hc R'.hs R'.hd R'.ht R'.fit (P.retail _).pos h'.limbs R'.hw R'.hl h'.price
    apply (hT.comp (tendsto_add_atTop_nat 5)).congr'; apply Eventually.of_forall; intro k
    have hx:(Smoke.localG Z (k+5)) = Y.ring (R.n k) (i+1):=by
      let F:= Y.sail X
      apply Subtype.ext; change ((T i).n (k+5)).val * (Y.spacing i).val=(Y.ring (R.n k) (i+1)).val
      rw [Y.next,hp.keeps i hl k]
    have hr: Z.chain.n (k+5)=Y.ring (R.n k) i:=hp.keeps i hl k
    change readP (rollG (J (Y.level (i+1))) X.wing X.sun.powerG (Smoke.localG Z (k+5))) relic-readP (rollG (J (Y.level i)) (Y.sail X).land E.sun.powerG (Z.chain.n (k+5))) relic=_
    rw [hx,hr,show (Y.sail X).land=E.wing from W.landed]; exact rfl

lemma aloft (hk:i+k≤ n) : Tendsto (fun j=>V.price_R Y (R.n j) (i+k)- V.price_R Y (R.n j) i) atTop (𝓝 (registerG V.spin (i+k)- registerG V.spin i)):=by
    induction k with
    | zero=> simp
    | succ k ih=>
      have h:i+k<n:=by omega
      rw [← Nat.add_assoc,succeeding]; convert (ih h.le).add (ascending Y V R hp h) using 1; · ext; abel
      congr 1; ring
lemma full (hk:i ≤ k)(hn:k ≤ n): Tendsto (fun j=>V.price_R Y (R.n j) k-V.price_R Y (R.n j) i) atTop (𝓝 (registerG V.spin k-registerG V.spin i)):=by
    obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le hk; exact aloft Y V R hp hn
lemma account (hk:i≤ k)(hn:k≤ n): |registerG V.spin k-registerG V.spin i-Pearl.chargeF*(Y.measure k-Y.measure i)|≤ expenses Y (i)+ expenses Y (k):=by
    apply le_of_tendsto ((full Y V R hp hk hn).sub_const _ |>.abs)
    filter_upwards [price_bound Y V R i, price_bound Y V R k] with z hz hw
    refine le_trans (le_of_eq (show |V.price_R Y (R.n z) k-V.price_R Y (R.n z) i-_|=|(V.price_R Y (R.n z) k-Pearl.chargeF*(Real.log ((R.n z).val:ℝ)+Y.measure k))-(V.price_R Y (R.n z) i-Pearl.chargeF*(Real.log ((R.n z).val:ℝ)+Y.measure i))| from ?_)) ?_
    · ring_nf
    exact (abs_sub ..).trans ((add_le_add hw hz).trans_eq (add_comm ..))

omit hp in
lemma land (hk:i≤n): |registerG V.gauge i+su.slopeConstant*Y.measure i|≤ registerG (fun i=>P.slope (Y.node i)) i:=by
  induction i with
  | zero=> simp[Y.origin_cost]
  | succ i ih=>
      have h: i<n:= hk
      rw [succeeding,Y.era,mul_add,succeeding]; have hh:=ih h.le
      have ht: |V.gauge i+su.slopeConstant*Real.log ((Y.spacing i).val:ℝ)| ≤ P.slope (Y.node i):=by
         have hx:= (V.steps i h).terrace.toll; exact (le_add_of_nonneg_right zero_le_one).trans hx
      rw [show registerG V.gauge i+_+(_+_)= registerG V.gauge i+su.slopeConstant* Y.measure i+(V.gauge i+su.slopeConstant* Real.log ((Y.spacing i).val:ℝ)) from (by ring)]
      exact (abs_add_le ..).trans (add_le_add hh ht)
omit hp in
def delta (F:ℕ)(i:ℕ):ℝ := V.gauge i+F*V.spin i
lemma sum_toll (F:ℕ)(hn:i≤ n): |registerG (V.delta Y F) i+ betaQ F * Y.measure i|≤ registerG (fun j=>P.slope (Y.node j)) i+F*(expenses Y 0+ expenses Y i):=by
    have he : |registerG V.spin i - Pearl.chargeF*Y.measure i|≤ expenses Y 0+ expenses Y i:=by simpa [Y.origin_cost] using account Y V R hp (show 0 ≤ i from by omega) hn
    have h : (registerG V.gauge i+su.slopeConstant*Y.measure i)+F*(registerG V.spin i-Pearl.chargeF*Y.measure i)= registerG (V.delta Y F) i+betaQ F*Y.measure i:=by unfold registerG delta betaQ; rw [Finset.sum_add_distrib,← Finset.mul_sum]; ring
    rw [← h]; refine (abs_add_le ..).trans (add_le_add (land Y V hn) (?_)); rw [abs_mul, abs_of_nonneg (by positivity:(0:ℝ)≤F)]; exact mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
end Survey
end Track
end YM.QCD.Acre.Stratum.MarchQ
