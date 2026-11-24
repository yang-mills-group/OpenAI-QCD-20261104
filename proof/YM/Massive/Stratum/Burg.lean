import YM.Massive.Stratum.Velour
/-!
# Permissions for tuning a trajectory

Bills before large reference inverse-coupling is specified. `slope_all` applies
at every intermediate stop, including visits by *later cutoffs*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores Revolve Rudder Eyrie
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {j n i k:ℕ}{Q:Rock j}{J:Plan j}{p:ChartRatio su} (Y:AtlasH Q J p)
local notation "Qq" => Q.Z.top.clip
local notation "Kq" => Q.Z.bind
local notation "u₀" => Q.Z.top.width
open AtlasH
open Fog.Voyage
variable {F:ℕ} (H₀: su.slopeConstant / 2 < betaQ F)

-- Can insist on this in planning the schedule, and any post-step fixed costs.
def Paid (A:ℝ):Prop:=∀ i, stamp J (Y.towns i) ≤ (i:ℝ)+A
abbrev Vacancy (j:ℕ):= Flight j j→Town→Town→ℝ→ℝ→ParcelR→ℝ
def priorH (f:Vacancy j) (A:ℝ): Prop:=∀ i:ℕ, f (Y.path i) (Y.towns (i+1)) (Y.towns i) (Y.gap i) (Y.cost i) (Y.marine i) ≤ (i:ℝ)+A
theorem well (K':ℕ)(Q:Rock j)(J: Plan j)(p: ChartRatio su) (hj:4≤j)(hp:LocalRatio p)(hw:∀ E:Patch,E.Branches Q.Z.bind su) (f:Vacancy j):∃ Y:AtlasH Q J p,∃ A:ℝ,(∀ i,K' ≤ (Y.length i).val) ∧ Paid Y A ∧ priorH Y f A:=by
    -- local notation Kq shadow
    obtain ⟨Y,B,H⟩:= atlasH Q J p K' hj hp hw (fun S X Y a b Ω=> max (stamp J Y) (f S X Y a b Ω)); exact ⟨Y,(B:ℝ),fun i=>(H i).1,fun i=>(max_le_iff.mp (H i).2).1,fun i=>(max_le_iff.mp (H i).2).2⟩
lemma scheduled (f:Vacancy j)(A:ℝ)(h: priorH Y f A):∀ᶠ x:ℝ in atTop,∀ i:ℕ,f (Y.path i) (Y.towns (i+1)) (Y.towns i) (Y.gap i) (Y.cost i) (Y.marine i) ≤ Y.scale x i:=by
   filter_upwards [Y.funded A 1] with x hx i; exact (h i).trans (by linarith only [hx i])
variable {T:ℕ→SparkMesh}{A x v:ℝ}
-- On the center of *this trajectory*, including its coupling offsets!
abbrev central (x:ℝ)(X:ℕ→ℝ)(i:ℕ):=x-registerG X i
abbrev costZone (x:ℝ)(i:ℕ)(p:ℝ):Prop := Y.scale x i/2 ≤ p ∧ p ≤2*Y.scale x i
abbrev height_R (i:ℕ):ℝ := (i:ℝ)*3+1
lemma zen (i:ℕ):0<height_R i:=by unfold height_R; positivity

section accounts
variable (h:Paid Y A)
include h
namespace SurveyT
abbrev hub (P:Survey Y T n) (x:ℝ)(F i:ℕ)(p:ℝ) :Prop := |p - central x (P.spin Y F) i| ≤ height_R i
lemma checks (P:Survey Y T n) (R:SparkMesh) (hp:Align Y R T n)(hn:i≤ n)(hb:hub Y P x F i v):
    |v-(x + betaQ F * Y.measure i)| ≤ (3+(F:ℝ)+Q.D)*i + (1+F*(A+A)) :=by
    let f:=P.spin Y F; have he:= P.sum_toll Y R hp F hn
    -- accounts bound using both endpoints
    apply le_trans (b:=height_R i+(Q.D*i+F*(stamp J (Y.towns 0)+ stamp J (Y.towns i))))
    · rw [show v-(x+_)= (v-central x f i)-(registerG f i+betaQ F*Y.measure i) from (by unfold central; ring)]
      exact (abs_sub ..).trans (add_le_add hb he)
    have hv:=h 0; simp only [Nat.cast_zero,zero_add] at hv
    unfold height_R; linarith only [mul_le_mul_of_nonneg_left (add_le_add hv (h i)) (by positivity:(0:ℝ)≤F)]
include H₀
lemma perimeter :∀ᶠ x:ℝ in atTop,∀ (n:ℕ)(S:ℕ→SparkMesh)(P: Survey Y S n) (R:SparkMesh), Align Y R S n →∀ i≤ n,∀ p:ℝ,hub Y P x F i p → costZone Y x i p:=by
  let t:=su.slopeConstant; let r:=betaQ F; let z:=2*(r-t/2); have hz:0<z:=mul_pos (by norm_num) (sub_pos.mpr H₀)
  have ht:0≤ t:=(Gauge.slopeConstant_pos simple).le
  let k:ℝ:=1+F*(A+A); let d:ℝ:=3+F+Q.D; have hh:r≤t:=sub_le_self _ (mul_nonneg (by positivity:(0:ℝ)≤F) (by unfold Pearl.chargeF; positivity))
  filter_upwards [Y.freedom (2*k) (2*d) z hz, eventually_ge_atTop (0:ℝ)] with x hx hx' n S P R hp i hi v hv
  obtain ⟨h1,h2⟩:= abs_le.mp (checks Y h P R hp hi hv); have H:=hx i
  have he : d*i+k ≤ x/2+(r-t/2)*Y.measure i:=by unfold z at H; linarith only [H];
  change -(d*_+k) ≤ v-(x+r*_) at h1; change v-(x+r*_) ≤ d*_+k at h2
  unfold costZone scale; change (x+t*_)/2≤v ∧ v≤2*(x+t*_); constructor
  · linarith only [h1,he]
  linarith only [h2,he,mul_le_mul_of_nonneg_right hh (Y.measure_nn i),mul_nonneg ht (Y.measure_nn i),hx']
omit H₀ in
theorem slope_all (x ε:ℝ)(he:0<ε)(F:ℕ): ∀ᶠ i:ℕ in atTop,∀ (n:ℕ)(S:ℕ→SparkMesh)(P:Survey Y S n)(R:SparkMesh)(p:ℝ), i ≤ n → Align Y R S n → hub Y P x F i p → |p/Y.measure i-betaQ F| ≤ ε:=by
   let w:=Y.measure; let b:=betaQ F; let k:ℝ:=1+F*(A+A); let d:ℝ:=3+F+Q.D
   filter_upwards [Y.outlay (k+|x|) d ε he, eventually_gt_atTop (0:ℕ)] with i hM hi n S P R p hn hp hV
   obtain ⟨h1,h2⟩:= abs_le.mp (checks Y h P R hp hn hV); have hv:=Y.measure_pos i hi; apply abs_le.mpr
   constructor
   · apply le_sub_iff_add_le.mpr; apply (le_div_iff₀ hv).mpr; change k+_+d*i≤ _ at hM; unfold d k at hM
     linarith only [hM,h1,(neg_abs_le x)]
   apply sub_le_iff_le_add.mpr; apply (div_le_iff₀ hv).mpr; unfold d k at hM; linarith only [hM,le_abs_self x,h2]
end SurveyT
end accounts
lemma payments (P:Survey Y T n) (X:ℕ→ℝ)(h: X 0=x)(he:∀ k< i,|X k-X (k+1)-P.spin Y F k| ≤ 2) : SurveyT.hub Y P x F i (X i):=by
   induction i with
   | zero=> simp [SurveyT.hub,h,central,height_R]
   | succ i ih=>
       have hx:= he i (by omega); obtain ⟨h₁,h₂⟩:= abs_le.mp hx
       obtain ⟨h₃,h₄⟩:= abs_le.mp (ih (fun k hk=> he k (by omega))); unfold SurveyT.hub central height_R; rw [succeeding]; unfold height_R central at h₃ h₄; push_cast; apply abs_le.mpr; constructor <;> linarith only [h₁,h₂,h₃,h₄]
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.SurveyT.slope_all
#print axioms YM.QCD.Acre.Stratum.SurveyT.perimeter
