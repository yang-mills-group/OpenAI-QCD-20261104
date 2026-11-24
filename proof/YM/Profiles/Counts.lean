import YM.Profiles.Bursary
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
-- elementary numerical gear for all expiry & pack. enters after.L before pad. pressure clocks.
variable (L:Side)(u:ℝ)
def dialQ (L:Side)(x:ℝ):= radiusB (run L x)
-- square maturity.Quicken.Sort
structure Cave (L:Side)(x θ:ℝ) : Prop where
  budget : 32 ≤ radiusB (run L x)
  high : 2 ≤ run L x
  later : (radiusB (run L (run L x)))^2 ≤ 2*(radiusB (run L x))^2
  takes : radiusB (run L x) ≤ radiusB (run L (run L x))
  shape : 0 < MassiveQCD.Sample.Sail.roomAt L θ x ∧ MassiveQCD.Sample.Sail.roomAt L θ x≤ 1 ∧ (MassiveQCD.Sample.Sail.roomAt L θ x)⁻¹ ≤ (betaF su x L)^ (2:ℝ)
lemma cave (θ:ℝ):∀ᶠ x in atTop,Cave L x θ:=by
    let Z:= MassiveQCD.Sample.Sail.roomAt L θ; have hZ:= MassiveQCD.Sample.Sail.slotR L θ; have he :Tendsto (run L) atTop atTop:= betaF_growth su L; filter_upwards [(Work.E01.radiusB_tendsto.comp he).eventually_ge_atTop 32, he.eventually_ge_atTop 2, he.eventually (Stock.stepsize (su.slopeConstant*Real.log (L.val:ℝ))),MassiveQCD.Sample.Sail.shuttle L θ, hZ.below (by norm_num) 1 zero_lt_one,(MassiveQCD.Sample.Sail.inverseSlot L θ) 2 (by norm_num)] with x h1 h2 h3 h4 h5 h6; refine ⟨h1,h2,h3,?_,h4.1,(le_abs_self _).trans h5,(le_abs_self _).trans h6⟩
    unfold radiusB; have hQ : 0 < run L x:=lt_of_lt_of_le (by norm_num) h2; exact Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_nonneg (le_trans (by norm_num) h2)) (Real.log_le_log hQ (show run L x≤ run L (run L x) from le_add_of_nonneg_right (Work.E04.shift_nonneg su L))) _)
variable (hX:∀ i:ℕ,Cave (A.spacing i) (clockQ P₀ A x i) θ)
local notation "Ψ" i=> A.scale x i
local notation "B" t=>radiusB (A.scale x t)
local notation "G" t=>A.spacing t
local notation "Δ" i=> A.measure i
-- Den ratio.TrSpan.Spikes. width traveling. minimum.Result `stages cover margin`. allowances η. L inline even Chakra. 
noncomputable def stampR (i j:ℕ):ℕ:= (A.den j).val/(A.den i).val
lemma stamps (hi:i≤j): ((A.den j).val)= (A.den i).val*stampR P₀ A i j:=by
    induction hi with
    | refl=>simp [stampR]
    | @step j hj ih=>
       unfold stampR; have hv:(A.den (j+1)).val=(A.den j).val*(A.spacing j).val:=by rw [Track.den,PNat.mul_coe]
       rw [hv,ih,Nat.mul_assoc]; exact congr_arg _ (Nat.mul_div_right _ (A.den i).pos).symm
lemma stamp_g (hi:i≤j): 0<stampR P₀ A i j:=by apply pos_of_ne_zero; intro h; have hp:= stamps P₀ A hi; rw [h,mul_zero] at hp; exact (A.den j).property.ne' hp
lemma stamp_t (hi:i≤j): stampR P₀ A i (j+1)= stampR P₀ A i j * (A.spacing j).val:=by
     unfold stampR; have hv:(A.den (j+1)).val=(A.den j).val*(A.spacing j).val:=by rw [Track.den,PNat.mul_coe]
     let s:= stampR P₀ A i j; let L:=(A.spacing j).val
     change _= s * L; rw [hv,stamps P₀ A hi, Nat.mul_assoc]; first | exact congr_arg _ (Nat.mul_div_right _ (A.den i).pos).symm | exact Nat.mul_div_right _ (A.den i).pos -- care rw stampR rec right reintroduced s
include hX
lemma evolves (i:ℕ) : ((B (i+1))^2) ≤2* (B i)^2 ∧ (B i) ≤ (B (i+1)):=by
   have hv := hX i; rw [← augmented P₀ A i x,A.eras,←augmented P₀ A i x]; exact ⟨hv.later,hv.takes⟩ -- argument order era. 
local notation "St"=> stampR P₀ A
-- construct minimal horizon maturity for arbitrary G.N
lemma rises (j M:ℕ) : ∃ m, j≤ m ∧ M*(B m)^2 ≤ St j m:=by
    let x' q := M*(B q)^2; -- X ratio Bun.L.Linear.P.
    let G' (i:ℕ):ℝ:= stampR P₀ A j (j+i)
    let P(i:ℕ):ℝ:=(x' (j+i):ℝ); have h(i:ℕ) : P (i+1) ≤2*P i∧ 3* G' i ≤ G' (i+1):=by
       have hz:= (evolves P₀ A hX (j+i)).1; have hL:= (A.flight (j+i)).coarse; unfold P G'; rw [← Nat.add_assoc,stamp_t P₀ A (by omega)]; constructor; exact_mod_cast (show x' _≤ _ from (mul_le_mul_left' hz M|>.trans_eq (by unfold x'; ring))); push_cast; unfold Track.spacing; exact mul_comm (3:ℝ) _ ▸ (mul_le_mul_of_nonneg_left (by exact_mod_cast hL) (by positivity)) -- rewrite mul_le_mul_right' argument order
    have h₀ : 0<G' 0:= by unfold G'; exact_mod_cast stamp_g P₀ A (show j≤j+0 by omega)
    have hf(i): P i / G' i ≤ (P 0/G' 0)*(2/3:ℝ)^i:=by
       induction i with
       | zero=>simp
       | succ i ih=>
          have he :0 < G' i:=by unfold G'; exact_mod_cast stamp_g P₀ A (show j ≤j+i by omega)
          rw [pow_succ, ← mul_assoc]; apply le_trans _ (mul_le_mul_of_nonneg_right ih (by norm_num : (0:ℝ)≤2/3)); refine le_trans ((div_le_div₀ (mul_nonneg (by norm_num) (show 0≤P i from Nat.cast_nonneg _)) (h i).1 (by positivity) (h i).2)) (le_of_eq ?_); ring
    obtain ⟨i,hi⟩:=(((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num: (0:ℝ)≤2/3) (by norm_num)).const_mul (P 0 /G' 0)).eventually_le_const (show P 0/G' 0 *0 <1 by rw [mul_zero]; norm_num)).exists
    refine ⟨j+i,by omega,?_⟩; have hP:0 < G' i:=by unfold G'; exact_mod_cast stamp_g P₀ A (show j ≤ j+i by omega)
    change x' _≤_; exact (Nat.cast_le (α:=ℝ)).mp ((div_le_one hP).1 ((hf i).trans hi))
open Rails.Reference.Sharp
lemma post (p i:ℕ) (h:i= Nat.find (rises P₀ A hX j p)): j≤ i ∧ p*(B i)^2 ≤ St j i ∧ St j i ≤ Rapture.packN (G i) (clockQ P₀ A x i) p:=by
    let z:=rises P₀ A hX j p; have hx:j ≤ i∧ p*(B i)^2 ≤ St j i:= h.symm ▸ Nat.find_spec z
    refine ⟨hx.1,hx.2,?_⟩; by_cases he:i=j; · rw [he,show St j j=1 from Nat.div_self (A.den j).pos]; unfold Rapture.packN; omega
    obtain _|i:=i; omega
    have hk:j≤ i:=by omega
    have hr: stampR P₀ A j i < p * (B i)^2:=lt_of_not_ge fun hv=> by have hT:= Nat.find_min' z ⟨hk,hv⟩; rw [← h] at hT; omega
    have hu:(G i).val ≤ (G (i+1)).val:=by simp_rw [Track.spacing,A.length_eq]; exact (A.nexts i).2.2.1
    unfold Rapture.packN; rw [stamp_t P₀ A hk, Suburb.augmented]; apply (mul_le_mul (hr.le.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.zero_le _) (evolves P₀ A hX i|>.2) _) (Nat.zero_le _))) hu (Nat.zero_le _) (Nat.zero_le _)).trans; rw [mul_right_comm]; omega -- syntax
end Counter
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Counter.post
