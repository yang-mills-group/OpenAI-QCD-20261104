import YM.Bard.Plaza
import YM.Profiles.Counts
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
open Track Depot
namespace MintV
variable (Z:Borough P₀ gate) (f:Tag P J (fun b=>(P₀ b).guide.table)→ℕ)(pad:ℕ→ℕ→ℕ)(j:ℕ)
local notation "x₁"=> Z.fixed j
local notation "T"=> Z.track f pad
local notation "b"=> Z.starts f pad j
lemma node_lead (hp: Z.Lead f pad j i): (T).beam i=Z.fixed j := Z.at_lead f pad hp
lemma node_age (hp: Z.Lead f pad j i) : (T).node i=(x₁).node:= ((T).node_at _).symm.trans (congr_arg _ (node_lead P₀ Z f pad j hp))
lemma spacing_lead (hp: Z.Lead f pad j i) : (T).spacing i=(x₁).L:= ((T).length_eq i).trans (congr_arg _ (node_lead P₀ Z f pad j hp))
lemma dayLead (hp:Z.Lead f pad j i): HEq ((T).flight i) (x₁).flight:=by
    have h (d e:Tag P J (fun r=>(P₀ r).guide.table))(ht:d=e):HEq d.flight e.flight:=by subst e; exact HEq.rfl
    exact HEq.trans ((T).flight_eq i) (h _ _ (node_lead P₀ Z f pad j hp))
lemma statusLead (hp:Z.Lead f pad j i):stanceQ P₀ T i=ceilingL (x₁).fromX (x₁).toX:=by
    unfold stanceQ; rw [← show ((T).beam i).fromX=(T).town (i+1) from ((T).nexts i).2.1]; unfold Track.town; rw [node_lead P₀ Z f pad j hp]
lemma keeper (M:Muster tol P₀ gate) (hp:Z.Lead f pad j i):HEq (M (Z.fixed j) (Z.resource j)) (M.patchV tol P₀ gate T i) :=by
   have h (c d:Tag P J (fun r=>(P₀ r).guide.table))(ht:gate c.node ≤ c.L.val)(hv:gate d.node ≤ d.L.val)(hh:c=d):HEq (M c ht) (M d hv):=by subst c; exact HEq.rfl
   exact HEq.trans (h _ _ _ _ (node_lead P₀ Z f pad j hp|>.symm)) (M.heartsV ..)
lemma oldest (k:ℕ): (A.den k).val ≤ (A.spacing k).val^k:=by
   have hi:Monotone (fun k=> (A.spacing k).val):=monotone_nat_of_le_succ fun i=>by simp_rw [Track.spacing,A.length_eq]; exact (A.nexts i).2.2.1
   induction k with
   | zero => simp [Track.den]
   | succ k ih=> rw [Track.den,PNat.mul_coe,pow_succ]; have h:=hi (show k≤k+1 by omega); exact Nat.mul_le_mul (ih.trans (Nat.pow_le_pow_left h k)) h
lemma stampLead (hp:Z.Lead f pad j i)(h:i≤k)(hz:k≤Z.rear f pad j): Counter.stampR P₀ T i k=(x₁).L.val^(k-i):=by
    induction h with
    | refl => rw [Counter.stampR,Nat.sub_self,pow_zero,Nat.div_self ((T).den _).pos]
    | @step k hv ih=>
        have hl:i≤ k:= hv; have hw:k.succ-i=(k-i)+1:=by omega
        rw [Counter.stamp_t P₀ T hl,ih (show k ≤_ from le_trans (by omega :k≤k+1) hz),hw,pow_succ,spacing_lead P₀ Z f pad j (show Z.Lead f pad j k from ⟨hp.1.trans hl,hz⟩)]
lemma den_lead (hp: Z.Lead f pad j (b+i)) : ((T).den (b+i)).val=((T).den b).val*(x₁).L.val^i:=by
   have hb:Z.Lead f pad j b:=⟨le_rfl,(Z.adj f pad j).1⟩; rw [Counter.stamps P₀ T (show b ≤ b+i from by omega),stampLead P₀ Z f pad j hb (Nat.le_add_right ..) hp.2.le]; simp
lemma meter_lead (hp: Z.Lead f pad j (b+i)) : (T).measure (b+i)=(T).measure b + i*Real.log ((x₁).L.val:ℝ):=by simp only [Track.measure,den_lead P₀ Z f pad j hp,Nat.cast_mul,Nat.cast_pow, Real.log_mul (show (↑((T).den b).val:ℝ)≠0 by positivity) (show ((↑(x₁).L.val:ℝ)^i)≠0 by positivity), Real.log_pow];
def riseV (X:Side)(s:ℝ)(i:ℕ):ℝ:= s+i*(su.slopeConstant * Real.log (X.val:ℝ))
lemma aheadV (X:Side)(h: 1 < X.val)(s:ℝ): Tendsto (riseV X s) atTop atTop:= tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos (Gauge.slopeConstant_pos simple) (Real.log_pos (by exact_mod_cast h))))
lemma risingV (s:ℝ)(hp:Z.Lead f pad j (b+i)): clockQ P₀ T s (b+i)=riseV (x₁).L (clockQ P₀ T s b) i:=by
   have hB : Z.Lead f pad j b:=⟨le_rfl,(Z.adj f pad j).1⟩; unfold clockQ; rw [spacing_lead P₀ Z f pad j hp, spacing_lead P₀ Z f pad j hB]; unfold Track.scale; rw [meter_lead P₀ Z f pad j hp]; unfold Spire.Client.fallback riseV; ring
lemma ridgeV (s:ℝ)(hp:Z.Lead f pad j i) (ho:Z.Lead f pad j (i+k)): clockQ P₀ T s (i+k)= riseV (x₁).L (clockQ P₀ T s i) k:=by
   obtain ⟨l,hl⟩:= Nat.exists_eq_add_of_le hp.1; subst i; rw [Nat.add_assoc] at ho ⊢; rw [risingV P₀ Z f pad j s hp, risingV P₀ Z f pad j s ho]; unfold riseV; push_cast; ring
-- observation requests any room & time delays, purchase simultaneous after reference. No uniformity as j varies.
variable (U:ℕ→ℝ→ℕ)(C:ℕ→ℝ→Prop)(hx:∀ j,∀ᶠ s:ℝ in atTop,C j s)
include hx
lemma rehearsalV (s:ℝ):∃ pad:ℕ→ℕ→ℕ,∀ j, ∃ i,C j (clockQ P₀ (Z.track f pad) s i) ∧ i≥Z.starts f pad j ∧ ∀ k:ℕ,k ≤ U j (clockQ P₀ (Z.track f pad) s i)→ Z.Lead f pad j (i+k):=by
   let B(j n:ℕ):=(Z.fixed j).L.val^n
   let r(j d:ℕ):= fallback (Z.fixed j).L (s+su.slopeConstant*Real.log (d:ℝ))
   let R(j d:ℕ):= riseV (Z.fixed j).L (r j d)
   have ht(j):1 < (Z.fixed j).L.val:= lt_of_lt_of_le (by omega :1<3) (Z.fixed j).flight.coarse
   choose a ha using fun j d=> ((aheadV _ (ht j) (r j d)).eventually (hx j)).exists
   let pad j n:= (Finset.range (B j n+1)).sup (fun d=> a j d + U j (R j d (a j d)))
   refine ⟨pad,fun j=>?_⟩; let k:= Z.starts f pad j; let A:= Z.track f pad; let X:=(A.den k).val; let v:=a j X
   have hd:X ≤ B j k:= (oldest P₀ A k).trans_eq (congr_arg (fun x:Side=> x.val^k) (spacing_lead P₀ Z f pad j (show Z.Lead f pad j k from ⟨le_rfl,(Z.adj f pad j).1⟩)))
   let C':=U j (R j X v); have hR:v+C' ≤ pad j k:= Finset.le_sup (f:=fun d=> a j d+U j (R j d (a j d))) (Finset.mem_range.mpr (show X < B j k+1 by omega))
   have hU(i:ℕ)(hi:i≤ C') : Z.Lead f pad j (k+v+i) :=by
        refine ⟨show k ≤ k+v+i from by omega, show k+v+i<_ from ?_⟩; unfold Depot.rear; change _<k+Z.Needs f j+pad j k+1; omega
   have hk: clockQ P₀ A s k=r j X:=congr_arg (fun z:Side=>fallback z _) (spacing_lead P₀ Z f pad j (show Z.Lead f pad j k from ⟨le_rfl,(Z.adj f pad j).1⟩))
   have hp: clockQ P₀ A s (k+v) =R j X v:= (risingV P₀ Z f pad j s (by simpa only [Nat.add_zero] using hU 0 (Nat.zero_le _))).trans (congr_arg (fun x=>riseV _ x v) hk)
   refine ⟨k+v,hp.symm ▸ ha j X,Nat.le_add_right ..,fun i hi=> hU i (show i ≤ C' from ?_)⟩
   change i ≤ U j (clockQ P₀ A s (k+v)) at hi; rw [hp] at hi; exact hi
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.dayLead
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.keeper
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.rehearsalV
