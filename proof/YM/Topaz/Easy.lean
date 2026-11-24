import YM.Topaz.Meter
import YM.Intag.Frost
import YM.Intag.Crown
import YM.Talis.Palm
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
namespace Sapphire
open Talis
open Talis Suburb.Melt Melt.Lobby LeaseV MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
-- geometry issuance independent of lengths; U any.F.Check positions.Pay margin in sectors all even. Canonical.Resource. use boosted Price argument for EP at terminal ℓ. `joins:` uptime ≥2XBT in denom given ratio at vT even if bookB pitch m.Quantity. Unit slots.
variable {D:ℕ}(X:Dial D)
open Dial YM.Bloom.TreeP
variable (U M:ℕ)(ε Y:ℝ)
local notation "tΓ"=> distV L X.ν
-- hPS=M proportional holder constant. must grow w Era root.J.L+D.LA.Checks.
structure EaseB (z:ℝ):Prop where
     guardT:∀ u≤ distV L (X.ν+1) z,highR L (riseV L z u) ≤paceN L 3 z
     grace : U*(M+202+paceN L 3 z*paceN L 3 z+1) ≤ paceN L 4 z
     mercy : 2*M < L.val^(bookB L X.ν X.H X.e z)
     tall :4*M < ε*(measureV L X.ν z)^(2*X.H)
     rail :Y≤ measureV L X.βA z
private lemma heavyB (hL:1<L.val):∀ᶠ z in atTop, 2*M < L.val^(bookB L X.ν X.H X.e z):=by
       -- bookB ≥ distV L ν, eventually. hE=X.pace.
       let B z:=L.val^(bookB L X.ν X.H X.e z); have he:0 < X.H:= X.height; have hK:X.e < X.ν:=by have h:=X.pace; omega
       filter_upwards [(tonicV L hL (show 0<X.ν from by omega)).eventually_gt_atTop (↑(2*M):ℝ),cliff L hK] with x hx hv
       have ht: tΓ x ≤ bookB L X.ν X.H X.e x:=by unfold bookB Jc; change _ ≤ tΓ x*(2*X.H)-_ ; have hh:tΓ x+tΓ x ≤ tΓ x*(2*X.H):=(Eq.trans_le (by exact (mul_two _).symm) (Nat.mul_le_mul_left _ (show 2 ≤ 2*X.H from by omega))); omega
       apply lt_of_lt_of_le ?_ (pow_le_pow_right₀ L.pos ht); rw [pitchN] at hx; exact_mod_cast hx
set_option maxHeartbeats 460000
lemma agesT (hL:1<L.val)(he:0<ε): ∀ᶠ z in atTop, EaseB L X U M ε Y z:=by
     have hX:X.ν>0:=by have h:=X.flare; omega
     filter_upwards [volley L (X.ν+1) hL,gale L 4 U (M+202) hL (by omega),heavyB L X M hL,(tonicV L hL hX).eventually_gt_atTop (↑(4*M)/ε:ℝ), (tonicV L hL (show 0<X.βA from by unfold βA; omega)).eventually_ge_atTop Y] with x hx ht hp he' hy
     let W:=measureV L X.ν x; have hW : W ≤ W^(2*X.H):= le_self_pow₀ (uniformV ..) (Nat.ne_of_gt (Nat.mul_pos (by omega) X.height)) -- maybe statement
     refine ⟨hx,ht,hp,?_,hy⟩; have h:= (div_lt_iff₀ he).1 (lt_of_lt_of_le he' hW); push_cast at h; rw[mul_comm (_^_) ε] at h -- wrong side.
     linarith only [h] -- check
namespace EaseB
open YM.Intag YM.Intag.Tarot Vista
open Massive.Patria.Depth
variable (p:ℕ)(z:ℝ)
variable (hv:EaseB L X U M ε Y z)(h:ActiveV L X z)
local notation "n!"=> vintage L X z p
local notation "ℓ"=> tailV L X z p
local notation "m!"=> PP L X z p
local notation "qB"=> viewAt L X z p
local notation "q"=> repay L z
variable (Pt:ℕ→BudgetPoint)(hX:entire P₀ A x Pt)(Jv: IntervalE P₀ A L x z p (PP L X z p))
include h hv hX Jv
lemma tallK (b:ℕ)(hh:p ≤ b)(hj:repay L z b ≤ m!) : U*(M+(Pt (repay L z b)).B*(Pt (repay L z b)).B+1) ≤ ratioTo (ladder P₀ A) (repay L z b) b:=by
       have hp:=formerA L X z p h; have hu:= roomsB P₀ A (X.ν+1) 4 p Jv Pt hX hh hj (show b ≤ q b from Nat.le_add_right ..) (show q b-b=distV L 4 z from Nat.add_sub_cancel_left b _) hp.2.2.2 hv.guardT U (M+202) hv.grace
       refine le_trans (Nat.mul_le_mul_left _ ?_) hu; omega
lemma warmK (u:ℕ)(hu:u<X.e)(ht:0<U):let l:=tailV L X z p; 202+(Pt l).B*(Pt l).B ≤ 2*marginM (ladder P₀ A) U (viewAt L X z p u) l:=by
       intro l; let Q:= qB u; have hp':=formerA L X z p h; obtain ⟨h₁,h₂,h₃,h₄,-⟩:=formerB L X z p h u hu; let n' := distV L 4 z
       have hV:U*(M+202+paceN L 3 z*paceN L 3 z+1) ≤ L.val^(l-Q):=by apply hv.grace.trans; apply pow_le_pow_right₀ L.pos; change Q+n'<l at h₃; omega
       let B:=(Pt l).B; refine le_trans (show 202+B*B ≤ marginM (ladder P₀ A) U Q l from ((Nat.le_div_iff_mul_le ht).mpr ?_)) (le_mul_of_one_le_left (Nat.zero_le _) (by omega)); rw [mul_comm]
       have he:l ≤ PP L X z p:=Nat.le_of_lt ((h₄).trans (lt_add_one _)); have hg:B ≤ paceN L 3 z:= (ipB P₀ A p Jv Pt hX h₂ he).trans_le (hv.guardT (l-p) (le_trans (Nat.sub_le_sub_right he _) hp'.2.2.2))
       refine le_trans (Nat.mul_le_mul_left _ (?_)) (le_trans hV (ratV P₀ A p Jv h₁ he (show Q ≤ l from le_trans (Nat.le_add_right .. : Q ≤ q Q) h₃.le)).ge); have hx:=Nat.mul_le_mul hg hg; omega
lemma mob : let l:=tailV L X z p;2*M < ratioTo (ladder P₀ A) n! l*((Pt l).B*(Pt l).B+2):=by
        intro l; obtain ⟨_,h,_,hp,_,_,ht,h'⟩:= formerB L X z p h 0 (show 0< X.e from by have h:=X.extent; omega); have hx:n! ≤ PP L X z p:=Nat.le_succ _
        refine hv.mercy.trans_le (le_trans ?_ (le_mul_of_one_le_right (Nat.zero_le _) (show 1 ≤ _ from by omega))); rw [ratV P₀ A p Jv h hx hp.le]; exact Nat.le_of_eq (congr_arg _ ht.symm)
end EaseB
end Sapphire
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Sapphire.agesT
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Sapphire.EaseB.warmK
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Sapphire.EaseB.mob
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Sapphire.EaseB.tallK
