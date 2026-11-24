import YM.Mistral.Num
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace Mistral
-- deterministic income algebra for Ward pair. orientation costs same both banks.
open Counter MassiveQCD.Sample.Eole.Gain
open Finset MassiveQCD.Sample MassiveQCD.Sample.Sail MassiveQCD.Sample.Kuna
namespace Coins
variable (d:ℕ)
local notation "V"=> ((d:ℝ)/2)
local notation "P"=>((d:ℝ)/2+1/128)
local notation "Z"=>((d:ℝ)/2+1/4)
variable (m₀ m₁ Δ u:ℝ)
local notation "E"=>Real.exp
local notation "M"=> E m₁
local notation "G"=> E u
variable (hD:0≤Δ)(hQ:Δ≤ m₁/(20000*((d:ℝ)+10)))(hC:10000*((d:ℝ)+10)*u= Δ)(he:0<u)(ht:32≤ Real.exp u)
include hD hQ hC he
lemma warm :100*u ≤ Δ:=by have h:= Nat.cast_nonneg (α:=ℝ) d; nlinarith only [hD,hC,he,h]
-- better. hℓ relative.D.Xk.
lemma liteM: Δ*(20000*((d:ℝ)+10)) ≤ m₁ := (le_div_iff₀ (by positivity)).1 hQ
lemma heavyM : (20000*((d:ℝ)+10))*u ≤ m₁:=by have h:= warm d m₁ Δ u hD hQ hC he; exact (mul_le_mul_of_nonneg_left (by linarith:u≤Δ) (by positivity)).trans ((mul_comm _ _).le.trans (liteM d m₁ Δ u hD hQ hC he))
lemma leanM : 10000*u+(d:ℝ)*100*u+(d:ℝ)*100*Δ+1000*Δ≤ m₁:=by have h:=liteM d m₁ Δ u hD hQ hC he; have hy:=heavyM d m₁ Δ u hD hQ hC he; have hz:=Nat.cast_nonneg (α:=ℝ) d; nlinarith only [hy,h,hD,he,hz]
-- elementary powered comparisons
local notation "K1"=> G^2 * E (P*Δ)
local notation "K2" => (2 * G^2) * K1 * E (P*Δ)
include ht
lemma Ť₁ : K2 ≤ E ((1/128)*m₁):=by
      calc _ ≤ G^5 * E (2*P*Δ):=by
                rw [show 2*P*Δ=P*Δ+P*Δ from by ring,Real.exp_add] -- E macro no
                change 2*G^2 * (G^2*E _) *_ ≤ _
                exact le_trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show 2 ≤ G from le_trans (by norm_num:2 ≤ (32:ℝ)) ht) (by positivity)) (by positivity)) (show 0 ≤ E (P*Δ) from by positivity))) (le_of_eq (by ring))
           _ = E (5*u+2*P*Δ):= (by rw [Real.exp_add,← Real.exp_nat_mul]; push_cast <;> rfl)
           _ ≤ _:=Real.exp_monotone (by have h:= leanM d m₁ Δ u hD hQ hC he; nlinarith only [h,liteM d m₁ Δ u hD hQ hC he,hD,Nat.cast_nonneg (α:=ℝ) d,he])
omit hQ
lemma growth_feeΔ (r:ℝ)(h:0 ≤ r)(hp:(V+1)*r ≤ u): (G*K1*G)*E (-(Z*(Δ-r)))*G^12 ≤ G⁻¹:=by
      change (G*(G^2 * E (P*Δ))*G)*E _*G^12≤_
      simp_rw [← Real.exp_nat_mul,← Real.exp_neg,←Real.exp_add]; push_cast; apply Real.exp_monotone; nlinarith only[h,hp,hC,he,Nat.cast_nonneg (α:=ℝ) d]
include hQ
-- pair scale |σ| includes stress comp. cap hΔ e^(+1/128) toler.fiscal spent. cost formula sharp witness values supplied choose.N!
local notation "Y₁"=> E ((V+(1/8))*m₁)
local notation "Y₂"=> E ((V+(1/6))*m₁)
local notation "F"=> E ((V+(1/64))*m₁)
local notation "Xv"=> E ((1/128)*m₁)
local notation "W"=> (E ((4+1/32)*m₁)) * (E (-m₁)*G)^4
variable {C c a A' S':ℝ} -- C salary_i, a premium, A'≤G^3.Exp via Δ ray ≤u, S' < etc
variable (hCp:0<C)(hc:0<c)(hv:C≤1)(hs:c⁻¹ ≤ Real.exp u*Real.exp u)(ha:a≤ Real.exp u)(hA:A' ≤ Real.exp u^3)(hQ':|S'| ≤ (Real.exp ((4+1/32)*m₁)) * (Real.exp (-m₁)*Real.exp u)^4)
include hCp hc hv hs ha hA hQ'
lemma coins : Access Y₁ Y₂ a A' C c S' F Xv:=by
      have hG':1 ≤ G:=le_trans (by norm_num: (1:ℝ)≤32) ht
      have hM:0 ≤ m₁:=by have h:=liteM d m₁ Δ u hD hQ hC he; nlinarith only[h,hD,show 0≤(d:ℝ) from by positivity]
      have hy: Y₁ ≤ Y₂:= Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only :V+1/8≤V+1/6) hM)
      have hV:1+2*a ≤ G^2:=by nlinarith only [ha, ht]
      have hp:(1/c) ≤ G*G:=by simpa only [one_div] using hs
      have hX : 0 < W:=by positivity
      have hyG:G^2*Y₁ ≤ Y₂:=by simp_rw [←Real.exp_nat_mul,←Real.exp_add]; push_cast; apply Real.exp_monotone; have h:=heavyM d m₁ Δ u hD hQ hC he; nlinarith only [h,Nat.cast_nonneg (α:=ℝ) d,he]
      have hP (Y:ℝ)(hy:Y₁≤Y): |2*(C/Y*S')| *F*Xv ≤ c^2:=by
            have htY: 0 < Y:=lt_of_lt_of_le (Real.exp_pos _) hy
            have htB:|2*(C/Y*S')| ≤ G/Y₁* W:=calc
                  _ = 2*(C/Y)*|S'|:= by rw [mul_comm (2:ℝ),abs_mul,abs_mul,abs_of_nonneg (div_pos hCp htY).le,abs_of_nonneg (by norm_num:(0:ℝ)≤2)]; ring
                  _ ≤ 2*(1/Y₁)* W:=(mul_le_mul (mul_le_mul_of_nonneg_left (div_le_div₀ (by norm_num:(0:ℝ)≤1) hv (Real.exp_pos _) hy) (by norm_num)) hQ' (abs_nonneg _) (by positivity))
                  _ ≤ G/Y₁* W:=(by gcongr; first | exact le_trans (by norm_num) ht | convert div_le_div_of_nonneg_right (le_trans (by norm_num : (2:ℝ)≤32) ht) (Real.exp_nonneg _) using 1 <;> ring)
            have hB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htB (show 0 ≤ F from Real.exp_nonneg _)) (Real.exp_nonneg ((1/128)*m₁))
            apply le_trans hB; have ht':(G*G)⁻¹ ≤ c:= inv_le_of_inv_le₀ hc hs
            refine le_trans ?_ (pow_le_pow_left₀ (by positivity) ht' 2)
            simp only [div_eq_mul_inv,←Real.exp_neg,←Real.exp_nat_mul, ←Real.exp_add]; push_cast; apply Real.exp_monotone; have h:=heavyM d m₁ Δ u hD hQ hC he; norm_num at *; nlinarith only [h,Nat.cast_nonneg (α:=ℝ) d,he]
      refine ⟨Real.exp_pos _,hP _ le_rfl,Real.exp_pos _,(mul_le_mul_of_nonneg_right hV (Real.exp_nonneg _)).trans hyG,hP _ hy,?_⟩
      have hx:2*(C/Y₂) ≤G/Y₂:= by rw [←mul_div_assoc]; gcongr; linarith only [ht,hv]
      have hh:(G*G)⁻¹ ≤ c:= inv_le_of_inv_le₀ hc hs
      have hR:= mul_le_mul_of_nonneg_right hA (Real.exp_nonneg ((V+(1/8))*m₁)); apply le_trans ((mul_le_mul_of_nonneg_left hR (show 0 ≤2*(C/Y₂) from by positivity)).trans (mul_le_mul_of_nonneg_right hx (by positivity)))
      apply le_trans _ hh; simp only [div_eq_mul_inv,←Real.exp_nat_mul,←Real.exp_neg,←Real.exp_add]; push_cast; apply Real.exp_monotone; have h:=heavyM d m₁ Δ u hD hQ hC he; norm_num at *; nlinarith only [h,Nat.cast_nonneg (α:=ℝ) d,he]
end Coins
end Mistral
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Mistral.Coins.coins
