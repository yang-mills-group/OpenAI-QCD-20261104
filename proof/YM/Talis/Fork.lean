import YM.Talis.Round
import YM.Bloom.Shrimp
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
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
open YM.Bloom.TreeP YM.Arise QCD.Bloom.Buzz QCD.Bank
variable (ν a δ H D:ℕ)
-- realization of spans vs ratio.Th.Can.Rfn integer. Note counter operators Polis.Max. true numerator.
private lemma stamp (g:Side)(W:ℝ) (k:ℕ): W^(4+2*k)/(g.val:ℝ)^(2+k)=(W^2/(g.val:ℝ))^(2+k):=by rw [div_pow,←pow_mul]; congr 2; omega
private lemma stall (g:Side)(W:ℝ) (k:ℕ): (W^(3+2*k)*QCD.Bank.gear g k)^2=(W^2/(g.val:ℝ))^(3+2*k):=by
     let f:=(g.val:ℝ); have hz:0<f:=by unfold f; positivity
     unfold QCD.Bank.gear Kit.slope; rw [mul_pow, div_pow, inv_pow,Real.sq_sqrt (show 0≤ f from hz.le), div_pow _ _]; change (W^(3+2*k))^2* (f⁻¹/(f^(1+k))^2)=(W^2)^(3+2*k)/f^(3+2*k); rw [←pow_mul,←pow_mul,←pow_mul,mul_comm 2 (3+2*k),show 3+2*k=1+(1+k)*2 from by omega,pow_add f]; simp only [pow_one]; ring
-- factor currency ζM.Certificate.El. generic when q.SetL. rent as Above.
private lemma suc_fact (W:ℝ)(g:Side)(v:ℝ)(hv:1≤v)(hW:1≤W)(he: g.val=W^2*v): Factor W D g v⁻¹∧ Porter W D g v⁻¹:=by
     have hV:0<v:= zero_lt_one.trans_le hv; have hz:0 < W:= zero_lt_one.trans_le hW; have hP:0<v⁻¹:=(by positivity); have hp: v⁻¹ ≤1:= inv_le_one_of_one_le₀ hv
     have h:W^2 / (g.val:ℝ)=v⁻¹:=by rw[he]; field_simp
     refine ⟨⟨hW,hP.le,fun k hk=>?_⟩,hW,hP.le,fun k hk=>?_⟩
     · rw [stamp,h]; exact (pow_le_pow_of_le_one hP.le hp (show 1 ≤ 2+k by omega)).trans_eq (pow_one ..)
     have hh:(W^(3+2*k)*QCD.Bank.gear g k)^2 ≤ v⁻¹^2:=by rw [stall,h]; exact pow_le_pow_of_le_one hP.le hp (by omega)
     nlinarith only [hh,hP] -- rpow lex
private lemma low_fact (W:ℝ)(g:Side)(v M:ℝ)(hv:1≤v)(hW:1≤W)(he: g.val=W^2/v)(hp: v^(2+D) ≤M): Factor W D g M ∧ Porter W D g M:=by
     have hV:0<v:=zero_lt_one.trans_le hv; have hn:0< W:=zero_lt_one.trans_le hW
     have hx :W^2/(g.val:ℝ)=v:=by rw[he]; field_simp
     have ht:= (pow_pos hV (2+D)).trans_le hp
     refine ⟨⟨hW,ht.le,fun k hk=>?_⟩,hW,ht.le,fun k hk=>?_⟩
     · rw[stamp,hx]; exact (pow_le_pow_right₀ hv (by omega)).trans hp
     have hh:(W^(3+2*k)*QCD.Bank.gear g k)^2 ≤ M^2:=by rw[stall,hx]; exact le_trans (b:=(v^(2+D))^2) (by rw [←pow_mul]; exact pow_le_pow_right₀ hv (by omega)) (pow_le_pow_left₀ (pow_pos hV _|>.le) hp 2)
     nlinarith only [hh,ht]
local notation "xΩ"=> WTop L ν H
lemma scalesA {z:ℝ}(g:Side)(hp:g.val=L.val^(bookA L ν H a z)): Factor (WTop L ν H z) D g (measureV L a z)⁻¹∧ Porter (WTop L ν H z) D g (measureV L a z)⁻¹:=by
       have he:(g.val:ℝ)=(L.val:ℝ)^(bookA L ν H a z):=by exact_mod_cast hp
       exact suc_fact D _ _ _ (uniformV ..) (joy ν H z) (he.trans (wins _ ν a H z)) -- order
variable {u b u':ℕ}
lemma scalesB (hL:1<L.val)(hq:u<b)(ht:δ<b):∀ᶠ z in atTop, distV L u z ≤ Jc L ν H z →disc L δ z ≤bookB L ν H u z → ∀ g:Side,g.val= L.val^(bookB L ν H u z-disc L δ z)→ Factor (xΩ z) D g (EV b z) ∧ Porter (xΩ z) D g (EV b z):=by
       let d:=max u δ; let hv: PageP L (fun z=> (measureV L u z*measureV L δ z)^(2+D)) d:=((PageP.budget_lo L (le_max_left ..)).times L (PageP.budget_lo L (le_max_right ..))).liftNat L (2+D)
       filter_upwards [PageP.cheaper L hv hL (show d < b from max_lt hq ht)] with z hz hu hp g h; have he:(g.val:ℝ)=(L.val:ℝ)^(bookB L ν H u z-disc L δ z):=by exact_mod_cast h
       exact low_fact D _ _ _ _ (one_le_mul_of_one_le_of_one_le (uniformV ..) (uniformV ..)) (joy ν H z) (he.trans (spanB L ν u δ H z hu hp)) hz
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.scalesB
