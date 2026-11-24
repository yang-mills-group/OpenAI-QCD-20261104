import YM.Bard.Tag
import YM.Mural.PerfQ
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

/-! # Mixed stage pricing, budget hook for further analytic purchases -/
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:Rock j}{χ:Chi}{F₀:Flavor N}{tol x Θ W0:ℝ}{st ord:ℕ}
variable (P:SheetR K st ord)(J:(i:ℕ)→Plan (rank i))
variable {P J}

variable {gate:ChangeQ→ℕ} {θ:ℝ}
namespace Suburb
open Spire.Client (Vows fallback ceilingL fall)
variable (tol:ℝ)(Y:Metros P J θ F₀ χ)
open Track
abbrev UnityVM : Calls Y tol:= fun _ _ _ _ _ _ Q x=> MarketCredit _ Q x
lemma renewVM (b b':ChangeQ)(S:Flight b.old b.new)(S':Flight b'.old b'.new)(he:b=b')(hr:HEq S S')(Θ σ α β:ℝ)(h:α=β)(p:ParcelR)(Q:LedgerQ (Y b) tol S Θ σ α p) (Q':LedgerQ (Y b') tol S' Θ σ β p)(h':HEq Q Q')(f:Calls Y tol)(x:ℝ)(ht:let z:=fallback S.L x; Q.Funded _ S z∧f _ _ _ _ _ _ Q z ∧ MarketCredit _ Q z):let z:=fallback S'.L x; Q'.Funded _ S' z∧f _ _ _ _ _ _ Q' z∧ MarketCredit _ Q' z:=by subst b'; subst β; cases hr; cases h'; exact ht
lemma stanceVM (hb:TaleS Y) (hw:Earlier P N gate) (D:Borough Y gate)(h:∀ b,(Y b).bound ≤ gate b)(ht:0<tol)(f:Calls Y tol)(hp:∀ b S Θ σ Λ p (X:LedgerQ (Y b) tol S Θ σ Λ p), gate b ≤ S.L.val → S.patch.Branches K su →0<σ→1≤Θ→1≤Λ→p.Rates (P.width b)→∀ᶠ x in atTop,f _ _ _ _ _ _ X x):∃ (e:Tag P J (fun b=>(Y b).guide.table)→ℕ)(B:ℝ)(Z:Muster tol Y gate), (∀ pay, (D.track e pay).Staked B)∧∀ᶠ x in atTop,∀ pay, delivery Y tol (D.track e pay) (fun b _ _ _ _ _ X x=>f _ _ _ _ _ _ X x ∧ MarketCredit (Y b) X x) (Z.patchV tol Y gate (D.track e pay)) x:=by
   have he (A:Tag P J (fun b=>(Y b).guide.table)) (hA:gate A.node ≤ A.L.val): ∃ n:ℕ,∃ X:LedgerQ (Y A.node) tol A.flight A.Θ A.c (ceilingL A.fromX A.toX) A.fare,∀ x≥ (n:ℝ), let t:=fallback A.L x; X.Funded _ A.flight t ∧ f _ _ _ _ _ _ X t∧ MarketCredit _ X t:=by
      let i:=A.node; let p:=A.supporting
      obtain ⟨Y₀,hQv,hF⟩:= (hb i).horizon tol ht A.flight p.owns ((h _).trans hA) A.Θ A.c (ceilingL ..) (by exact zero_lt_one.trans_le p.roofF) ((ridge A.fromX).trans (le_max_left ..)) A.fare p.applause.rates
      have hz:Tendsto (fallback A.L) atTop atTop:=tendsto_atTop_add_const_right _ (-(_ * _:ℝ)) tendsto_id
      have h0:∀ᶠ x in atTop, MarketCredit (Y i) Y₀ x:= hF.mono fun _ ht=> ⟨⟨⟨hQv,ht.2.1⟩,ht.2.2⟩,ht.1⟩
      obtain ⟨w,H⟩:= eventually_atTop.mp (hz.eventually (Y₀.income.and ((hp _ _ _ _ _ _ Y₀ hA p.owns p.grain p.roofF ((ridge A.fromX).trans (le_max_left ..)) p.applause.rates).and h0)))
      exact ⟨⌈w⌉₊,Y₀,fun x hx=>H x ((Nat.le_ceil w).trans hx)⟩
   have hw' (A : Tag P J (fun b=>(Y b).guide.table)) (hA:gate A.node ≤ A.L.val) := (he A hA)
   let u(A:Tag P J (fun b=>(Y b).guide.table)):= if h: gate A.node ≤ A.L.val then (he A h).choose else 0
   let T (pay:ℕ→ℕ→ℕ):=D.track (Depot.finance u) pay
   let M: Muster tol Y gate:= fun b hb=> (he b hb).choose_spec.choose
   have hv (p:ℕ→ℕ→ℕ)(i:ℕ)(x:ℝ)(hx:x≥ (u ((T p).beam i):ℝ)) : let Z:= M.patchV tol Y gate (T p) i; let t:=fallback ((T p).spacing i) x; Z.Funded _ _ t ∧ f _ _ _ _ _ _ Z t∧ MarketCredit _ Z t:=by
       let F:=T p; let A:=F.beam i; let K0:=F.room i
       apply renewVM tol Y _ _ _ _ (F.node_at i) (F.flight_eq i).symm _ _ _ _ _ _ (M A K0) _ (M.heartsV tol Y gate F i)
       · apply (he A K0).choose_spec.choose_spec; rw [show u ((T p).beam i)=_ from (show u ((T p).beam i) = (he A K0).choose from (by unfold u; rw [dif_pos ((T p).room i)]))] at hx; exact hx
       rw [←show (T p).town (i+1)=A.fromX from (F.nexts i).2.1.symm]
   refine ⟨Depot.finance u,_,M,D.staked u,?_⟩
   filter_upwards [D.solvent u hw] with x hx pay i
   exact hv pay i _ (hx pay i)
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.stanceVM
