import YM.Profiles.Counts
import YM.Profiles.PerchV
import YM.Next.RANK.Coordinates
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
namespace Tiler
open Finset
open Planned.PrimaryIntegral295 MassiveQCD.Sample MassiveQCD.Sample.LoomT MassiveQCD.Cupola MassiveQCD.Plate
lemma cellar_step (k:Side)(b:Cover): Carrier.cellar k (k.val • b)=b:=by
    let L:=k.val; have hx:wrap k (k.val • b)=0:=by
         rw [map_nsmul]; ext i; simp
    let P:= wrap k; have hp := Work.F08.carry_spec (0:Site k) (L • b); simp only [Work.F08.arrives] at hp; rw [show Lattice.lift (0:Site k)=0 by funext i; simp [Lattice.lift],zero_add,hx,show Lattice.lift (0:Site k)=0 by funext i; simp [Lattice.lift],zero_add] at hp
    exact nsmul_right_injective k.pos.ne' hp.symm -- L type.Support
variable {I:Type} [Fintype I] (q:I→Bool)
local notation "Δ"=>Eq (α:=I)
abbrev square (I:Type) := Set.univ (α:=Finset I)
local notation "Hp"=> square I
lemma pledgeR : Pledge q q Δ Hp Hp:=by
    refine ⟨⟨Set.mem_univ _,fun i j _ _=>Set.mem_univ _,fun _ i j k _ _ _ h1 h2=> h1.symm.trans h2⟩,fun i j h=> congr_arg q h,fun i j _=>Set.mem_univ i⟩
lemma earnR (j:I) : (∑ x:MassiveQCD.Sample.LoomT.To Δ j, (1:ℝ))=1:=by
    haveI : Unique (MassiveQCD.Sample.LoomT.To Δ j):={default:=⟨j,rfl⟩,uniq:=fun x=> Subtype.ext x.property}; rw [Fintype.sum_unique]
lemma tailR (j:I) : (opts Δ j).card ≤1:=by
    change _≤_; unfold opts; apply card_le_one.2; intro i hi k hk; exact ((mem_filter.mp hi).2).symm.trans (mem_filter.mp hk).2
lemma fires_of_inj (R:I→Site c)(hc:Injective R)(H:ℕ)(hm:0<H): Fires R H:= fun i=> (card_le_one.mpr (fun x hx y hy=>hc (((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm))).trans hm
open Counter.Economies -- via Perch?
variable (W:Side)
local notation "π"=>stampR P₀ A
lemma qstabs (R: Side)(hm:i ≤ j) : (A.ring R j).val=(A.ring R i).val * π i j:=by simp_rw [Track.ring,PNat.mul_coe]; rw [stamps _ _ hm,Nat.mul_assoc]
noncomputable abbrev knit (R:Side){i j:ℕ}(h:i ≤ j) : Ratio (A.ring R i) (A.ring R j):=⟨⟨stampR P₀ A i j,stamp_g P₀ A h⟩,qstabs P₀ A R h⟩
-- systematic placement frontier. No fixed ordering
noncomputable abbrev atoll (j:ℕ)(b:I→ Cover)(i:ℕ)(u:I): Cover:=stampR P₀ A j i • b u
variable (R₂: Side)(Xb:I→ Cover)(hX:Injective (wrap (A.ring R₂ j)∘Xb))
local notation "Aq"=>A.ring R₂
local notation "T"=>atoll P₀ A j Xb
local notation "H" i:arg =>wrap (Aq i) ∘ (T i)
lemma climbs (h:j≤ i)(u:I): T (i+1) u =(A.spacing i).val • T i u:=by unfold atoll; rw [stamp_t _ _ h,mul_comm,mul_smul]
include hX
lemma focusW (h:j≤ i): Injective (wrap (Aq i) ∘ (atoll P₀ A j Xb i)):=by
    let J:=knit P₀ A R₂ h; have hq : H i=J.embed ∘ (wrap (Aq j) ∘ Xb):=funext fun u=> (J.embed_wrap (Xb u)).symm; rw [hq]; exact J.embed_injective.comp hX
lemma notches (h:j ≤ i)(u v:I)(hu:u≠v): stampR P₀ A j i ≤ separation ((H i) u) ((H i) v):=by
    let V:= knit P₀ A R₂ h; have he(k):(H i) k = V.embed (wrap (Aq j) (Xb k)):= (V.embed_wrap (Xb k)).symm ; rw [he,he, Next.Rank.Station.both]; apply le_mul_of_one_le_right (Nat.zero_le _); exact Next.Rank.Station.separation_pos _ _ (fun hx=> hu (hX hx))
lemma booked (D:ℕ)(h₀:1 ≤ D)(hV:∀ i:ℕ,Counter.Cave (A.spacing i) (clockQ P₀ A x i) θ)(m:ℕ)(he:m=Counter.Economies.maturity P₀ A hV j D)(hp:m ≤ i)(s:Finset I): Spaced (wrap (Aq i)∘ (atoll P₀ A j Xb i)) s (radiusB (Track.scale A x i)):=by
    obtain ⟨h1,h2,h3⟩:= Counter.post P₀ A hV D m he; intro u hu v hv hF; apply le_trans _ (notches P₀ A _ _ hX (h1.trans hp) u v hF); rw [←sq]; induction hp with
    | refl=>exact (le_mul_of_one_le_left (Nat.zero_le _) h₀).trans h2
    | @step i hk ih=>
       have hf := (Counter.evolves P₀ A hV i).1; rw [stamp_t P₀ A (h1.trans hk)]; exact hf.trans ((mul_le_mul (_root_.le_trans (by norm_num : 2 ≤ 3) (show 3≤ (A.spacing i).val from (A.flight i).coarse)) ih (Nat.zero_le _) (Nat.zero_le _)).trans_eq (mul_comm _ _))
omit hX
end Tiler
end Counter
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Counter.Tiler.booked
