import YM.VStages.Purchasing
import YM.Massive.Stratum.Range
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog.Mist
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03 Voyage
open YM.Massive.Stratum Raft Raft.ParcelR
open scoped Matrix Topology ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}

variable {α :ℝ} 
structure BirthW (R:ParcelR) (P:Plan j)(T:Plan k)(V:Back E K j k p u v) (L: Avenue V η Ω Θ) (X Y:SunR R)(α:ℝ):Prop where
 roots (i:ℕ) : Tender (V.charge P T X.X.lamp i) (castF (Y.X.lamp _)) 2
 limbs (i:ℕ): Tender (V.charge P T X.powerG i) (castF (Y.powerG _)) 3
 bill:|α| ≤ R.b
 price:Skies P V X.powerG L.D' X.Z.page Y.Z.page α R.w R.l

structure BondW (J:Plan j) (L:Plan k)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(X Y: Ledger)(P:ParcelR):Prop where
 near:Buoy X P
 far:Buoy Y P
 rates:Rates P η
 sails (V:Back E K j k p u v) (F:Avenue V η Ω Θ) (S:SunR (rate X)):
      ∃ (S':SunR (rate Y)) (α:ℝ),BirthW P J L V F (near.keep rates S) (far.keep rates S') α
lemma bond (J:Plan j) (L:Plan k)(X Y:Ledger)(he:0<η)(h:Story J L E K p u v η Ω Θ X Y):∃ P:ParcelR,BondW J L E K p u v η Ω Θ X Y P:=by
  obtain ⟨⟨h,hT⟩,b,l,hL,H⟩:=h
  let P:ParcelR:=⟨min X.1.1.r Y.1.1.r,min X.1.2.r Y.1.2.r,min (min X.2.r Y.2.r) (η/2),max X.1.1.bill Y.1.1.bill,max X.1.2.bill Y.1.2.bill,max X.2.bill Y.2.bill,b.r,b.bill,l⟩
  have hx:Buoy X P:= ⟨min_le_left ..,le_max_left ..,min_le_left ..,le_max_left ..,(min_le_left ..).trans (min_le_left ..),le_max_left ..⟩; have hy:Buoy Y P:= ⟨min_le_right ..,le_max_right ..,min_le_right ..,le_max_right ..,(min_le_left ..).trans (min_le_right ..),le_max_right ..⟩
  have hr:Rates P η:=⟨lt_min X.1.1.live Y.1.1.live, lt_min X.1.2.live Y.1.2.live, lt_min (lt_min X.2.live Y.2.live) (by positivity), X.1.1.good.trans hx.firstCap, X.1.2.good.trans hx.secondCap,X.2.good.trans hx.thirdCap,b.live,b.good,hL,min_le_right ..⟩
  refine ⟨P,hx,hy,hr,fun V F S=>?_⟩
  obtain ⟨U₁,h₁⟩:=h V F S.X; obtain ⟨U₂,h₂⟩:=hT V F S.X U₁ S.Y h₁; obtain ⟨α,Z,hα,hZ⟩:= H V F S.X S.Y S.Z
  exact ⟨⟨U₁,U₂,Z⟩,α,h₁,h₂,hα,hZ⟩

end YM.QCD.Fog.Mist

namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{B T: Bed}{F L:Side→ℝ}
open ChangeQ
variable {l:ChangeQ} {h hr:ℕ→ℕ} (P:Docket K h hr) (J:(i:ℕ)→Plan (rank i))
noncomputable def city (e:ChangeQ):Teller su:= ⟨K,P.stage e.hi,P.stage e.lo,e.old,P.width e,P.cost e,(P.retail e).pos⟩
def relation (e:ChangeQ)(E:Patch) := Tangle (Story (J e.hi) (J e.lo) E K (P.stage e.hi).clip (P.stage e.hi).width (P.allowance e.hi) (P.width e) (P.cost e) (P.cost e)) (Loop (P.postLoop e) E)
theorem connected (e:ChangeQ) : ∃ n:ℕ,∀ E:Patch,n≤E.L.val→ Century (relation P J e E):=by
   have H:0≤P.cost e:= zero_le_one.trans (P.retail e).ample
   obtain ⟨n,h⟩:= rays (J e.hi) (J e.lo) (rank_ge _) (rank_ge _) (P.retail e).pos H H; refine ⟨n,fun E ht=>?_⟩
   obtain ⟨Z⟩:= Push.Uniform.pre_order su (P.stage e.hi).width (P.allowance e.hi) E.J K (le_refl 3)
   have hh:=h E ht _ K (P.stage e.hi).width (P.allowance e.hi) Z (P.stage e.hi).clip; apply stitch _ _ hh
   · intro a b _ u; obtain ⟨X,H⟩:=scope (P.postLoop e) E a b; exact ⟨_, H _ _ (Price.step ..)⟩
   intro a ha; obtain ⟨X,H⟩:=scope (P.postLoop e) E a a; exact Price.hit X _ H

def helm (S:Flight j k)(x:Train j): Flight j k:= { S with wing:=x }
structure FlightTicket (P:Docket K h hr)(J:(i:ℕ)→Plan (rank i))(l:ChangeQ)(S:Flight l.old l.new)(X Y:Town)(p:ChartRatio su)(c Θ:ℝ)(Ω:ParcelR):Prop where
  grain : 0 < c
  roofF : 1 ≤ Θ
  fares : P.lim l ≤ S.L.val
  owns : S.patch.Branches K su
  applause : BondW (J l.hi) (J l.lo) S.patch K (P.stage l.hi).clip (P.stage l.hi).width (P.allowance l.hi) (P.width l) (P.cost l) (P.cost l) X.1 Y.1 Ω
  crossing : ∀ (z:Train l.old) (B T: Bed) (R:PathData su) (D:Towers S.L), let F:=helm S z; let P₁:=P.stage l.hi; let P₂:=P.stage l.lo;
    QuarryQ P₁.clip (P.width l) (P.floor l) (P.cost l) B → QuarryQ P₂.clip (P.width l) (P.floor l) (P.cost l) T → Enjoy B P₁.clip P₁.width (P.allowance l.hi) (loop X) R →
    DeltaW K P₁.clip P₂.clip (P.width l) (P.cost l) F B T D→∀ m:SparkMesh,reachM S.patch m →∃ (α:ℝ)(R':PathData su), Enjoy T P₂.clip P₂.width (P.allowance l.lo) (loop Y) R' ∧ Nonempty (Aloft F K m R' R P₁.clip P₂.clip P₁.width (P.allowance l.hi) D p α c Θ (P.gamma l) (P.slope l))
lemma issueW (X Y:Town) (S:Flight l.old l.new)(hf:P.lim l ≤ S.L.val)(hp:LocalRatio p)(hv:S.patch.Branches K su)(h: relation P J l S.patch X Y):∃ c Θ Ω,FlightTicket P J l S X Y p c Θ Ω:=by
   obtain ⟨Ω,hΩ⟩:= bond (J l.hi) (J l.lo) X.1 Y.1 (P.retail l).pos h.1
   obtain ⟨c,H1,H⟩:= uncover (k:=l.new) (q':=(P.stage l.lo).clip) (q:=(P.stage l.hi).clip) (P.horn l) (P.stage l.lo).width_pos hp (P.retail l).growth S.L
   let Θ:=max 1 (P.goalsAt l S.L)
   refine ⟨c,Θ,Ω,H1,le_max_left ..,hf,hv,hΩ,?_⟩
   intro i B T R D F hu hv hB hT hR hD m hm
   exact H F rfl hf (by exact ‹S.patch.Branches K su›) _ _ D m _ _ _ Θ hB hT hD (ridge X) h.2.1 h.2.2 hm (le_max_right ..) hR
lemma continues {X:Type*} {H:X→X→Prop}(h: Century H)(x:X):∃ y:X,H x y:=by
   obtain ⟨y, ht,hL⟩:=h; cases hL x using Relation.ReflTransGen.head_induction_on with
   | refl => exact ⟨_,ht⟩
   | head ha h' ih => exact ⟨_,ha⟩
end YM.QCD.Acre.Stratum.MarchQ
