import YM.QCD.Stem.Ule
/-! # LEDGER. all tags finance delivered before data proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j k l m:ℕ}{d r t t' p p' η b z A Δ θ ρ P' :ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration Song Meadow Quotes
variable (S:Silo c)(T: BankP c)(X:St c)
local notation "P"=> sealG S N
local notation "K"=>kiln c B.B
local notation "q₀"=> B.B
local notation "Z"=> preExponent B
-- purchase direct trunk X, reversible stash
lemma incomeK (hn:0<n)(hp : Run.Pack id id d r n X b S T) (ht : Torch S)(hz: n ≤ q₀)(hC:0 < d)(hr:1≤ η)(hv:z+1+1≤ Z) (hk:0≤z)
    (hw: AnchorT P (portage B hn) η (Z+1) t):
      AnchorT P B η (Z+1) t ∧ TokenB (hoist P B.threshold) B.threshold q₀ z (payment 1 (4*q₀+2) 0 1 1 t z 0) η ∧ Bound (rat S N q₀) univ (huskQ P K) (Ruby.HJoin (burl P K q₀ B) (hoist P B.threshold)) B (q₀+q₀) (Real.exp (-meterQ n q₀)*t) (t*ballCost q₀) (penS q₀ 1 t z+Footprint.payment 1 (4*q₀+2) 0 1 1 t z 0) η Z z (paleF N ∘ X):=by
   have he:= glossy hp ht N; obtain ⟨x,hx,hx'⟩:=hw.peg
   have hL:= notables d S T X hp hC hn hz (w:=q₀) peg_pos.le hw.law -- b name
   have h1 : 0≤ Z+1:= add_nonneg peg_pos.le zero_le_one
   have hx : Anchored (fun i=> ((P).addr i).site) x (fun i=>coverNumber q₀ ((P).addr i).support) (Z+1) t:= pardon P x _ _ hx (fun i=> cover_earns hz _) h1 (fun i=> (hx' i).1.travel)
   have hD : AnchorT P B η (Z+1) t:=by
      refine ⟨x,hx,fun i=> ?_⟩; obtain ⟨hh,he⟩:=hx' i; refine ⟨⟨hh.room,hh.gated,hh.use,hh.pole,hh.Borel,hh.travel⟩,he⟩
   have he':0<η:= zero_lt_one.trans_le hr
   have hy:= infold P K hD.law he.blank (fun i hi=>breadth _ hi) hL hr h1 hk (show q₀≤1*B.B from (by rw [one_mul]))
   have hE := stony P hD.law he.blank he' x hx (fun (i:Tick c) V=> (opticX ((P).view i V) ((P).addr i).site η he').trans ((hx' i).2 V)) (le_trans hv (by linarith)) hk
   refine ⟨hD,hE,away _ _ _ _ hy hr peg_pos.le _ hE hk (fun _=> Summable.of_finite) ?_⟩; intro U; refine thaw P hD.law hr h1 U _ (_root_.id ?_)
   have hp : Summable (fun i=>((P).view i) U):=Summable.of_finite; apply hp.hasSum_iff.mpr ?_; rw [tsum_fintype]; exact setsK (by assumption) .. -- assumption
local notation "τ"=> B.threshold
variable (Y:Gem c N I)(J:Finset I)
lemma anchorM (v:I→ℝ)(hz:∀ i,0≤v i)(h:Ac.Hit (fun i=>(Y.addr i).support) q₀ v t d): Anchored (fun i=> (Y.addr i).site) v (fun i=> coverNumber q₀ (Y.addr i).support) t d:=by
   intro x; apply budget_mono (h x)
   · intro i; split; exact mul_nonneg (hz i) (Real.exp_pos _).le; exact le_rfl
   intro i; dsimp only; split
   next he=> rw [if_pos (he ▸ (Y.addr i).anchor)]
   next hq=> exact (h x).1 _
lemma defaultP (hp:SoilB J Y B w t)(hx:Pockets J Y B t d) (Z':I→Prop)(hv:Licence B r z t (muteK Y Z'))(hg:Dyed Y):
    Bound Y J (muteK Y Z') (spareH c N) B w z d 0 t r b (fun U:Grid c=>(∑ i∈J,letters Y τ U i)+ Patron.total (muteK Y Z') τ U) :=by
     refine ⟨hp,hx,hv,dyedM _ hg _,spareTu,fun i=>?_⟩; rw [tsum_empty,add_zero]
end YM.QCD.Stem
