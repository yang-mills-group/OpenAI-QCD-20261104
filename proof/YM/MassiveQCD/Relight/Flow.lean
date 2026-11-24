import YM.MassiveQCD.Relight.Vale
import YM.MassiveQCD.Relight.Exchange
import YM.MassiveQCD.Tangent.Sieve
import YM.MassiveQCD.Relight.Seal
import YM.MassiveQCD.Relight.Generic
import YM.MassiveQCD.Tangent.Aisle
/-! # Rotate with respect to `Honest` occupancy; preserve weight classes
 before remasking (uses the robust `relight` eventual equality in the complex range). -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival Shells Shells.Warmlet Finch Stem Grove Calm
variable (E G:Gem c N I)(X:Ruby.Hue c N J)(U:Grid c)(v:I→ℕ)(z:ℕ→ℂ)
set_option quotPrecheck false
local notation "T0"=> v ∘ Prod.snd
local notation "X0"=> stitch E G p
local notation "R!"=> flightY (X0) r
local notation "F!"=> flightE (glean G) r
open Tangent
variable {C M A B:ℝ} (hp:Bridge E G v p t u η C ξ)(ht:0<r)(hb:1≤ t)(ha:1 ≤ a)(hf:r*a≤ t) (he:0 ≤ η)(hQ:0 ≤ u)
include hp ht hb he ha hf hQ
lemma board : RotationE (F!) T0 ∧ Yank (R!) T0 ∧ Wax R! p.threshold p.B η (stitchCost p ξ η) a ∧ Licence p u C a F! ∧ ∀ z:ℕ→ℂ,UnitCoeff z →∀ V, wearK c N r (Stem.income (weight E v z) p.threshold V)=Stem.income (weight F! T0 z) p.threshold V + swarm (bleach R! T0 z) V:=by
    refine ⟨wired (glean G) T0 r hp.alive,wisedY _ T0 hp.glory,warmedY _ hp.earn ht (zero_lt_one.trans_le ha) hf,irises _ hp.debit (zero_le_one.trans ha) ht.le hf, fun z hz V=>?_⟩
    rw [hp.flow z V hz,map_add,← wingY,← wing]; exact congr_arg₂ (·+·) (sour _ V r (permits _ (payments _ T0 z (fun _=>hz _) zero_le_one hp.debit) (zero_lt_one.trans_le hb) hQ V)).tsum_eq.symm (wings _ r V ((bleachPay _ T0 z (fun _=>hz _) zero_le_one hp.earn).heated hb he V).1).tsum_eq.symm
local notation "Gh"=> Ghoul (F!) T0
noncomputable abbrev solidify (b:Bool)(t r:ℝ): Ruby.Hue c N ((ManyA c I)⊕ ManyA c I):= HJoin (flightY (stitch E G p) r) (refund (flightE (glean G) r) b t)
local notation "X!"=> Sum.elim (T0) T0
structure Arbor (b:Bool)(E G:Gem c N I)(v:I→ℕ)(p:BudgetPoint)(r u η B C l :ℝ):Prop where
    peers: Peers (shadowE (flightE (glean G) r) b) (v ∘ Prod.snd) p u l C
    buy: Wax (solidify E G b p.threshold r (p:=p)) p.threshold p.B η B l
    face: Yank (solidify E G b p.threshold r (p:=p)) (Sum.elim (v∘Prod.snd) (v∘Prod.snd))
    fisc: SumBudget (fun i=> ‖gemTone (flightE (glean G) r) i‖) ((Fintype.card (Site c):ℝ)*C)
    sparta: ∀ z:ℕ→ℂ,UnitCoeff z→∀ x:Grid c,
       wearK c N r (Stem.income (weight E v z) p.threshold x)=
       Stem.income (weight (shadowE (flightE (glean G) r) b) (v∘Prod.snd) z) p.threshold x + sparkF c N (vern (flightE (glean G) r) z (v∘Prod.snd)) + labelled (flightE (glean G) r) b z x (p:=p)+ swarm (bleach (solidify E G b p.threshold r (p:=p)) (Sum.elim (v∘Prod.snd) (v∘Prod.snd)) z) x
variable (b:Bool)(hM :∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ M*Sen i w X)
include hM
lemma arboretum (h:b=true→∀ i,v i=1)(h':b=false→∀ i,2≤v i)(hx:η+1+1 ≤ u)(hm:1≤M): let Q:= tideCost N M*C; Arbor b E G v p r u η (stitchCost p ξ η+ stitchCost p Q η) Q a:=by
   intro Q; obtain ⟨hF,hG,hY,hZ,hS⟩:=board E G v hp ht hb ha hf he hQ
   obtain ⟨hp0,hX,hX',hN,hT⟩:=jobs _ _ b hM hm ⟨hF,fun i hb=>h hb i.2, fun i hb=>h' hb i.2⟩ hZ ha hx he; refine ⟨hp0,reach_w hY hX, notedW _ _ hG hX', ?_, fun z hz F=>?_⟩
   · let N := Fintype.card (Site c); have hu:0 ≤ C:=by obtain ⟨T,hT,-⟩:= hp.debit.zone; exact budget_nonneg (hT (0:Site c)); -- syntax
     exact budget_loosen hN (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hu (weightEase M hm)) (Nat.cast_nonneg _))
   rw [hS z hz F, hT z hz F]
   let X:= refund (F!) b p.threshold; let H:= (bleach X (T0) z); let V:= (bleach R! T0 z);
   have hQ : swarm (bleach (solidify E G b p.threshold r (p:=p)) (X!) z) F=swarm V F+swarm H F:= (HasSum.sum (f:=fun i=> (bleach (solidify E G b p.threshold r (p:=p)) (X!) z).mean i F) ((bleachPay R! T0 z (fun _=>hz _) zero_le_one hY).heated ha he F).1.hasSum ((bleachPay X T0 z (fun _=>hz _) zero_le_one hX).heated ha he F).1.hasSum).tsum_eq; rw [hQ]; unfold H V X; abel
end YM.QCD.Relight
#print axioms YM.QCD.Relight.arboretum
