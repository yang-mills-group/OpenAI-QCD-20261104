import YM.MassiveQCD.Relight.Wax
import YM.MassiveQCD.Festival.Park
import YM.QCD.Finch.Dad
import YM.MassiveQCD.Relight.Whirl
import YM.QCD.High.Coins
/-! # Colored Charge interfaces for re-expression after mass accounting
 Must enter `Hill` Step at coarser tick, carrying genuine all-power budgets & reflection masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival
variable (Y:Ruby.Hue c N I)(X G:Gem c N I)(v:I→ℕ)(s:ℕ→ℂ)
local notation "K*"=> v ∘ Prod.snd
-- integration income. apply hs.S.
open Shells Shells.Warmlet Finch Stem Grove Calm
lemma wired (r:ℝ)(h:RotationE X v): RotationE (flightE X r) v:=by
    let U:=wearK c N r; constructor
    · refine ⟨fun i p z=> congr_arg Subtype.val (show sways (Lat.rotates N z) (U (X.view i (Lattice.gauge z p)))=U (X.view i p) from ?_),fun i V W hz=>(purity _ _ r).trans (congr_arg U (h.notes.num i V W hz)),fun i V=>(dearR (X.view i V) r).trans (congr_arg U (h.notes.real i V))⟩
      exact (purity _ _ r).trans (congr_arg U (Subtype.ext (h.notes.gauge i p z)))
    intro s k p hp; obtain ⟨e,h⟩:=h.turnsK s k p hp; refine ⟨e,fun i=> ⟨(h i).1,(h i).2.1,fun V=>(purity _ _ r).trans (congr_arg U ((h i).2.2 V))⟩⟩
noncomputable def flightY (Y: Ruby.Hue c N I)(r:ℝ): Ruby.Hue c N I:= ⟨Y.bud,fun i V=> wearK c N r (Y.mean i V)⟩
lemma wisedY (h:Yank Y v): Yank (flightY Y r) v:=by
    let U:=wearK c N r; refine ⟨⟨fun i p z=> congr_arg Subtype.val (show sways (Lat.rotates N z) (U (Y.mean i (Lattice.gauge z p)))=U (Y.mean i p) from ?_),fun i V=> (dearR (Y.mean i V) r).trans (congr_arg U (h.real i V)),fun i V W hz=> (purity _ _ r).trans (congr_arg U (h.fit i V W hz))⟩,?_⟩
    · exact (purity _ _ r).trans (congr_arg U (Subtype.ext (h.gauge i p z)))
    intro s k p hp; obtain ⟨e,h,hp',hY⟩:= h.glamour s k p hp; exact ⟨e,h,hp',fun i V=> (purity _ _ r).trans (congr_arg U (hY i V))⟩
lemma warmedY (h:Wax Y p.threshold p.B a T t)(ht:0<r)(he:0<σ)(hc:r*σ ≤ t): Wax (flightY Y r) p.threshold p.B a T σ:=by
    let W:= wearK c N r; obtain ⟨f,hf,hQ⟩:= h.expense; refine ⟨⟨fun i x y hx hv=> congr_arg W (h.burns.bond i x y hx hv),fun i=> ((songT (c:=c) (N:=N) r).continuous.measurable.comp (h.burns.meas i)),fun i V hr=>h.burns.non i V (fun hz=>hr ?_),fun i V=> dings _ _ _ (h.burns.lives i V)⟩,f,hf,fun i V=> (quy _ _ _ _ ht he hc).trans (hQ i V)⟩ -- check quy
    · exact (congr_arg W hz).trans (map_zero W)
-- choose λ all
lemma wing (r:ℝ): flightE (weight X v s) r=weight (flightE X r) v s:=by unfold weight flightE; congr 1; funext i V; exact map_smul (wearK c N r) _ _
lemma wingY (r:ℝ): flightY (bleach Y v s) r=bleach (flightY Y r) v s:=by unfold bleach flightY; congr 1; funext i V; exact map_smul (wearK c N r) _ _
lemma wings (r:ℝ)(U:Grid c)(h:Summable fun i=>Y.mean i U): HasSum (fun i=>(flightY Y r).mean i U) (wearK c N r (swarm Y U)) := (songT r).hasSum h.hasSum
lemma bleachMin (h: Purchases Y p.threshold p.B u T t): Wax Y p.threshold p.B u T t:=by obtain ⟨f,hf,hQ⟩:=h.paint; exact ⟨h.life, f,hQ,hf⟩
-- 
lemma soul (hp: Y.Garish) (n:ℕ):Yank Y (fun _=>n):=by
    refine ⟨⟨hp.gauge,hp.real,fun j U=>AccentFit.of_fit (hp.number j U)⟩,fun s k g h=>?_⟩; obtain ⟨e,h,h'⟩:=hp.travel _ _ _ h; exact ⟨e,h,fun _=>rfl,h'⟩
end YM.QCD.Relight
