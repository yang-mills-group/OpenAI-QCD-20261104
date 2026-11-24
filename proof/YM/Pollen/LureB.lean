import YM.Pollen.Aspens
import YM.Pollen.Story
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c 6→L[ℂ]Fields c 6) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Z"=>Keys c 6
open ConnectedActivityE6 Blaze King
local notation "K"=> wag
local notation "T"=>Stitch.Tablet.credits
variable {J K':Type}
open Cape
local notation "H'"=> withdraw 6 o t
local notation "Q'" X:arg=> shutter Z X
structure CarryT (p:I→Site c)(R:Reel c 6 I D)(Y:Cape.Lure c 6 I J)(U:BudgetPoint)(t w a b:ℝ)(P': Set (Finset I))(X:Grid c→Patio (Keys c 6⊕Spine I)):Prop where
    earn : R.Occupant p (traceI I) t U 2 w a (fun _=>1)
    wax : Wax (Cape.vesta p Y t) U.threshold U.B w b t
    lit : Lure.On p (traceI I) Y U.threshold
    take : ∀ i∈ P',∀ V, shutter (Keys c 6) i (X V)=shutter (Keys c 6) i (Reel.rope R U.threshold V+withdraw 6 p t (swarm (Cape.vesta p Y t) V))
noncomputable def plusLure (A:Lure c 6 I D)(B:Lure c 6 I J):Lure c 6 I (D⊕J):=⟨Sum.elim A.spot B.spot,Sum.elim A.wick B.wick,Sum.elim A.f B.f⟩
variable {I₁ I₂:Type}
variable {C A A' B':ℝ}{P':Set (Finset I)}{X0 Y0:Grid c→Patio (Keys c 6⊕Spine I)}
-- p wrap.L.Caption. use general union Occup lemma by exhibiting Lift wrap. simpa once.
omit [Fintype I] in
lemma lifts (o:I→ Site c): o=wrap c ∘ (fun i=> Lattice.lift (o i)):= funext (fun i=> (wrap_lift _).symm)
open Iris
lemma plusE (R:Reel c 6 I D)(S':Reel c 6 I I₁)(X:Lure c 6 I J)(Y':Lure c 6 I I₂)(h:CarryT o R X U t w A A' P' X0)(he:CarryT o S' Y' U t w C B' P' Y0)(ht:0≤ w)(hp:1≤ t) : CarryT o (addReel 6 R S') (plusLure X Y') U t w (A+C) (A'+B') P' (X0+Y0):=by
    let r:= plusLure X Y'; let y:= Cape.vesta o r t; have hx:= h.wax; have hv:= he.wax; have hf:y=Ruby.HJoin (Cape.vesta o X t) (Cape.vesta o Y' t):=by unfold y r vesta plusLure Ruby.HJoin; congr 1; funext i; cases i <;> rfl -- mean equality pointwise case split
    refine ⟨?_,(show Wax y _ U.B w _ t from hf.symm ▸ reach_w hx hv),?_,fun i hi V=> ?_⟩
    · let k:=fun i=> Lattice.lift (o i); have hy₁:=h.earn; have hy₂:= he.earn; rw [lifts o] at hy₁ hy₂ ⊢; exact Gel.May.jointlyEarn q k U _ _ hy₁ hy₂ le_rfl
    · constructor
      · rintro (i|i); exact h.lit.lend i; exact he.lit.lend i
      · rintro (i|i); exact h.lit.meas i; exact he.lit.meas i
      · rintro (i|i); exact h.lit.expense i; exact he.lit.expense i
      · rintro (i|i); exact h.lit.shades i; exact he.lit.shades i
      · rintro (i|i); exact h.lit.paint i; exact he.lit.paint i
      · rintro (i|i); exact h.lit.stamp i; exact he.lit.stamp i
      · rintro (i|i); exact h.lit.enough i; exact he.lit.enough i

    rw [Pi.add_apply,map_add,h.take i hi V,he.take i hi V]; rw [show Reel.rope (addReel 6 R S') U.threshold V=_ from (unionR R S' V (tip _ _ R _ h.earn ht hp) (tip _ _ S' _ he.earn ht hp)).2]; change _= (Q' i) (_+H' (swarm y V)); rw [hf, show swarm (Ruby.HJoin ..) _= _ from (show swarm (Ruby.HJoin (Cape.vesta o X t) (Cape.vesta o Y' t)) V=swarm (Cape.vesta o X t) V+swarm (Cape.vesta o Y' t) V from HasSum.tsum_eq ((hx.heated hp ht V).1.hasSum.sum (hv.heated hp ht V).1.hasSum)),map_add H']; rw [←map_add (Q' i)]; congr 1; abel
include H
-- general hom version
variable (F:Reel c 6 I D)(f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
variable (hs:s.Nodup)(hc:0 ≤a) (hx:0 ≤ x)(hp:0<t)(hd:∀ i,‖d i‖ ≤x)
local notation "Q" X:arg=> shutter Z X
variable (Ft:ℕ)(ε ζ C:ℝ)(he:Ac.Hit (fun i:D=> (F.addr i).support) U.B g ζ C)(hK:Fires o Ft)(he0:0<ε)(hA:0 ≤ b)(hW:b+3*ε ≤ ζ)
local notation "V'"=>mCash U.B U.power U.order Ft ε b (a*x)
variable (hΦ:hullP U.B Ft*(Real.exp (b+ε)*(a*x*2^U.order))≤ ε) (paid:Bool) (hX:∀ i∈ P',Spaced o i U.B)(hT:1 ≤ t)(hC':1 < U.B*U.B)
include h hs hc hx hp hd he hK he0 hA hW hΦ hX hT hC'
local notation "λX"=> domeE o V H d s F paid
local notation "B!" U':arg i:arg=> oldMask paid ((F.addr i).support) U.threshold (F.mark i) U'
noncomputable abbrev deltaU (X:Grid c→ P) : Grid c→P:= fun x=> (Ω x) s (X x)-X x
local notation "A_"=> deltaU o V H d s
lemma adoption (hP:paid=true→∀ i X,Stitch.Tablet.credits t (F.mark i X) ≤ g i)(h₀:∀ v:Grid c,HasSum (fun i=> oldMask paid ((F.addr i).support) U.threshold (F.mark i) v) (X0 v)): CarryT o (etherU o V H d s F) λX U t b (V'*C) (V'*C) P' (deltaU o V H d s X0):=by
    refine ⟨mossy o V H d s F f g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ,wearsA o V H d s F f g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ paid hP,relents o V H d s F f g h paid,fun i hi X=> ?_⟩
    have he:= canopyU o V H d s F f g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ paid X i (hX i hi) hC' hT hP (h₀ X).summable
    unfold deltaU; rw [← (h₀ X).tsum_eq,map_sub,he,add_assoc,map_add]; abel
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.plusE
#print axioms YM.MassiveQCD.Sample.Basal.adoption
