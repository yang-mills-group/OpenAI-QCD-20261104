import YM.Hank.Beta
/-!
# Quantitative pricing of bare suffix translation in stride two.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix ComplexOrder
namespace Romance.HankV
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n r t m:ℕ}{c f:Side}
variable (C: Regulator c 6) (T: Cells.Cut c) (a:Cover)
local notation "X"=> Insertion c 6
local notation "Q"=> T.sector
local notation "S"=> banner
local notation "Θ"=> picture T C.zeroCut
local notation "Pv"=>C.average
local notation "L" => plot C T
variable (hq:C.t=0)(hk:T.kind=.link)(ht:0 ≤ C.β)(hp:2≤ T.half.val)(hz:0 < C.Z) (ha:T.flip.act a= -a)
local notation "uK"=> Complex.I
variable {B D:ℝ}
local notation "xK"=> tidal a
include ha hq hk hz ht hp

-- apply to prefix/suffix glued translated within two-step parity cosets
lemma paintsM (x y:X)(Z W:X)(he: Θ x= Z) (hv: tidal a y (2*i)=W)(hX:Budget C T a x n B)(hY:Budget C T a y n B)(hK:0<k)(h:k ≤ i)(hx: i+d+k ≤ n): ‖Pv (Z * banner ((2*d) • a) W)-Pv (Z*W)‖ ≤ d*(4*B/(k:ℝ)):=by
    let Y:=Z; rw [←hv,← he,show banner _ (tidal a y (2*i))=_ from (show banner ((2*d) • a) (tidal a y (2*i))=tidal a y (2*(i+d)) from (by unfold tidal; rw [order_cast,mul_add,add_smul]))]; exact hankel C T a hq hk ht hp hz ha x y hX hY hK h hx
-- convenient centered shift. To arrange floors.Pos shift origins both closer than actual. hK=margin half units. Need carpets at all j. Kernel ⟮θX)Y moves.
lemma paceM (z y:X)(b:ℕ)(hb:1≤b)(hw:d≤ b) :
    let x:= picture T C.zeroCut z
    let XK:= banner (-(b • a)) x
    let Y:= banner (-(b • a)) y
    Budget C T a XK (4*b) B→ Budget C T a Y (4*b) B → ‖Pv (z* banner ((2*d) • a) y) - Pv (z*y)‖ ≤ d*(4*B/(b:ℝ)):=by
    -- Hankel vertical plot projected from translating both XK,Y. At k=b. Calculate first target exactly.
    intro x Xk Yk hX hY
    have he': tidal a Xk b=x:=by unfold Xk tidal; rw [order_cast,neg_add_cancel, order0]
    have he: Θ x=z:= pictured ..
    have hm:tidal a Yk b=y:=by unfold Yk tidal; rw [order_cast, neg_add_cancel,order0]
    have h(j:ℕ): L Xk (xK Yk (b+j))= Pv (z* tidal a Yk j):=by rw [← plot_add C T a hq hk ha,he', plot,he]
    have hs: banner ((2*d) • a) y=tidal a Yk (b+2*d):=by nth_rw 1 [←hm]; unfold tidal; rw [order_cast,add_smul]
    rw [hs,← h, show Pv (z*y)= Pv (z*tidal a Yk b) from (by rw [hm]), ← h,show b+(b+2*d)= 2*(b+d) from by omega, show b+b=2*b from by omega]; exact hankel C T a hq hk ht hp hz ha _ _ hX hY hb le_rfl (by omega)
-- x/y hypotheses cost over placements.Point.A.So.S spectral.
end HankV
end Romance
end YM.Massive
#print axioms YM.Massive.Romance.HankV.paceM
