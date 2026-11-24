import YM.Eole.Glow
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
local notation "ξ"=> Stitch.Tablet.credits
local notation "w0"=> wag
variable (hv:0<t)
include hv
lemma gold1 : ξ t (1:Patio (Keys c 6⊕ Spine I))=1:=by unfold Stitch.Tablet.credits; rw[map_one,Cove.load_one]
local notation "R!" i:arg=> ((1+ (wag (shore a i) P.B:ℝ))^P.power)
local notation "Q"=> P.order
lemma saturn (i:Cand W g Y)(x:Grid c)(hx:Healthy T (shore a i.val) x)(r:Site c)(ht:r∈shore a i.val) (u:Finset (E⊕K))(hU:u⊆i.val) : Phy t (∏ j∈u,f j) x (P.dirBound r) P.order (∏ j∈u,z j) (1+(u.card:ℝ)* R! (i.val)):=by
      induction u using Finset.induction_on with
      | empty=> rw [Finset.prod_empty,Finset.prod_empty,card_empty,Nat.cast_zero,zero_mul,add_zero,← gold1 W g Y q o p old a f z h hv]; exact Phy.fixedX (U:=x) _ (by rw [gold1 W g Y q o p old a f z h hv]; positivity)
      | insert j u hj ih=>
           have hz:=ih ((subset_insert ..).trans hU); let E' := R! (i.val); have hV': Phy t (f j) x (P.dirBound r) Q (z j) E':=by
                have hs:= hU (mem_insert_self ..); cases j with
                | inr j=> exact False.elim (i.2.2 ⟨j,mem_toRight.mpr hs⟩)
                | inl j=>
                   obtain ⟨v,hv'⟩:=h.ear j
                   have hp:old j⊆ shore a i.val:= (h.grows _).trans (subset_biUnion_of_mem _ hs)
                   have hr:= hp (h.hugs (.inl j) (mem_image_of_mem _ hv')); have hW:=Corona.extent (shore a i.val) P.B hr ht
                   exact turner (chartA q _ _ (fun V=> (h.price (.inl j) V).1) x (hx.mono_left hp) (h.each j v hv') hv) (Nat.cast_le.mpr hW)
           have hX:= rotated hV' hz; rw [prod_insert hj,prod_insert hj, Finset.card_insert_of_notMem hj,Nat.cast_add,Nat.cast_one]
           rw[show 1+_* E'=E'+(1+(u.card:ℝ)*E') from (by ring)]; exact hX -- not find.E'
local notation "Ω"=> journal W g q f
noncomputable abbrev heightE (k:ℕ)(f:E⊕K→ℝ)(j:E⊕K):ℝ:= (2:ℝ)^k * f j
noncomputable def payU (Y:Support c)(x:ℝ)(P:BudgetPoint):ℝ:= (1+(wag Y P.B:ℝ))^(2+P.power*P.order)*x
local notation "ω" i:arg=> payU (shore a i) (∏ j∈i,heightE P.order z j) P
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.saturn
