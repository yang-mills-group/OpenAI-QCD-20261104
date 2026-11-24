import YM.Eole.Norm
import YM.Cape.Meg
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
structure Setting (Pt:BudgetPoint)(t:ℝ) :Prop where
      grows i : old i ⊆ a (.inl i)
      gram j: (Y j).place⊆ a (.inr j)
      hugs i : (g i).image o⊆ (Sum.elim old (fun k=> (Y k).place) i)
      corpus i : (tags W g i).image p ⊆ a i
      ear i: (g (Sum.inl i)).Nonempty
      readable i: Measurable (f i)
      mood i: LocalOn (old i) (f (.inl i))
      pays j: UsesFinal Pt.threshold (Y j).place (f (.inr j))
      price i V: Stitch.lights (g i) (Sum.elim old (fun k=>(Y k).place) i) o q (f i V)
      color i U g : parcelColor 6 g I (f i (gauge g U))= f i U
      borne j (x:Grid c): Stitch.Tablet.credits t (f (Sum.inr j) x) ≤ z (Sum.inr j)
      each i j: j∈ g (.inl i)→ Sight (old i) (o j) 2 Pt t (pluck (Keys c 6) (burst q (g (.inl i))) ∘ f (.inl i)) (z (.inl i))
-- names need adorn defs
noncomputable abbrev day (V:Grid c) : E⊕K→ Patio ((Keys c 6)⊕Spine I):= fun i=>f i V
noncomputable def lunar (i:E⊕K) (t:ℝ)(V:Grid c) : Patio ((Keys c 6)⊕Spine I):= match i with
     | Sum.inl j=> masked t (old j) (f (.inl j)) V
     | Sum.inr j=> f (.inr j) V
noncomputable def night(t:ℝ)(V:Grid c): E⊕K→ Patio ((Keys c 6)⊕Spine I):=fun i=>lunar old f i t V
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
lemma up_support(i:E⊕K) : Sum.elim old (fun j=>(Y j).place) i ⊆ a i:=by cases i; exact h.grows _; exact h.gram _
lemma packet (s:Finset N)(hs:spark (tags W g) s) : Ac.Spark a s:=by
    refine spark_ac (tags W g) a hs (fun i hi j hj=>?_); intro ⟨k,hk,hg⟩; exact ⟨p k,h.corpus i (mem_image_of_mem _ hk),h.corpus j (mem_image_of_mem _ hg)⟩
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
noncomputable abbrev shore (i: Finset (E⊕K)):= i.biUnion a
noncomputable abbrev journal (i:Finset (E⊕K)): Grid c→ Mt:= fun V=> reward W g q (day f V) i
noncomputable abbrev lunarZ (i:Finset (E⊕K))(t:ℝ): Grid c→ Mt:= fun V=> reward W g q (night old f t V) i
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
lemma rays (i:Finset (E⊕K)) : (glowT W g i).image p⊆shore a i:=by
    rw[← tiles]; intro j hj; obtain ⟨x,hx,rfl⟩:=mem_image.mp hj; obtain ⟨k,hk,hx⟩:=mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨k,hk,h.corpus k (mem_image_of_mem _ hx)⟩
lemma readings (s:Finset N): UsesFinal T (shore a s) (lunarZ W g q old f s T):=by
    have hh_i(i) : UsesFinal T (a i) (fun U:P₀=> H' U i):=by
            apply Work.H03.reads_larger (up_support W g Y q o p old a f z h i); cases i with
            | inr j=> exact h.pays j
            | inl i=> exact Cape.MaskR _ _ (h.mood i)
    intro i j hi hx; exact congr_arg (Bloc.lane κ q W (glowT W g s)) (prod_congr (f:=H' i) rfl fun k hk=> Work.H03.reads_larger (subset_biUnion_of_mem _ hk) (hh_i k) _ _ hi hx)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.packet
#print axioms YM.MassiveQCD.Sample.Eole.readings
