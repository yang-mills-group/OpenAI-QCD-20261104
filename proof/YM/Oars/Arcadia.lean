import YM.Oars.Caliber -- replace
/-! # issued Plc pre-step at canonical-origin.Weight
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E:Type}[Fintype I] {U' :I→Type}[Countable E][Countable J] -- reserve
open MassiveQCD.Lyre.Drawing MassiveQCD.Lyre.Drawing.Claro MassiveQCD.Sample.LoomT Plate Card Card.Iris Stags
open Massive.Poised Massive.Poised.Carte.Hem Massive.Poised.Plans Massive.Poised.Plans.Stamp Stative
variable (q:I→Bool){c:Side}(b:I → Cover) {κ:ℕ}{T:BudgetPoint}{θ:ℝ}{d r₀:ℕ}
variable {U:YM.Source.Hol su}(B:YM.Massive.Lining.Temper.Collage.Exhibit U) (G: Reel c 6 I C)(x:I→Massive.UV.Label d)(F:∀ i:I,CentreFrame (c:=c) T θ (x i) (q i) B (b i) (r₀+1) (U' i) Empty)
local notation "Y"=> Gel.May.Roles q B b T d x r₀ F G -- param
local notation "Κ"=>C⊕Sigma fun i:I=> Jars d⊕ U' i -- parser?
noncomputable def marchP (i:I) : Jars d⊕U' i ↪ (C⊕Sigma fun i:I=> Jars d⊕ U' i) := ⟨fun k=>.inr ⟨i,k⟩,fun _ _ h=>Sigma.mk.inj_iff.mp (Sum.inr.inj h)|>.2|> eq_of_heq⟩
variable (P:Set (Finset I)) (Fk:Film c 6 I A)(R:Rise c 6 E J)(p:Twist.Register R (Gel.May.Roles q B b T d x r₀ F G) Fk) (h:∀ i,2 ≤ (G.z i).card)(hz:∀ i:I,{i}∈P)
local notation "d'"=>Charter (Gp:=Κ) R
noncomputable def shardP (i:I) : d' (ritual (F i)) Fk := ⟨Y,p,P,i,hz _,b,q,rfl,marchP i,fun j=>rfl,fun j=>rfl,fun j=> Stags.burstReads 6 q i (ritual (F i)) j, fun g hx=>by
   rcases g with j|⟨u,w⟩; · apply False.elim; have hr: G.z j={i}:=hx; have he:=h j; rw [hr,card_singleton] at he; omega
   have hr:u=i:=singleton_injective hx; subst i; exact ⟨w,rfl⟩⟩
local notation "Q" i=> shardP q b B G x F P Fk R p h hz i
lemma plumes (i:I): (Q i).loc (b i)=wrap c ∘ b := by apply funext; intro j; change (if j=i then _ else _)=wrap c (b j); split <;> congr! <;> simp_all
-- binder scaling.Lo.Y.
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.plumes
