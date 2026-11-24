import YM.Cape.Fountain
import YM.Cape.Seize
/-!
# Caret. Geometric scopes for pure value anchors
 Validated reads at given native field exactly.
 Keep separate costs. Mark uniqueness even when many flag distributions exist.
 Pre-State publication at entry.[α and h_]
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch Creek SC FlareV
open QCD.Acre Rails Struck Struck.Library Carrier
open QCD.Jets.Touch Apron Apron.Grove Play Anomaly Bera
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius -- no ambiguity
variable {c f:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I] {l φ k B P A A':ℕ} {v α s t:ℝ}
variable (p:I→Site c)(q:I→Bool)(T: Finset (Finset I))(M: Patron.Rail c N U) (E: Reel c N I J)
def innerT (l:ℕ):= (2*l+1)*200
def orbital (l:ℕ):= 6*innerT l
def majorT (l:ℕ):=2*orbital l
def refuge (l:ℕ):=innerT l*3
abbrev baseTZ (b:ℕ):= (10*b+45*b)
def cups (b:ℕ)(V:Finset I):Support c:= halo b (V.image p)
lemma cups_eq (b:ℕ)(V: Finset I): cups p b V= V.biUnion (Camp.Ray p b) :=by
    ext j; unfold cups; rw [halo_spec]; constructor; rintro ⟨i,hi,hp⟩; obtain ⟨i,hi0,rfl⟩:=mem_image.mp hi; exact mem_biUnion.mpr ⟨i,hi0,(Camp.portion ..).mpr hp⟩
    intro h; obtain ⟨i,hi,h⟩:=mem_biUnion.mp h; exact ⟨_,mem_image_of_mem _ hi,(Camp.portion ..).mp h⟩
lemma subray (a:ℕ)(o x:Site c)(r s:ℕ)(h:separation o x ≤ a)(hp:a+r ≤ s) : halo r {x}⊆ halo s {o}:=by
    intro y hy; obtain ⟨z,hz,hv⟩:=halo_spec.mp hy; rw [mem_singleton.mp hz] at hv; exact halo_spec.mpr ⟨_,mem_singleton_self _,((separation_triangle ..).trans ((Nat.add_le_add h hv).trans hp))⟩
lemma puff (R:Ratio c f)(p:I→ Site f)(l B Q:ℕ)(h:0<B)(hp:Q≤2*B)(hk: 20*majorT l ≤R.count.val)(i:I) : (halo (majorT l*Q) {p i}).image R.parent⊆Camp.Ray (R.parent∘p) (10*B) i:=by
    intro j hj; obtain ⟨v,hv,rfl⟩:=mem_image.mp hj; obtain ⟨z,hz,hv⟩:=halo_spec.mp hv; rw [mem_singleton.mp hz] at hv; apply (Camp.portion ..).mpr
    refine Nat.le_of_mul_le_mul_left ((Corona.foreshorten R _ _).trans (Nat.le_trans (Nat.add_le_add_right (hv.trans (Nat.mul_le_mul_left _ hp)) _) ?_)) R.count.pos
    calc majorT l*(2*B)+ ↑R.count ≤ R.count.val*B+R.count.val*B:=Nat.add_le_add (by nlinarith) (by nlinarith [R.count.pos])
         _≤_ := by nlinarith
-- no std basis selection. Syntactic boosts.Warm. NOTE final readout on whole compound parent may need A support in Booth. hence explicit pay for even if i not emitting.
structure Vault (T:Finset (Finset I)) (Ζa : Finset J) (B l m:ℕ) : Prop where
    mug : Set.InjOn E.z ↑Ζa
    arcs i : i∈ Ζa→ (E.z i)∈T ∧ Ac.Spark (Camp.Ray p (baseTZ B)) (E.z i)
    brood i : i∈Ζa →∀ j∈ E.z i, (E.addr i).support ⊆ halo (majorT l*B) {p j}
    -- final read at unitE. request.S given at every mark at least namespace. ∀ marker
    shield i : i∈Ζa→ ∀ j∈E.z i, halo (refuge l*B+10) {p j}⊆(E.addr i).support
    domain i : i∈Ζa →∀ j∈ E.z i, LocalOn (↑(halo (innerT l * B) {p j}):Set (Site c)) (E.mark i) -- compensates final gauge extension
    degree i : i∈Ζa→ ∀ V:Grid c, (E.mark i V).val ∈ Rim univ ((E.z i).card*m)
-- budget w either Booster ξ or 1. pure exact w even if Λ changes choose absorb. 
local notation "Bq"=> (3/32:ℝ)
variable (Γ: Finset J)
noncomputable def boosts (Λ:ℝ)(i:J):= if i∈Γ ∨ E.z i∉ T then (1:ℝ) else Λ -- ensure Λ>1
structure Bearing (L:Side)(l m:ℕ) (v y Λ:ℝ) (P:BudgetPoint)(t:ℝ) (F: Film c N I D): Prop where
    rise: Vault p E T Γ P.B l m
    boost : SC.Valve E p q v P.threshold P.B Bq t (boosts T E Γ Λ)
    flag : Film.Beat N p q F P.threshold
    cost : Film.Stock N F P.B (taxK L y (31/32)) Bq v (taxK L y (1/64))⁻¹ (fun _=>1)
-- pollutant slot read off-grid interpolation pressure.A. root center tile # sign.Nusp. uniform phase.D hands.
lemma brood_unit (p:I→Site c)(B l:ℕ)(h:∀ i∈ T,i.card≤ l)(hb:0<B)(j:parish p T (baseTZ B))(i:I)(hi:i∈j.val):
       separation (rayA p T _ (orbital l*B) j).site (p i) ≤ l*(110*B):=by
     refine (Camp.ridgeSpan p j.val _ j.2.2 _ i j.2.2.1.choose_spec hi).trans ?_; unfold baseTZ; specialize h _ j.2.1; nlinarith
lemma configurationD (l B:ℕ)(hp:0<B):
   let x:=10*B; let D:= innerT l*B;
   l*(2*(x+45*B))+(x+45*B)+4 ≤ (l*110+60)*B ∧
   l*(110*B)+(l*110+60)*B ≤ D ∧
   D+l*(110*B) ≤ refuge l*B ∧
   l*(110*B)+(refuge l*B+10) ≤ orbital l*B ∧
   l*(110*B)+orbital l*B≤ majorT l*B ∧ 55*B ≤ majorT l*B:=by
   unfold majorT orbital refuge innerT; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>nlinarith
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.configurationD
