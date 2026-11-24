import YM.Cardinal.Dot
/-! # Differential estimate assertion. Entire output label assembly at predecessor motion
 permit (true before cells, including hard). Use actual Weser incidence counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
-- pre-L frame budget.Norm output group values as weight block. with history.W true physical stats
abbrev weightJ (s:Jars d): ℕ:= s.val.1
def princS (x:Label d)(s:Jars d)(p:BudgetPoint)(t:ℝ):= wealth (gradeCut d s.val x).val p.threshold t
def toted (k:ℝ)(x:Label d)(p:BudgetPoint)(t:ℝ):=∑ i:Jars d,k^(weightJ i)*princS x i p t
/-- Engineering estimate, no cancellation asserted in higher rows. `payer` compares same grade with spin transmission `t₂` (letter value used measuring DIAG, may not be the chosen measurement weight but bounded comparable across). Entire remaining label through total price. -/
structure TypeBeta (u w w' t ε ε' ε₂:ℝ)(v v':BudgetPoint)(x y:Label d) : Prop where
   paid : ∃ W:Jars d→Label d,
      (∀ i, wealth (W i).val v'.threshold w' ≤ ε*u^(weightJ i)*princS x i v w ∧ ∀ e:Rings d, weight e.val ≤ weightJ i→ ‖Stative.fare e (W i).val v'.threshold w'- (u:ℂ)^weight e.val*Stative.fare e (gradeCut d i.val x).val v'.threshold t‖ ≤ ε'*princS x i v w) ∧
      wealth (y-∑ i,W i).val v'.threshold w' ≤ ε₂
-- entry scheduling.K.Edit. Waive PSC.Car.Φ.Act SymbolPort. Capt Table from pre Φ. 
namespace Incidence
local notation "o"=>wrap c b
local notation "GT"=> wealth
local notation "αᶠ"=> K -- remove
variable (P:BudgetPoint) (hk:Pilot H A d m k n j r α β)(ht: Pt.order=m) (hp:Pt.power=k) (Q:Puff c 6 I q)(S:I→Support c)(hQ: Seal 6 (wrap c b) Q)
variable {a₀ a₁ ε₀ ε₁ ε₂ ε₃ ε₄ z z₀ ζ q₀ p₀:ℝ} (J0:Jars d → I) (J₁:E→I) (hi:Injective (Sum.elim J0 J₁))
-- inputs h.Transaction.E cost paid upper Converted.Y.Acc.Hit.Cov exposures. Alloc Pc W.Appointed. Let outputs split.S.T.X.On eligible with residual all entries. Use function predicted.
structure Scenes (H:TaperHol)(Pt P :BudgetPoint)(v t v' t' x₁ eT eT' α₀ α₁ e e':ℝ)(x:Label d) (b:Cover)(Dn Dz :ℕ) : Prop where
    roots (i:I):wrap c b∈S i
    fmt0 (i:Jars d) : ∃ t:ℝ, Flame (Q.fill (J0 i)) Pt (S (J0 i)) (wrap c b) v Dn Dz t ∧ t*Real.exp (α₀*coverNumber Pt.B (S (J0 i))) ≤ eT*x₁^(weightJ i)*princS x i P v' ∧ ∀ y:Label d, ActionTest H b (Q.fill (J0 i)) y.val → ∀ e':Rings d, weight e'.val≤ weightJ i→ ‖Stative.fare e' y.val Pt.threshold v - (x₁:ℂ)^weight e'.val * Stative.fare e' (gradeCut d i.val x).val Pt.threshold t'‖ ≤ e *princS x i P v'
    fmt1 : ∃ f:(i:{u//u∉Set.range J0})→ℝ, (∀ i, Flame (Q.fill i.val) Pt (S i.val) (wrap c b) v Dn Dz (f i))∧ SumBudget (fun i=> f i*Real.exp (α₀*coverNumber Pt.B (S i.val))) eT'
    prep (p:I→Label d) : (∀ i,ActionTest H b (Q.fill i) (p i).val) → SumBudget (fun i:{u//u∉Set.range J0}=> wealth (p i.val).val Pt.threshold v) e'
-- no decomposition.North.An.Marrow addon. Need Real branch readability. Ring variance.
variable (h:Scenes q Q S J0 H Pt P v t φ z z₀ a₀ a₁ u ν ε₀ ε₁ x b n j) -- order likely J0 position. 
include h hi
lemma spends : ∃ f:I→ℝ, (∀ i,Flame (Q.fill i) Pt (S i) (wrap c b) v n j (f i)) ∧ Ac.Hit S Pt.B f u (a₀*toted z₀ x P φ+a₁):=by
   choose g hg hw hQ using h.fmt0; obtain ⟨ℓ,hL,hT⟩:=h.fmt1; let F(i:I):= if h:i∈ Set.range J0 then g (Classical.choose h) else ℓ ⟨i,h⟩; have hf(i:I): Flame (Q.fill i) Pt (S i) o v n j (F i):=by
       unfold F; split
       next hp=> let b:=Classical.choose hp; have he: J0 b=i:=Classical.choose_spec hp; exact Eq.mp (congr_arg (fun a=> Flame (Q.fill a) Pt (S a) o v n j (g b)) he) (hg b)
       next hp=> exact hL ⟨i,hp⟩
   have hJ:Injective J0:=fun i j he=> Sum.inl.inj (@hi (Sum.inl i) (Sum.inl j) he) -- args
   have hx(Ac Cc:ℝ)(f:I→ℝ): (∀ i,0≤f i)→ SumBudget (f ∘ J0) Ac → SumBudget (f ∘ (Subtype.val (p:=fun i=> i∉Set.range J0))) Cc → SumBudget f (Ac+Cc):= by -- arbitrary v.S sig
       intro hF ht hh; let X:= {i//i∉Set.range J0}; let H : Jars d ⊕ X→ I:=Sum.elim J0 Subtype.val; have h1: Bijective H:=by
          refine ⟨fun a b h=>?_,?_⟩
          · rcases a with a|a <;> rcases b with b|b
            · exact congr_arg _ (hJ h)
            · exact (b.2 ⟨a,h⟩).elim
            · exact (a.2 ⟨b,h.symm⟩).elim
            exact congr_arg _ (Subtype.ext h)
          intro i; by_cases he:i∈Set.range J0; · obtain ⟨i,rfl⟩:=he; exact ⟨Sum.inl i,rfl⟩
          exact ⟨Sum.inr ⟨i,he⟩,rfl⟩
       have hk:SumBudget (f ∘ (Equiv.ofBijective H h1)) (Ac+Cc):= Extra.Iteration.Cost.sum ht hh; -- `equiv` f expects hf. 
       refine ⟨hF,?_,?_⟩; exact (Equiv.summable_iff (Equiv.ofBijective H h1)).1 hk.2.1; exact ((Equiv.ofBijective H h1).tsum_eq f).symm.trans_le hk.2.2 -- edit via Summable equivalence
   let L(i:I):= F i*Real.exp (u*coverNumber Pt.B (S i)); have hz i:0≤L i:=mul_nonneg (hf i).sight.travels (Real.exp_nonneg _)
   refine ⟨F,hf,Iris.spend_collect S F (hx _ _ L hz ?_ ?_)⟩
   · refine ⟨fun i=>hz _,Summable.of_finite,?_⟩; rw [tsum_fintype, toted, Finset.mul_sum]; apply sum_le_sum; intro i _; change F (J0 i)*_ ≤ _; unfold F; split
     next ht=> rw [show Classical.choose _=i from hJ (Classical.choose_spec ht)]; exact (hw i).trans_eq (mul_assoc ..)
     next he=> exact (he ⟨i,rfl⟩).elim
   convert! hT using 1; funext i; unfold L; change F i.val * _= _; unfold F; rw [dif_neg i.property]
-- sum arrangements.End envelope.W limits after Calendar.App
include hk ht hp
variable (hZ:1 ≤ v)(hU:0 ≤ u)
include hZ hU
lemma sewing (p:I→Label d)(hh:∀ i, Beacon.ActionTest H b (Q.fill i) (p i).val) (hg: Summable p) : TypeBeta z₀ φ v z (α*a₀) ε₀ ε₁ P Pt x (∑' i,p i):=by
    have hJ:Injective J0:=fun i j he=> Sum.inl.inj (@hi (Sum.inl i) (Sum.inl j) he); refine ⟨p ∘ J0,fun i=>?_,?_⟩
    · obtain ⟨b,h1,h2,h3⟩:= h.fmt0 i; refine ⟨(hk.earn _ _ Pt (p (J0 i)) _ _ v _ ht hp (zero_lt_one.trans_le hZ) h1 (hh _)).trans ?_,h3 _ (hh _)⟩; apply (le_trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right h1.sight.travels (Real.one_le_exp (by positivity : 0 ≤ u * _))).trans h2) (zero_le_one.trans hk.light)) (le_of_eq (by ring))) -- syntax p price.AR.
    let Z:= {u//u∉Set.range J0}; have h1: (∑' i,p i)- (∑ i:Jars d,p (J0 i))= ∑' i:Z,p i.val:=by
         have hx := splice J0 hJ hg; rw [sub_eq_iff_eq_add]; exact hx -- define
    change wealth ((∑' i,p i)- _).val _ _≤ _; simp_rw [Function.comp_apply]; rw [h1]; exact (total_wealth _ (hg.comp_injective Subtype.val_injective)).trans (h.prep _ hh).2.2 -- mismatch comp
 where
   splice (J0:Jars d→I)(hp:Injective J0)(hf:Summable p) : (∑' i,p i)=(∑' i:{u//u∉ Set.range J0},p i.val)+∑ i:Jars d,p (J0 i) :=by
        let X:= {i//i∉Set.range J0}; let H: Jars d⊕X→I:= Sum.elim J0 Subtype.val; have h1: Bijective H:=by
          refine ⟨fun a b h=>?_,?_⟩
          · rcases a with a|a <;> rcases b with b|b
            · exact congr_arg _ (hp h)
            · exact (b.2 ⟨a,h⟩).elim
            · exact (a.2 ⟨b,h.symm⟩).elim
            exact congr_arg _ (Subtype.ext h)
          intro i; by_cases he:i∈Set.range J0; · obtain ⟨i,rfl⟩:=he; exact ⟨Sum.inl i,rfl⟩
          exact ⟨Sum.inr ⟨i,he⟩,rfl⟩
        have he:= (Equiv.ofBijective H h1).tsum_eq p; rw [← he,add_comm]; exact ((hasSum_fintype _).sum (f:=fun i=>p ((Equiv.ofBijective H h1) i)) (hf.comp_injective (i:=Subtype.val) Subtype.val_injective).hasSum).tsum_eq
end Incidence
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Incidence.sewing
