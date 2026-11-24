import YM.Alum.Pulp
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet.Sworn
variable {k:ℕ}{n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola
variable {I:Type}[Fintype I](Q:I→Bool)(X:I→Stud n F) (hp:∀ i V,Hom (Q i) (X i V))
variable (u:I→ℕ)(p: I→ E4)(f:Fin k→I)
open Quills.Clover YM.Arise.Bill YM.Arise.Count Play Play.Chamber
variable (B:∀ i:I,Cups (u i) (Q i))
-- literal future projection operator inverse.L.Pr.Utility applies not junk markers.Phases vac. Orth.
variable (R:Regulator n F)(T:Tiling n)(C:T.Cell)
include hp
lemma literal (hP:Set.InjOn p (crest f))(ht:Injective f): (List.ofFn (X ∘ f)).prod= UV.Free.moment (u∘f) (points (p∘ f)) (fun i=>meaning _ _ (B (f i))) • (1: Stud n F)+ ∑ i∈(crest f).powerset.erase (crest f), saves Q u B p f i • (Sworn.readL Q (List.ofFn (tour ((crest f) \ i))) u p B X hp):=by
      funext W; rw[Pi.add_apply, Finset.sum_apply]; simp_rw [Pi.smul_apply]; apply Eq.trans ((songX n X f W).symm); exact Clover.inverse_l (A:=Keys n F) Q u B p (fun i=>X i W) (fun i=>hp i W) f hP ht
variable (e H:ℝ)
omit hp
lemma pawn (P:Stud n F)(hx:Fence (T.chamber C) P)(he:Potion P)(hz:Smoke T R): ‖valueH R P‖ ≤ topH T R P C:=by
     have ht:= wardsP (A:=Unit) T R hz.seam (fun _=> P) (fun _=> C) (injective_of_subsingleton _) [()] (by simp) (by simp) (fun _=>⟨hx,he⟩) hz.real hz.pos hz.cycle hz.energy; simpa using ht
-- pure moments closeness on one request.T.S. compile align.Armanent.H if use.Apply Any Ψ cap. Later exterior.Power.
include hp
lemma mflower (hP:Set.InjOn p (crest f))(ht:Injective f) (hz:Smoke T R)(he:0 ≤ e) (hh:0 ≤H)(hk:∀ i∈(crest f).powerset.erase (crest f), ‖saves Q u B p f i‖ ≤ H)(hX:∀ i∈(crest f).powerset.erase (crest f), let t:=Sworn.readL Q (List.ofFn (tour ((crest f)\ i))) u p B X hp; Fence (T.chamber C) t ∧ Potion t ∧ topH T R t C ≤ e): ‖valueH R (List.ofFn (X∘f)).prod- UV.Free.moment (u ∘ f) (points (p∘f)) (fun i=> meaning _ _ (B (f i)))‖ ≤ (2:ℝ)^Fintype.card I * (H*e):=by
       let M:= UV.Free.moment (u ∘ f) (points (p∘f)) (fun i=> meaning _ _ (B (f i)))
       let x:= M • (1:Stud n F); let s:= (crest f).powerset.erase (crest f); let p'(i:Finset I):= saves Q u B p f i; let z(i: Finset I):= Sworn.readL Q (List.ofFn (tour ((crest f)\i))) u p B X hp; let y(i:Finset I):= p' i • z i; have hy(i)(hi:i∈s):= ((hX i hi).1.mass (p' i)).hp
       rw [literal Q X hp u p f B hP ht]; change ‖valueH R (x+ ∑ i∈s, y i)-M‖ ≤ _; have hx:Tide.Stays x:= (Fence.mass (Fence.one (A:=T.chamber C)) M).hp
       rw [spentA R hx (sumsA s y hy),sumsV R s y hy,show valueH R x=M from (by unfold x; rw[spend,blank R hz.energy]; simp),add_sub_cancel_left]
       apply (norm_sum_le ..).trans; have hb:s.card≤2^Fintype.card I:= (Finset.card_le_card (Finset.erase_subset (crest f) _)).trans (le_trans (le_of_eq (Finset.card_powerset _)) (Nat.pow_le_pow_right (by norm_num) (Finset.card_le_univ (crest f))))
       refine (sum_le_sum (g:=fun _=>H*e) (fun i hi=>?_)).trans (?_); · unfold y; rw [spend,norm_smul]; exact mul_le_mul (hk i hi) ((pawn R T C _ (hX i hi).1 (hX i hi).2.1 hz).trans (hX i hi).2.2) (norm_nonneg _) hh
       rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (mul_nonneg hh he)
end Goblet.Sworn
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.Sworn.mflower
#print axioms YM.Massive.Lyre.Goblet.Sworn.pawn
