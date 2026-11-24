import YM.Poised.Amber
/-!
 # Projection display size, relative orientation. Small requires BOTH input readability and output Small; explicit gate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k n:ℕ}{c l:Side}
namespace Landing
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource
open Counting Counting.Click Display Costs Sieve Chute PhysicalNext.Repeat PhysicalNext.Repeat.Brim MassiveQCD.Plate Lining.Temper Collage Carte.Hem Papyrus
variable {X:Support l}{Y:Support c}{o :Site l}{a b:Cover}{d d₀ e p q m i:ℕ}{R:Ratio c l}
lemma changeC (L:Side)(x y: Cover): Laurent.size (cellar L x-cellar L y) ≤ Laurent.size (x-y):=by
    have he:= Work.F08.carry_spec (wrap L y) (x-y); rw [Work.F08.arrives, map_add,map_sub,wrap_lift,add_sub_cancel] at he -- cancellation formula?
    let p:= Work.F08.carry (wrap L y) (x-y); have h:L.val • (cellar L x-cellar L y)= L.val • p:=by have ht:=balance L x; have hu:=balance L y; change L.val • _= _; calc
        _= (x-lift (wrap L x))-(y-lift (wrap L y)):=by rw [smul_sub]; exact congr_arg₂ (·-·) (by nth_rw 2 [ht]; abel) (by nth_rw 2 [hu]; abel)
        _= (lift (wrap L y)+(x-y))-lift (wrap L x):=by abel
        _= L.val • p:= by rw [he]; abel
    have hv : cellar L x-cellar L y=p:= (smul_right_injective Cover L.pos.ne') h -- check lemma
    rw [hv]; exact Work.F08.carry_size ..
lemma passport (R:Ratio c l)(b a:Cover)(X:Support l)(Y:Support c)(B B':ℕ)(q:ℕ)(u v:ℕ)(ht:wrap l b∈X)(he:Laurent.size (cellar R.count b-a) ≤ p)(hx:coverNumber B X≤ q)(hy:coverNumber B' Y≤ m)(h₁: R.parent (wrap l b)∈Y) (hs:∀ x∈X, Lattice.halo (u+1) {R.parent x}⊆ Y) (hz: 100≤c.val)(hV:4*(q*(4*B+2)+2*B)+p ≤ v) (hY:10*(m*(4*B'+2)+2*B'+p)<c.val) (hU: 2*(v+u)< c.val)(hX:10*(q*(4*B+2)+2*B)< l.val): Cruising R X Y b a u v:=by
    let D:=q*(4*B+2)+2*B; have h i (hi:i∈X) :separation i (wrap l b)≤D:=(Corona.extent X B hi ht).trans (add_le_add_left (Nat.mul_le_mul_right _ hx) _)
    refine ⟨?_,hU,hz,hz.trans (le_trans ?_ R.exact_size.ge),fun i hi=> lt_of_le_of_lt (Nat.mul_le_mul_left _ (h i hi)) hX,fun i hi=>?_,hs⟩; rotate_left
    · simpa only [mul_comm] using Nat.le_mul_of_pos_right c.val R.count.pos
    · have ht : separation (R.parent (wrap l b)) (wrap c a)≤p:= by rw [Streets.owner]; exact (cost_p ..).trans he
      have hp:= (separation_triangle i (R.parent (wrap l b)) (wrap c a)).trans (add_le_add ((Corona.extent Y B' hi h₁).trans (add_le_add_left (Nat.mul_le_mul_right _ hy) _)) ht)
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hp) hY
    intro x hx; apply le_trans _ hV; let f:=plinth b x; have he' : (cellar R.count f-a)= cellar R.count f-cellar R.count b+(cellar R.count b-a):=by abel
    rw [show plinth b x=f from rfl,he']; refine (size_add ..).trans (add_le_add ((changeC ..).trans ?_) he); unfold f plinth; rw [add_sub_cancel_right]; unfold Beacon.offset; refine (sum_le_sum (f:=fun i:Axis=>(lift (x-wrap l b) i).natAbs) (g:=fun _=>D) (fun i _=>(component_le _ i).trans (h _ hx))).trans_eq ?_; simp [Axis,D]
-- rate. wrappers later
end Landing
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Landing.passport
