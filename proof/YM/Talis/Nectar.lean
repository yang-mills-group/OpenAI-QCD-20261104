import YM.Talis.Harvest
import YM.Talis.Palm
import YM.Lyre.Bloom
import YM.Lyre.Story
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter QCD QCD.Lat QCD.RP QCD.Tide QCD.Grass Lattice Wilson NormedSpace
open Chess Cells Romance Plum Finset
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {A:Type*}{F:ℕ}{n:Side} (T:Cells.Tiling n)(R:Regulator n F)
open YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis
variable (x:Stud n F)(g:T.Cell)(X:T.Cell → Stud n F) (hX:∀ i,SignedEq (palmH T x g i) (X i))
include hX
lemma apportion : SignedEq (loom T (palmH T x g)) ((univ.toList.map X).prod):=by
      let p':=palmH T x g
      suffices h:∀ l:List T.Cell,SignedEq (l.map p').prod (l.map X).prod from h _
      intro l; induction l with| nil=> exact SignedEq.refl _|cons a l ih=> exact signsM (hX a) ih
variable (u v:ℝ){Y W:ℝ}(c k:ℕ)(hW: W ≥0)(hu:0<u)(hv:0<v)
local notation "Car"=> Fintype.card (T.Cell)
-- use r reserve Holding.Left.Nonempty cells ensures.
include hW hu hv
lemma narrower (hm:0<Car)(hp: Y^Car ≤(u*v)^k* W^Car)(hx:‖valueH R (univ.toList.map X).prod‖ * (u*v)^k ≤ Y^Car) : topH T R x g ≤ W:=by
      rw [←signsV R (apportion T x g X hX),← top_power] at hx; have hV:(topH T R x g)^Car*(u*v)^k ≤ W^Car*(u*v)^k:= hx.trans (hp.trans_eq (mul_comm ..)); rw [mul_le_mul_iff_of_pos_right (pow_pos (mul_pos hu hv) k)] at hV; exact le_of_pow_le_pow_left₀ hm.ne' hW hV
lemma faster (hu0:Car ≤ k)(hp:1 ≤ u*v) (he: Y ≤ u*v*W) (hY:0 ≤ Y) (hT:0<Car)(hx:‖valueH R (univ.toList.map X).prod‖*(u*v)^k ≤ Y^Car) : topH T R x g ≤ W:=by
     apply narrower T R x g X hX u v k hW hu hv hT _ hx; rw [mul_pow]; exact charter Y u v W k Car hu0 hp hv.le hY he
lemma fared (h:0 < Car)(hb:k=Car)(ht:0 ≤ Y)(hp: Y ≤ u*v*W)(hx:‖valueH R (univ.toList.map X).prod‖ * (u*v)^k ≤ Y^Car) : topH T R x g ≤ W:=by
      apply narrower T R x g X hX u v k hW hu hv h _ hx
      rw [hb,← mul_pow]; exact pow_le_pow_left₀ ht hp _
omit hW hu hv hX
-- helm unify Correction C canonical at any L. use Melody/Eden Art.
open MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden YM.Arise YM.Arise.Bill Arise.Count MassiveQCD.Ribbon MassiveQCD.Play.Chamber QCD.Cove
open UV UV.Free QCD.Bera
variable {I J:Type}[Fintype I](Q:I→Bool)(L: I→ℕ)(Y:∀ i:I,Cups (L i) (Q i))(Z:I→E4) (l:List J)(f:J→List I)
local notation "Θ"=> allV l f
-- structural.FullAll. negative. local no proof-depend coarse slots.
variable (hZ:∀ i∈ l,Set.InjOn Z ((f i).toFinset:Set I))
include hZ
lemma provenance : ∃ C: Finset I→ Patio (Spine I),∀ t∈ allV l f, Honest Q t (C t)∧∀ (A:Type)[Fintype A], qraft A _ (C t)= -cetacea (pence (stampU A L Z) (fun i=> port Q L i (Y i))) t:=by
      choose C hc using fun t:Finset I=> show ∃ P:Patio (Spine I), t∈ allV l f→ Honest Q t P∧∀ (A:Type)[Fintype A], qraft A _ P= -cetacea (pence (stampU A L Z) (fun i=> port Q L i (Y i))) t from (by
             by_cases ht:t∈allV l f; swap; · exact ⟨0,fun h=> (ht h).elim⟩
             obtain ⟨j,hj,hp⟩:=mem_biUnion.mp ht; obtain ⟨F,hF,hX⟩:= Quills.Eden.artwork Q L Y Z _ (hZ _ (List.mem_toFinset.mp hj)); let v:=cetacea F t; let P:= -(v: Patio (Spine I)); have ht:t⊆(f j).toFinset:= Finset.mem_powerset.mp (Finset.mem_of_mem_erase hp); have hP(A:Type)[Fintype A]: Honest Q t v ∧ cetacea (pence (stampU A L Z) (fun i=> port Q L i (Y i))) t=qraft A _ v:=Quills.Eden.honorG Q ((f j).toFinset) F (fun i hi=>(hF i hi).1) t ht ∅ A _ (fun i hi=> (hF i hi).2 A)
             exact ⟨P, fun _=>⟨fun i h=> by unfold P; rw[map_neg]; exact ((hP i).1 i).minus,fun A _=>by unfold P; rw [map_neg,hP A |>.2]⟩⟩)
      exact ⟨C,hc⟩
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.faster
#print axioms YM.Massive.Lyre.provenance
