import YM.Alum.Dews
import YM.Alum.Chord
import YM.Pods.Hoops
import YM.Topaz.Room
import YM.Alum.Greet
import YM.Intag.Shift
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Tess Hymnal MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV UV UV.Free QCD.Grass QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon Quills.Clover
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6) {f l:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
-- presentations.From Calibration arrays.SYM
open Massive.Poised Massive.Poised.Plans Stamp Massive.Patria
variable {Vb:YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb) (Θ: Massive.SourceRead.TaperHol)(sy:RawSym)(Y: Massive.Sequence)(U:Lining.Temper.Collage.Exhibit.CoreMix)(base:ℕ→ℕ)
local notation "Px" => P.display Y Θ sy U base
variable (σ:Cover)(T:Tiling f)(t:T.Cell)(m:ℕ)(G:UV.Label D)(q:Bool)
lemma fences {u:T.Cell}{X:Insertion f 6}(h:Base T u k X): Fence (T.chamber u) X:=by
    refine ⟨Tide.stays X.continuous, ⟨?_,?_⟩, fun l U=> ContinuousMap.congr_fun (h.invariant l) U⟩
    all_goals
       obtain ⟨r,hF,hX,hZ⟩:= lower_maps h.floors (show T.margin u k ⊆ T.chamber u from fun i ht=>ht.1)
    · intro U V h; rw [hZ U,hZ V,hX U V h]
    intro U; exact ⟨r U,hZ U⟩
-- expose HP without carrying reference. compute r pre independent of sequence.
set_option quotPrecheck false
noncomputable def kingT (V:Finset Cover):= V.sup (fun i=>1+Laurent.size i)+1
lemma kerT {V:Finset Cover}{x:Cover}(h:x∈V)(a:Axis): (x a).natAbs < kingT V:=by
     have hv : 1+Laurent.size x ≤ V.sup (fun i=>1+Laurent.size i):= le_sup (f:=fun i=>1+Laurent.size i) h
     have ht : (x a).natAbs ≤ Laurent.size x:=single_le_sum (f:=fun i:Axis=> (x i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ a); unfold kingT; omega
-- want always without Seq? `Exhibit` → stencils.Local.
lemma kingFlow (hp:moored G.val q)(hk:wrap f σ∈ T.margin t m)(hV: kingT ((P.display Y Θ sy U base).stencil D) ≤ m)(ht:T.kind=.link):Base T t 0 (Bloom P D f σ G) ∧ Fence (T.chamber t) (Bloom P D f σ G)∧∀ V, Hom q (Bloom P D f σ G V):=by
      have h:= Hub.harvest sy G q hp σ T Y Θ P base U m t hk (fun x h a=> (kerT h a).trans_le hV) ht -- guess signatures `harvest`
      exact ⟨h, fences T h,Hub.fade (Bloom P D) sy (Massive.Patria.Depth.stays P Θ Y base sy U _) G q hp σ⟩
end Vista
end Tarot
end YM.Intag
#check YM.Massive.Patria.Hub.harvest
#print axioms YM.Intag.Tarot.Vista.kingFlow
