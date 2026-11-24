import YM.Avena.Glow
import YM.Dart.Oscilla
import YM.Dart.Steps
import YM.Dart.Lodge
import YM.Infer.Vase
/- Genuine root tiling reflection for deterministic placement prices.
  Works for arbitrary single calibrated discrepancy and the true symmetry acts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PlaneG
open Gallery PrismD Civic
open Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate
open Cove Creek Stamp
variable {H:YM.Source.Hol su}(U:Lining.Temper.Collage.Exhibit H)(θ:SourceRead.TaperHol)
variable {X:Drape} {s:ℕ}
namespace Asset
variable (V:Asset X s) (l:List Axis)
open Hub Patria.Depth Chess.Fortuna
-- scale once.Observer calibration counterterms P.X
variable (B:Bore d) (Q:RawSym)(ψ:Label d ≃ₗ[ℂ] Label d) (t:ℝ) (x:Label d) (hB:Rubric Q B) (hx:moored x.val (polarity s))
variable (hZ:∀ x:Label d,Q.parity d (ψ x)=ψ (Q.parity d x))(hU:∀ a:Axis,∀ x:Label d,Q.adj d a (ψ x)=ψ (Q.adj d a x))
local notation "Dℓ"=> differenceD X s B Q ψ x t
open Intag

open Massive.Chess.Fortuna Massive.Chess Massive.Romance Massive.Patria YM.Intag.Pilgrim YM.Intag.CardsT Cells YM.Next.Rank
variable {S:Scheme}{R0:Side}{m n' p':ℕ}{F:Type}(A:Massive.Run S m R0 6) (r:Averaging)(z:Site (S.side R0 n'))(k:Site (S.side R0 p')) (hh:p'≤ n')(hk:n' ≤ m)(he:Even R0.val)(u:Cover)
local notation "M"=> S.side R0 m
local notation "R"=> mural (viewW S R0 hh) (evenW S R0 he p') z
local notation "Ψ" k':arg=>Hymnal.reversa (mural (viewW S R0 hh) (evenW S R0 he p') z) k k'
local notation "P₀"=> S.side R0 p'
local notation "Fφ"=> fun k':Site P₀=> Dℓ (Ψ k') M
local notation "W★"=> Column.sky S R0 p' m (hh.trans hk) (evenW S R0 he p') z
include V hB he hx hk hh hZ hU
lemma stormF : ∃ (m':ℕ)(f:Fin m'→Hole (Site (S.side R0 p')) S n' n'), MassiveQCD.Sample.Quills.crest f=Finset.univ ∧ Function.Injective f ∧ m'=Fintype.card (Site (S.side R0 p')) ∧ ‖A.regulator.average (CardsT.rolledT (Pilgrim.bout (R) k rfl u) (fun _=>r) (Fφ) m' f)‖=Massive.Lyre.topH (W★) A.regulator ⇑(CardsT.checkedT r (ratioTo S m n') (Dℓ [] M) u) k ^ Fintype.card (Site (S.side R0 p')):=by
      let Φ:= Fφ; let T: Tiling (S.side R0 n'):= R; have ht:Φ k=Dℓ [] M:=by
           unfold Φ Hymnal.reversa; rw [Pilgrim.at_p]; rfl
      rw [← ht]; apply stoke A z hh he k u (fun _=>polarity s) r Φ le_rfl hk (fun i a b=> marchD V (Ψ i) B Q ψ t x hB a b)
      · exact fun i b=> V.potD (Ψ i) _ _ _ _ _ hB hx hZ b
      intro i hi b; let C:= T.bandCut (Pilgrim.post (R) k i).1 (Pilgrim.post (R) k i).2
      let j:= Pilgrim.μ (R) k i
      have hf:= congr_arg DFunLike.coe (seeD (Ψ j) B Q ψ t x hB hU C.pos b (X:=X) (n:=M) (s:=s)) -- inspect unia tape
      change Cylinder.Action.adj C.pos (Φ j b)=(Φ i) (C.flip.act b); dsimp only [Φ]; rw [Hymnal.writes (R) k _ hi]; exact hf
end Asset
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.stormF
