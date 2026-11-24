import YM.Avena.Rest
import YM.Oriole.Fowl
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
include V hB hZ hx he hk
open Tarot.Vista Massive.Lyre QCD.Plum
variable (s' Kp:ℕ) -- macro R
-- supports need generic stencil X complementary difference. supplier include exhibit data instead of forcing.RootV. 
lemma pollen (V':ℕ)(U':ℕ)(hU':0<U') (hb:wrap (S.side R0 n') u∈ (mural (viewW S R0 hh) (evenW S R0 he p') z).margin k (marginM S U' p' n'+102+V')) (hr:Kp ≤ V'*ratioTo S m n') -- Kp parameter
    (hFl:∀ σ, Floors (Gallery.rim Kp (wrap M σ)) ((Dℓ []) M σ)) (hRG:∀ σ:Cover,Lat.Invariant ((Dℓ []) M σ)) : QCD.Plum.Fence ((Column.sky S R0 p' m (hh.trans hk) (evenW _ R0 he _) z).chamber k) ⇑(checkedT r (ratioTo S m n') ((Dℓ []) M) u) ∧ Potion ⇑(checkedT r (ratioTo S m n') ((Dℓ []) M) u):=by
    obtain ⟨c,hc,hv,hg⟩:= strummed S u r (Dℓ [] M) hk; let I:=↥(Lattice.box (CardsT.flex S n' m)); let H(v:I):= ratioTo S m n' • u+v.val
    have h0(tR:Cover)(ht:wrap M tR∈ (W★).margin k Kp) : Base (W★) k 0 (Dℓ [] M tR):=by
          refine ⟨lower_maps (hFl tR) ?_, hRG tR, _,V.potD [] B Q ψ t x hB hx hZ tR⟩
          intro i hi; change i∈(W★).margin k 0; unfold Column.sky; apply (Intag.key_margin _ _ _ _ _ (viewOdd ..) 0).mpr; have h:= (Intag.key_margin _ _ _ _ _ (viewOdd S R0 (hh.trans hk)) Kp).mp ht; apply le_trans _ h
          · rw [Nat.add_zero]; apply (separation_triangle i (wrap M tR) _).trans; change separation _ _ ≤ _ at hi; rw [← separation_comm (wrap M tR) i]; omega
    have hP(i:I) := h0 (H i) (Intag.padding _ _ _ _ _ (viewOdd S R0 (hh.trans hk)) (budding hh hk he z k U' hU' u V' i.val i.property hb) (hr.trans ?_)) -- hp
    unfold checkedT; rw[hg]; constructor; rw[ContinuousMap.coe_sum]; exact shelter _ _ _ (fun i h'=> ((fences _ (hP i)).mass (↑(c i):ℂ)))
    refine ⟨polarity s,fun U=> ?_⟩; rw [ContinuousMap.sum_apply]; exact Grass.Hom.sum fun i _=> ((V.potD [] _ _ _ _ _ hB hx hZ _) U).smul (↑(c i):ℂ)
    rw [mul_comm V' _]; exact Nat.le_add_left ..
end Asset
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.pollen
