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
variable (b:Cover)
local notation "ζ"=> Dℓ ([])
open QCD.RP Romance Chess Cells
variable {c f:Side}(R:Regulator f 6) (g:Ratio c f) (hp:Odd g.count.val)(he:Even c.val)(hr:R.t=0)
include hp he hB hx hZ hU hr V
local notation "K"=> g.count.val
local notation "T"=> mural g he (wrap f b)
lemma claims (Vv:ℝ)(hV:0≤Vv)(hX:∀ Y:Site c→List Axis,(∀ i,(Y i).length ≤ 8) → ‖R.average ((univ:Finset (Site c)).toList.map fun i=>Dℓ (Y i) f (g.count.val • Lattice.lift i)).prod‖≤ Vv^Fintype.card (Site c)) : floorL (mural g he (wrap f b)) R.average R (Dℓ [] f b) 0 ≤ Vv:=by
    let TQ:= T; let b':=wrap f b; let y(v:Site c):= b+K • Lattice.lift v
    have hh(v): TQ.copyMap v b'=wrap f (y v):= (tuned g he hp b' v).trans (by rw [show _= _ from map_add (wrap f) b _]; rfl)
    have hG : y 0=b:=by unfold y; rw [show Lattice.lift (0:Site c)=0 from (by funext; simp [Lattice.lift]),smul_zero,add_zero]
    have hv : ∀ (p:TQ.Cell)(a:Axis)(v:TQ.Cell),wrap f (y (TQ.mate p a v))=(TQ.bandCut p a).reflect (wrap f (y v)):=fun p a v=> (hh _).symm.trans ((TQ.after p a v b').trans (congr_arg (TQ.bandCut p a).reflect (hh v)))
    choose L he₁ ht using fun v: TQ.Cell=> legsT TQ 0 v; let Qv(v:TQ.Cell):= axes (pathT TQ (L v)); have htL(v:TQ.Cell):(Qv v).length ≤8:=by unfold Qv axes pathT; simp only [List.length_map]; exact he₁ v
    have he₂:TQ.kind=.link:=rfl; let P:= Dℓ [] f b; let F(v:TQ.Cell):= Dℓ (Qv v) f (y v); let G(v:TQ.Cell):= Dℓ (Qv v) f (K • Lattice.lift (show Site c from v))
    have hx'(v):SignedEq (replicateR TQ R P 0 v) (F v):=by
         apply SignedEq.trans (SignedEq.symm (along TQ R.zeroCut P (L v) 0 v ⟨_,V.potD [] _ _ _ _ _ hB hx hZ b⟩ hr he₂ (ht v)))
         have h:= snakes V B Q ψ t x hB hx hZ hU R hr TQ he₂ y hv 0 (L v); rw [show y (0:TQ.Cell)=b from hG,ht] at h; exact h
    let l:= (Finset.univ :Finset TQ.Cell).toList; apply le_of_pow_le_pow_left₀ TQ.cells_positive.ne' hV; rw [roof_power]; change ‖R.average ((l.map _).prod)‖ ≤ Vv ^ Fintype.card TQ.Cell
    rw [Chess.Fortuna.Array.holds_period R.average (signed_product l _ _ hx'), ← ferry_many R l hr b G F (fun i=>?_)]; · exact hX Qv htL
    unfold G F y; rw [marchD V _ _ _ _ _ _ hB]; exact congr_arg (fun o:Cover=> ⇑(Dℓ (Qv i) f o)) (add_comm _ b)
omit hp he hB hx hZ hU hr
-- authenticity geometric.Footing on T chamber.
lemma supplier (A:Lining.Temper.Collage.Exhibit H)(d:ℕ) : ∃ k:ℕ,∀ (n:Side)(x:Label d)(t:ℝ)(p:Cover), Floors (Gallery.rim k (wrap n p)) ((tileD X s t [] n p) - (Bloom A d n p x)):=by
     obtain ⟨r,h⟩:= caseFoot A d
     obtain ⟨W,hW⟩:= (V.bore []).exists; obtain ⟨F,hF,h₁,h₂⟩:= hW.funded; obtain ⟨k,hK⟩:= shafts W; refine ⟨k+r,fun n x t p=>?_⟩
     have hpx: Floors (rim k (wrap n p)) (tileD X s t [] n p):=by
           unfold tileD; rw[layered,←hF]; apply QCD.RP.flooring_smul _ (Gallery.padG p F _ (hK n p))
     exact Gallery.floors_sub (RP.lower_maps hpx (fun i ht=> le_trans ht (show k≤k+r from Nat.le_add_right ..))) (RP.lower_maps (h _ _ _) (fun i ht=> le_trans ht (show r≤k+r from Nat.le_add_left ..)))
include he
lemma basePay (A:Lining.Temper.Collage.Exhibit H) (hb: ∀ (n:Side)(b:Cover)(x:Label d), Lat.Invariant (Bloom A d n b x))(hB:Rubric Q (Bloom A d))(hp:moored (ψ x).val (polarity s))(k:ℕ) (hp':Floors (Gallery.rim k (wrap f b)) (tileD X s t [] f b - (Bloom A d f b (ψ x)))) (hP:k≤g.count.val/2)(hG:Odd g.count.val) :Base (mural g he (wrap f b)) 0 0 (differenceD X s (Bloom A d) Q ψ x t [] f b):=by
      change Base (mural _ _ _) _ 0 (tileD X s t [] f b-Bloom A d f b (ψ x)); have hh: ∀ U, Hom (polarity s) ((tileD X s t [] f b-Bloom A d f b (ψ x):Insertion f 6) U):=by
            intro i; change Hom _ (_-_); rw [sub_eq_add_neg,← neg_one_smul ℂ _]; exact (V.heritageD t [] b i).add ((fade _ Q hB _ _ hp b i|>.smul _)) -- infer
      have ht :Invariant (tileD X s t [] f b) :=profileEv (x:= (↑(game s t):ℂ) • X) (fun i o=> RP.invariant_smul _ (V.shape i o) _) [] _ _
      refine ⟨lower_maps hp' (fun i hi=>?_),?_,_,hh⟩
      · rw [key_margin _ _ _ _ _ hG]; change separation i (wrap f b + g.embed 0)+0 ≤ _; rw [show g.embed 0=0 from g.root.map_zero,add_zero,add_zero,separation_comm]; exact le_trans hi hP
      rw [sub_eq_add_neg, ←neg_one_smul ℂ _]; apply RP.invariant_add _ _ ht (RP.invariant_smul _ (hb f b _) _) -- hb trailing frame.
end Asset
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.claims
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.basePay
