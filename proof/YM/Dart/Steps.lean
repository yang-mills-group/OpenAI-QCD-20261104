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
include V
lemma marchL (a:ℝ)(b x:Cover): Patria.march x (tileD X s a l n b)= tileD X s a l n (b+x):=by
    unfold tileD; rw[layered]; have ht:=(V.bore l).scale (↑(PlaneG.Asset.game s a):ℂ); obtain ⟨S,hs⟩:= ht.exists; obtain ⟨F,hF,h₁,h₂⟩:= hs.funded; rw [←hF]; exact Patria.Canvas.stylus ..
lemma heritageD (a:ℝ)(l:List Axis)(b:Cover): moon (polarity s) (tileD X s a l n b):=by unfold tileD; rw[layered]; exact fun i=>(V.heritage l n b i).smul _
omit V
open Hub Patria.Depth Chess.Fortuna
-- scale once.Observer calibration counterterms P.X
variable (B:Bore d) (Q:RawSym)(ψ:Label d ≃ₗ[ℂ] Label d) (t:ℝ) (x:Label d) (hB:Rubric Q B) (hx:moored x.val (polarity s))
variable (hZ:∀ x:Label d,Q.parity d (ψ x)=ψ (Q.parity d x))(hU:∀ a:Axis,∀ x:Label d,Q.adj d a (ψ x)=ψ (Q.adj d a x))
noncomputable abbrev differenceD (X:Drape)(s:ℕ)(B:Bore d)(Q:RawSym)(ψ:Label d≃ₗ[ℂ]Label d)(x:Label d)(t:ℝ)(l:List Axis):Drape:= tileD X s t l-(fun n b=> B n b (ψ (spine Q x l)))
local notation "Dℓ"=> differenceD X s B Q ψ x t
open Intag
variable (b:Cover)
include hB hx hZ V in
lemma potD : moon (polarity s) (Dℓ l n b):=by
    have h(l:List Axis): moored (spine Q x l).val (polarity s):=by induction l with|nil=>exact hx|cons i l ih=>exact durable _ _ _ ih i
    let y:= spine Q x l; have hy:moored (ψ y).val (polarity s):= (moored_iff Q _ _).mpr (by rw[hZ y,(moored_iff Q y _).1 (h _),map_smul]); have hf:= fade (c:=n) B Q hB _ _ hy b; have hh:= V.heritageD (n:=n) t l b; intro i; change Hom _ (_-_); rw [sub_eq_add_neg,←neg_one_smul ℂ _]; exact (hh i).add ((hf i).smul _)
include hB hU in
lemma seeD (a:Axis)(j:Cover) : unia a (differenceD X s B Q ψ x t l n j)=Dℓ (a::l) n (axisT a j):=by
    change unia a (tileD X s t l n j- B n j (ψ (spine Q x l)))= via a (Asset.tileD X s t l) n (axisT a j)-B n (axisT a j) (ψ (spine Q x (a::l)))
    have h(W Y:Insertion n 6):unia a (W-Y)=unia a W-unia a Y:=by ext1 U; rw [heroY,ContinuousMap.sub_apply,map_sub, ContinuousMap.sub_apply,heroY,heroY]
    rw [h, via_site]; congr 1; apply ContinuousMap.ext; intro i
    apply Eq.trans (congr_fun (hB.eye n (ψ (spine Q x l)) j a) i)
    rw [hU a]; rfl
include hB V in
lemma marchD (v:Cover) : Patria.march v (Dℓ l n b)=Dℓ l n (b+v):= by
    let Y:= B n b (ψ (spine Q x l)); funext U
    have h :∀ W Y:Insertion n 6, Patria.march v (W-Y:Insertion n 6) U=march v W U- march v Y U:=by intro W Y; simp [march,TorusPCAC.Geometry.post]
    exact (h (tileD X s t l n b) Y).trans (congr_arg₂ (·-·) (congr_fun (V.marchL ..) U) (congr_fun (hB.advances ..) U))
local notation "ζ"=> Dℓ ([])
open QCD.RP Romance Chess Cells
variable {c f:Side}(R:Regulator f 6) (g:Ratio c f) (hp:Odd g.count.val)(he:Even c.val)(hr:R.t=0)
include V hB hx hZ hU hr
lemma snakes (T:Tiling f)(he:T.kind=.link)(Xo:T.Cell→ Cover)(hg:∀ (p:T.Cell)(a:Axis)(v:T.Cell), wrap f (Xo (T.mate p a v))=(T.bandCut p a).reflect (wrap f (Xo v)))(v:T.Cell)(L:TapeWalk f T): SignedEq (reels R.zeroCut (pathT T L) (Dℓ [] f (Xo v))) (Dℓ (axes (pathT T L)) f (Xo (finish T v L))):=by
    have hC(p:T.Cell)(a:Axis)(u:T.Cell)(l:List Axis): SignedEq (picture (T.bandCut p a) R.zeroCut (Dℓ l f (Xo u))) (Dℓ (a::l) f (Xo (T.mate p a u))):=by
         let C:= T.bandCut p a; let K:=T.mate p a u; let y:= Xo u; let t':=axisT a y; let b:= Xo K-t'; have ht:wrap f b=C.slide:=by unfold b; rw [map_sub,hg]; change affine _ _ _- _=_; unfold t' axisT; rw [←wrap_signed]; exact add_sub_cancel_left ..
         let G:= Dℓ l f y; have hf:= pic_match R C b ht he G hr (polarity s) (V.potD _ _ _ _ _ _ hB hx hZ _) -- probably args
         have hz:Patria.march b (Cylinder.Action.adj C.pos G)= Dℓ (a::l) f (Xo K):=by
                change Patria.march b (⇑(unia a G))=_; rw [show unia a G=Dℓ (a::l) f t' from seeD l B Q ψ t x hB hU a y, marchD V _ _ _ _ _ _ hB t' b, add_sub_cancel]
                -- fix VEd abbreviation
         rw[hz] at hf; rcases hf with hf|hf; exact Or.inl (ContinuousMap.ext (congr_fun hf)); exact Or.inr (ContinuousMap.ext (congr_fun hf))
    induction L with
    | nil=>exact SignedEq.refl _
    | cons i l ih=>
       rcases i with ⟨j,a⟩; apply SignedEq.trans _ (hC j a (finish T v l) (axes (pathT T l)))
       change SignedEq (picture (T.bandCut j a) R.zeroCut (reels R.zeroCut (pathT T l) _)) (picture (T.bandCut j a) R.zeroCut _); rcases ih with h|h; · rw[h]
       apply Or.inr; rw [h]; apply Hub.negatePic ..
end Asset
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.Asset.snakes
