import YM.Sprig.Slush
import YM.ValeK.Aster
import YM.Dart.Book
/-! Convert all tickets to one compatible matcher. Keeps law true at pre-polar discrete flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator
variable {S:Scheme}{R:Side}{i j ℓ k p N:ℕ}{c:Side}{D d:ℕ}(A:Massive.Run S N R 6)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas
open UV Vale Massive.Elm.SparK.Arbor.PlaneG
-- fix PlaneG path
variable (V:Vista (S.side R i) D)(Ξ:RawSym)(Θ:TaperHol)
variable (hA:A.Actual) (h:i ≤ N)(ht:j≤ i)
local notation "Φ"=> (lung V)
local notation "Sn"=>S.side R
variable (L:Bore d) {W:Market S R d}(hf:Rubric Ξ L)(hW:Wager A Θ L W j)
local notation "π"=>Attest A V Θ
variable {Vb: YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb)(Qv:∀ d,PatchMix d)(εr:ℝ)(base:ℕ→ℕ)
structure Skin (Ξ:RawSym)(d:ℕ)(f:Label d →ₗ[ℂ] Label d):Prop where
    pin (x) (p s) (h:p.Lifts s) : f (Ξ.pin d p x)=Ξ.pin d p (f x)
    adj x a : f (Ξ.adj d a x)=Ξ.adj d a (f x)
    charge x : f (Ξ.charge d x)=Ξ.charge d (f x)
    flavor x u: f (Ξ.flavor d u x)=Ξ.flavor d u (f x)
    parity x: f (Ξ.parity d x)=Ξ.parity d (f x)
    unit: f (Ξ.unit d)=Ξ.unit d
variable (H:Pins d)(K:Label d→ₗ[ℂ] Label d)
set_option quotPrecheck false
local notation "F"=> H.basic
include hf hA ht h hW
lemma awakens (hc:∀ p:Raw d, Attest A V Θ j (H.basic p) (K (H.basic p))): (∀ x:Label d,Attest A V Θ j x (K x))∧Skin Ξ d K:=by
     have hz : Attest A V Θ j 0 (K 0):=by rw[map_zero]; simpa only [zero_smul] using witnesses A V Θ _ _ (0:ℂ) (wingUnit A V Ξ Θ hA h ht L hf hW)
     have hm (x:Label d)(s:Finset (Raw d)) :Attest A V Θ j (∑ v∈s,(H.basic.coord v x) • F v) (K (∑ v∈s,(H.basic.coord v x) • F v)):=by
         induction s using Finset.induction_on with
         | empty=> rw [Finset.sum_empty]; exact hz
         | insert p s h ih=> rw [Finset.sum_insert h,map_add,map_smul]; exact brights A V Θ _ _ _ _ (witnesses A V Θ _ _ _ (hc p)) ih
     have he(x:Label d):π j x (K x):=by have h:=hm x Finset.univ; rwa [show ∑ v, H.basic.coord v x • H.basic v=x from H.basic.sum_repr x] at h
     refine ⟨he,⟨fun x p s hL=>?_,fun x a=>?_,fun x=>?_,fun x u=>?_,fun x=>?_,?_⟩⟩
     · exact Canvas.consensus Θ 0 _ (he _) _ (venus A V Ξ Θ hA h ht L hf hW _ _ (he x) p s hL)
     · exact Canvas.consensus Θ 0 _ (he _) _ (adjacent A V Ξ Θ hA h ht L hf hW _ _ (he x) a)
     · exact Canvas.consensus Θ 0 _ (he _) _ (topC A V Ξ Θ hA h ht L hf hW _ _ (he x))
     · exact Canvas.consensus Θ 0 _ (he _) _ (flora A V Ξ Θ hA h ht L hf hW _ _ (he x) u)
     · exact Canvas.consensus Θ 0 _ (he _) _ (lyreP A V Ξ Θ hA h ht L hf hW _ _ (he x))
     exact Canvas.consensus Θ 0 _ (he _) _ (wingUnit A V Ξ Θ hA h ht L hf hW)
noncomputable def harmonic (f:Raw d→Label d):Label d→ₗ[ℂ] Label d:= H.basic.constr ℂ f
lemma actors (p:Raw d→Label d)(hf':∀ t:Raw d, Attest A V Θ j (H.f t).mark (p t)): (∀ x:Label d,Attest A V Θ j x (harmonic H p x))∧Skin Ξ d (harmonic H p):= by
    apply awakens A V Ξ Θ hA h ht L hf hW H
    intro i; unfold harmonic; rw[Module.Basis.constr_basis,H.idV]; exact hf' i
omit hA h ht hf hW
noncomputable def tallyPt (R0:Vista c D)(X: Glyph D)(v:Label X.width):Label X.width:= (Vista.tokenP X R0:ℂ) • v
lemma stark (X:Glyph D)(v:Label X.width)(f:Label X.width→ₗ[ℂ] Label X.width)(hf:∀ u,Attest A V Θ (base X.width) u (f u))(h:TicketZ A P Θ V εr base Qv none X v) : tallyPt V X v=f X.material:= Canvas.consensus Θ 0 _ (smut A V Θ P Qv εr base X v h) _ (hf _)
lemma stampAt (X:Glyph D)(v:Label X.width): bornC (N:=N) P X V (Qv X.width none v) = fun x:Cover=> Massive.Patria.Depth.Bloom P X.width (S.side R N) x (Qv X.width none (tallyPt V X v)):=by funext x; unfold bornC tallyPt; rw[map_smul,map_smul]
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.actors
#print axioms YM.Intag.Sprig.stark
