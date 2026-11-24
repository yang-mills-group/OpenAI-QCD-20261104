import YM.Mural.Lipid
import YM.Mural.Wallet
/-!
# Tracking the line on the actual unnormalized spin-gauge history.
 The rail must name a pressure normalization yielding the initial mass test density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
variable {R:Side}{S:Scheme}{n:ℕ} (X:Massive.Run S n R N) (a b:Flavor N)(q:ℕ)
-- S constant stencil size only on this range. collar `t_j` width.
variable (V:ℕ→ TokenP)(D:∀ i,DeckV (S.side R i) N)(p:ℕ→ℝ)(Z:Spike){w x y:ℝ}{i:ℕ}
local notation "Y"=> (PCAC.actor X)
structure Cavalry (j:ℕ):Prop where
 stride (i:ℕ) (h:i<q): S.J (i+1)=j
 radius : ∃ z:ℂ,z≠0 ∧∀ i:Grid (S.side R q), actor X q i=z • (D q).density i
 lift i(h:i<q):∃ (C:ℂ), C≠0 ∧ ∃ (B:ℕ)(a b v w wp:ℝ), Comet.SpanC (D i) (D (i+1)) (S.step i) (S.sides_next R i) S.choices (X.w i) (X.β (i+1)) C (V i) (V (i+1)) B a b v w wp -- h budget extra fields include Toll on same knobs. adjust
structure Sworn (j:ℕ) (u v₁ w':ℝ):Prop where
  stride :∀ i<q,S.J (i+1)=j
  radius : ∃ z:ℂ,z≠0 ∧∀ i:Grid (S.side R q), actor X q i=z • (D q).density i
  lift i(h:i<q):∃ (C:ℂ), C≠0 ∧ ∃ (B:ℕ)(a b v w wp:ℝ), Comet.SpanC (D i) (D (i+1)) (S.step i) (S.sides_next R i) S.choices (X.w i) (X.β (i+1)) C (V i) (V (i+1)) B a b v w wp ∧ TollG (V (i+1)) (S.step i).L (S.J (i+1)) (X.w i) wp b w u v₁ w'
  -- Lipid q₀=a(y), y₀=b, e₀=v,b=w.W.R.Prop.
variable (h:X.Actual) (hv:q≤n)(H: Sworn X q V D j x y w) (hx:0 ≤x)(hy:0≤y)(hz:∀ i j,‖Z i j‖≤w)
include h hv H hx hy hz
set_option maxHeartbeats 460000 in
lemma crosses (M:∀ i,PCAC.Deck (S.side R i) N) (hc : M q=0) (hp:∀ i<q,M i= liftM X Z a b i (M (i+1))) : ∀ i ≤ q,∃ w:ℂ,w≠0 ∧(∀ u:Grid (S.side R i), Y i u= w • (D i).density u)∧ Invoice (D i) (M i) (berthD j) (V i) (Y i) w x y:=by
      intro i hi; induction hi using Nat.decreasingInduction with
      | self=> rw [hc]; obtain ⟨w,he,hp⟩:=H.radius; exact ⟨_,he,hp,fun _ _ _ _ _=>rfl,fun _ _ _ _ _=> ClaimP.boxed hx hy⟩
      | of_succ i hi ih=>
          obtain ⟨C,hC,B,a',b',v,w',wp,hX,hT⟩:= H.lift i hi; obtain ⟨α,hα,he,hM⟩:=ih
          let N₀:= (S.step i).L; let V₀:= Transfer.blockMap (F:=N) (S.step i) S.choices (S.sides_next R i) (X.β (i+1)) (X.w i) (S.admissible i); have hV: Y i= V₀ (Y (i+1)) :=(moves X h (hi.trans_le hv)).symm
          refine ⟨α*C,mul_ne_zero hα hC, credible (D i) (D (i+1)) _ _ _ _ _ (S.admissible i) _ _ C α _ _ a' b' v w' wp B hX he hV, ?_⟩
          rw [hp i hi,← H.stride i hi]; exact attain (D i) (D (i+1)) _ _ _ _ _ (S.admissible i) _ _ C α _ _ a' b' v w' wp B hX he hV w x y Z a b hz hT hx hy (M (i+1)) (H.stride i hi|>.symm ▸ hM)
end YM.QCD.Comet
#print axioms YM.QCD.Comet.crosses
