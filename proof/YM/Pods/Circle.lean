import YM.Pods.Alight
import YM.Pods.Shingle
import YM.Pods.Gleams
import YM.Pods.Pads
/-! Transforms of reflected calibrated source. Root tickets. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth
variable {S:Scheme}{r c n:Side}{N d:ℕ}{F:ℕ} (R:Regulator n 6)
variable (Z:Bore d) (sym:RawSym)(hz:Rubric sym Z)(u:Label d)(q:Bool)(hu: moored u.val q)
lemma graded_eye (a:Axis) : sym.parity d (sym.adj d a u)=sym.adj d a (sym.parity d u):=by
    apply Subtype.ext; rw [sym.parityActs,sym.adjActs,sym.adjActs,sym.parityActs]
    induction u.val using TensorProduct.induction_on with
    | zero=> simp only [map_zero]
    | add x y ih iH=> rw [map_add,map_add,map_add,map_add,ih,iH]
    | tmul x y=> unfold parityAct UV.adj; rw [TensorProduct.map_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul]; apply congr_arg (TensorProduct.tmul ℂ (((Labels.rotated (Signed.reflect a)).toLinearMap.comp conjGPol) x)); exact (by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, changeVars,exterior_parity, dagger_parity]) -- exterior order
include hu
lemma durable (a:Axis) : moored (sym.adj d a u).val q:=by
    apply (moored_iff sym _ q).2; rw [graded_eye, (moored_iff sym u q).1 hu,map_smulₛₗ]; cases q <;> simp
include hz
lemma fade (b:Cover)(V: Grid c) : Hom q (Z c b u V):=by
    have hp:= congr_fun (hz.parity c u b) V; rw [(moored_iff sym _ q).1 hu,map_smul] at hp
    cases q; · change grade _=_; rw [if_neg Bool.false_ne_true,one_smul] at hp; exact hp
    unfold Grass.Hom Minus; rw [if_pos rfl, neg_one_smul] at hp; exact hp
-- paths don't length cost if use orientation spine.S same orientations.S
variable (T:Tiling n)(A₀:T.Cell)(hv:T.kind=.link)(x:T.Cell→ Cover)(hg:∀ (p:T.Cell)(a:Axis)(v:T.Cell), wrap n (x (T.mate p a v))=(T.bandCut p a).reflect (wrap n (x v)))(hr:R.t=0)
local notation "B"=>x A₀
local notation "ω"=>T.omega
local notation "Θ₁"=>sym.adj d
local notation "Cn"=> Z n
include hr hv hg
lemma copied (p:T.Cell)(a:Axis) : SignedEq (picture (T.bandCut p a) R.zeroCut (Cn B u)) (Z n (x (T.mate p a A₀)) (Θ₁ a u)):=by
    let C:= T.bandCut p a; let o:= T.mate p a A₀; let L:=(Signed.mirror a); let R₁:= L.act B; let b:= x o-R₁
    have ht : wrap n b=C.slide:=by
        unfold b; rw [map_sub]; unfold o; rw [hg]; change affine L C.slide (wrap n B)- _=_; rw [show R₁= _ from rfl, ← wrap_signed]; exact add_sub_cancel_left ..
    have hf := pic_match R C b ht hv (Z n B u) hr q (fade Z sym hz u q hu B)
    have h: march b (Action.adj C.pos ⇑(Z n B u)) = Z n (x o) (Θ₁ a u) := by rw [hz.eye n u B, hz.advances, show (Signed.mirror C.pos).act B+b=x o from add_sub_cancel ..]; rfl -- arg order. test
    rw [h] at hf; rcases hf with hf|hf; exact Or.inl (ContinuousMap.ext (congr_fun hf)); exact Or.inr (ContinuousMap.ext (congr_fun hf))
-- tally orientations.L. Path
noncomputable def spine (x:Label d) : List Axis → Label d
 | []=>x
 | a::l=> sym.adj d a (spine x l)
local notation "T'"=> spine sym
omit hz hu hg hv hr
lemma negatePic (p:T.Cell)(a:Axis)(X:Insertion n 6): picture (T.bandCut p a) R.zeroCut (-X)= -picture (T.bandCut p a) R.zeroCut X:=by rw [← neg_one_smul ℂ X,pic_smul]; simp
-- include resets caution negatePic includes many vars automatic! omit wrappers
include hz hu hg hv hr
lemma spirals (k:TapeWalk n T) : moored (T' u (axes (pathT T k))).val q ∧ SignedEq (reels R.zeroCut (pathT T k) (Z n B u)) (Z n (x (finish T A₀ k)) (T' u (axes (pathT T k)))):=by
    induction k with
    | nil=> exact ⟨hu,SignedEq.refl _⟩
    | cons i k ih=>
       let w:= T' u (axes (pathT T k)); let p:= finish T A₀ k
       rcases i with ⟨j,a⟩
       refine ⟨durable sym w q ih.1 a,?_⟩
       let G:= copied R Z sym hz w q ih.1 T p hv x hg hr j a; apply SignedEq.trans _ G
       change SignedEq (picture (T.bandCut j a) R.zeroCut (reels R.zeroCut (pathT T k) (Z n B u))) (picture (T.bandCut j a) R.zeroCut _); rcases ih.2 with h|h; · rw [h]
       apply Or.inr; rw [h]; apply negatePic .. -- sig. constructor
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.spirals
#print axioms YM.Massive.Patria.Hub.copied
