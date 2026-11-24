import YM.Avian.Jade
/-! Sym panel grouped reads carry ALL neutral slots at origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper
variable {S:Scheme}{R:Side}{i N p n d D:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore d)(hT:Rubric sym B) (H:Bore D)(hH:Rubric sym H)(W:Market S R D)(hW:Wager A T H W 0)(hA:A.Actual)
namespace Jewels
open Tawny Cast
open StressFlux.Offer (acts marks Vc)
open Patria.Rolls Patria.Rolls.Attain
-- origin d estimator on height
variable (F:PatchMix d)(hf:OrderMix A T sym B (i:=0) F)
variable (x:ℂ)(Q:RawTensor x d)
local notation "c"=> S.side R N
local notation "W'"=> A.density 0
include A
noncomputable def skyU (A:Run S N R 6)(B:Bore d)(F:PatchMix d)(x:ℂ)(Q:RawTensor x d)(i j:Axis)(p:Cover): Insertion c 6:= B c p (F (shelS i j) (Q.val (i,j)))
noncomputable def vine (i j:Axis): Cover→Insertion c 6:= nick (S.spacing N)⁻¹ i (skyU A B F x Q i j)
noncomputable def divine(i:Axis): Cover →Insertion c 6:= ∑ k:Axis,vine A B F x Q k i
local notation "Sχ"=> skyU A B F x Q
local notation "Yχ"=> vine A B F x Q
local notation "Vχ"=> divine A B F x Q
variable (s:Signed)(p:EuPin)(hp:p.Lifts s)(g:FlavorTorus)
variable (i j:Axis)
local notation "L"=> S.spacing N
-- lifts within Y
include hT hf
include hp in
lemma Ŝpin (r:Cover): Action.pin p s (Sχ i j r)= ((marks s (i,j):ℝ):ℂ) • ⇑(Sχ (s.perm i) (s.perm j) (s.act r)):=by
    unfold skyU; rw [hT.pin _ _ _ _ _ hp,hf.pinO _ _ p s hp]; rw[show Averaging.permute s (shelS i j)=shelS (s.perm i) (s.perm j) from pays_rotate _ _, show sym.pin d p (Q.val (i,j))=((marks s (i,j):ℝ):ℂ) • Q.val (acts s (i,j)) from ?_,map_smul,map_smul]; rfl
    apply Subtype.ext; rw [sym.pinActs]; exact (show Meaning _ _ _ _ _ _ from Q.property).ringo _ _ hp _
lemma shift_pin(r:Cover)(hh:p.Lifts s): Action.pin p s (Yχ i j r)= (↑(signT s j):ℂ) • ⇑(Yχ (s.perm i) (s.perm j) (s.act r)):=by
    funext U; apply Attain.highE; intro y; have hf:= congr_fun (Ŝpin A T sym B hT F hf x Q s p hh i j y) U; rw [show (↑(signT s j):ℂ)* _= ((marks s (i,j):ℝ):ℂ) from ?_]; exact hf
    change (_:ℂ)* (signT s i:ℂ)= (((signT s i*signT s j:ℝ)):ℂ); push_cast; ring
lemma organic_pin (r:Cover)(he:p.Lifts s): Action.pin p s (Vχ i r)= ⇑(( ((signT s i):ℝ):ℂ) • Vχ (s.perm i) (s.act r)):=by
     funext U; unfold divine; let G:= shipP c s p; let Y:= pull s 0 U; apply aux_val (T:=G) (s:=s) (z:=r) (e:=s.perm) (r:=signT s i) (B:=fun j=> vine A B F x Q j (s.perm i)); exact fun i' b=> congr_fun (shift_pin A T sym B hT F hf x Q s p i' i b he) U
variable (q:Axis→Label D)(h:∀ i, Tally T 0 (q i) (A.density 0) (trolley A (divine A B F x Q i) (shelV i) 0 0)) -- notation W' in variable! avoid
-- shared pipeline for charm transforms referencing Time charge
include hW hA hH h
lemma bond_pin(hh:p.Lifts s): (sym.pin D p) (q i)=(↑(signT s i):ℂ) • q (s.perm i):=by
    let k:=s.perm i; let r:ℂ:= signT s i; let X':=r • Vχ k; apply Attain.auth A T sym H hH W hA hW (Vχ i) X' s _ _ (h i) p hh (fun b=> organic_pin A T sym B hT F hf x Q s p i b hh) _ _ -- order hW hT
    unfold X'; rw [show Averaging.permute s (shelV i)=shelV (s.perm i) from pays_rotate _ _,scopeY]; exact Needle.quotaY _ _ _ _ _ _ (h (s.perm i))
end Jewels
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.Jewels.bond_pin
