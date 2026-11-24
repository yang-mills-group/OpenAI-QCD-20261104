import YM.Avian.Beryl
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
local notation "Sχ"=> skyU A B F x Q
local notation "Yχ"=> vine A B F x Q
local notation "Vχ"=> divine A B F x Q
variable (s:Signed)(p:EuPin)(hp:p.Lifts s)(g:FlavorTorus)
variable (i j:Axis)
local notation "L"=> S.spacing N
include hT hf
variable (q:Axis→Label D)(h:∀ i, Tally T 0 (q i) (A.density 0) (trolley A (divine A B F x Q i) (shelV i) 0 0)) -- notation W' in variable! avoid
-- shared pipeline for charm transforms referencing Time charge
include hW hA hH h
lemma Flavor_pure : sym.flavor D g  (q i)= q i:=by
       apply Attain.eon A T sym H hH W hA hW (divine A B F x Q i) (shelV i) (q i) (h i) g 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=stroll c g; let U':Grid c:=(fun U=>U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i b U') = Yχ j i b U:=by
            intro j b; apply aux_g; intro y; let z:=Q.val (j,i); let t:= shelS j i; have hh: sym.flavor d g z=z:=by
                apply Subtype.ext; rw [sym.flavorActs]; exact (show Meaning _ _ _ _ _ _ from Q.property).light (j,i)|>.2 g
            unfold skyU; have hp: Action.flavor g (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.flavor c (F t z) y g,hf.flavorO,hh]
            exact congr_fun hp U
       change L' ((Vχ i) b U')=_; unfold divine; rw [Finset.sum_apply, ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma quiet_pure : sym.parity D  (q i)= q i:=by
       apply Attain.dew A T sym H hH W hA hW (divine A B F x Q i) (shelV i) (q i) (h i) 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=QCD.Grass.grade; let U':Grid c:=(fun U=>U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i b U') = Yχ j i b U:=by
            intro j b; apply aux_g; intro y; let z:=Q.val (j,i); let t:= shelS j i; have hh: sym.parity d z=z:=by
                apply Subtype.ext; rw [sym.parityActs]; exact (show Meaning _ _ _ _ _ _ from Q.property).light (j,i)|>.1
            unfold skyU; have hp: Action.parity (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.parity c (F t z) y,hf.parityO,hh]
            exact congr_fun hp U
       change L' ((Vχ i) b U')=_; unfold divine; rw [Finset.sum_apply, ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma sea_pure : sym.charge D  (q i)= q i:=by
       apply Attain.hour A T sym H hH W hA hW (divine A B F x Q i) (shelV i) (q i) (h i) 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=eveN c; let U':Grid c:=(fun U=> conjugate ∘ U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i b U') = Yχ j i b U:=by
            intro j b; apply aux_g; intro y; let z:=Q.val (j,i); let t:= shelS j i; have hh: sym.charge d z=z:=by
                apply Subtype.ext; rw [sym.chargeActs]; exact (show Meaning _ _ _ _ _ _ from Q.property).coal (j,i)
            unfold skyU; have hp: Action.charge (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.charge c (F t z) y,hf.chargeO,hh]
            exact congr_fun hp U
       change L' ((Vχ i) b U')=_; unfold divine; rw [Finset.sum_apply, ContinuousMap.sum_apply,ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma vectorial : q ∈ RawVec D:=by
    refine ⟨fun i=>⟨?_,fun u=>?_⟩,fun i=>?_,fun s p hp i=>?_,fun i=> ?_⟩
    · rw [← RawSym.parityActs,quiet_pure A T sym B hT H hH W hW hA F hf x Q i q h] -- order ht hf
    · rw [← RawSym.flavorActs, Flavor_pure A T sym B hT H hH W hW hA F hf x Q u i q h]
    · rw [← RawSym.chargeActs, sea_pure A T sym B hT H hH W hW hA F hf x Q i q h]
    · rw [← RawSym.pinActs,bond_pin A T sym B hT H hH W hW hA F hf x Q s p i q h hp]; rfl
    rw [one_smul]; rfl
end Jewels
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.Jewels.vectorial
