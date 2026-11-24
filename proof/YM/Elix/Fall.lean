import YM.Elix.Gold
/-! Sym panel grouped reads carry ALL neutral slots at origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper
variable {S:Scheme}{R:Side}{i N p n d D:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 6)(hT:Rubric sym B) (H:Bore D)(hH:Rubric sym H)(W:Market S R D)(hW:Wager A T H W 0)(hA:A.Actual)
namespace Onyx.Gourd
open Tawny Cast
open StressFlux.Offer (acts marks Vc)
open Patria.Rolls Patria.Rolls.Attain
variable (F:PatchMix 6)(hf: OrderMix A T sym B (i:=0) F)
local notation "c"=> S.side R N
local notation "W'"=> A.density 0
include A
variable (u: Flavor 6)
noncomputable def skyH(A:Run S N R 6)(B:Bore 6)(F:PatchMix 6)(u:Flavor 6)(i j k:Axis)(p:Cover): Insertion c 6:= B c p (F (shelC i j k) (Carnal.gamma6 u i j k))
noncomputable def branch(i j k:Axis): Cover→Insertion c 6:= nick (S.spacing N)⁻¹ i (skyH A B F u i j k)
noncomputable def brook(j k:Axis): Cover→Insertion c 6:= ∑ i:Axis,branch A B F u i j k
local notation "Sχ"=> skyH A B F u
local notation "Yχ"=> branch A B F u
local notation "Vχ"=> brook A B F u
variable (s:Signed)(p:EuPin)(hp:p.Lifts s)(g:FlavorTorus)
variable (i j k:Axis)
local notation "L"=> S.spacing N
open Carnal
local notation "G"=> gamma6 u
local notation "Z1"=>signT s i
local notation "Z2"=>signT s j
local notation "Z3"=>signT s k
include hT hf
lemma Hpin(r:Cover)(hp:p.Lifts s): Action.pin p s (Sχ i j k r)= ((↑((signT s i)*(signT s j)*(signT s k))):ℂ) • ⇑(Sχ (s.perm i) (s.perm j) (s.perm k) (s.act r)) :=by
     unfold skyH; rw [hT.pin _ _ _ _ _ hp,hf.pinO _ _ p s hp]; rw [show Averaging.permute s (shelC i j k)=shelC (s.perm i) (s.perm j) (s.perm k) from pays_rotate _ _, show sym.pin 6 p (G i j k)=(↑((signT s i)*(signT s j)*(signT s k)):ℂ) • G (s.perm i) (s.perm j) (s.perm k) from ?_,map_smul,map_smul]; rfl
     exact Subtype.ext ((sym.pinActs ..).trans (pin_lamp u s p hp i j k))
lemma Bow_pin(r:Cover)(h':p.Lifts s): Action.pin p s (Yχ i j k r)= (↑(signT s j*signT s k):ℂ) • ⇑(Yχ (s.perm i) (s.perm j) (s.perm k) (s.act r)):=by
     funext U; apply Attain.highE; intro y; have hh:= congr_fun (Hpin A T sym B hT F hf u s p i j k y h') U; rw [show (↑(signT s j*signT s k):ℂ)*(signT s i:ℂ)=(↑(signT s i*signT s j*signT s k):ℂ) from by push_cast; ring]; exact hh
lemma omega_pin(r:Cover)(ht:p.Lifts s) : Action.pin p s (Vχ j k r)= ⇑(((↑(signT s j*signT s k)):ℂ) • Vχ (s.perm j) (s.perm k) (s.act r)):=by
     funext U; unfold brook; apply aux_val (T:= shipP c s p) (s:=s) (z:=r) (e:=s.perm) (r:= signT s j *signT s k) (B:=fun i=> Yχ i (s.perm j) (s.perm k)); exact fun l b=>congr_fun (Bow_pin A T sym B hT F hf u s p l j k b ht) U
lemma omega_flip : Vχ k j= (-1:ℂ) • Vχ j k:=by
     have he(i:Axis): Yχ i k j= (-1:ℂ) • Yχ i j k:=by
          have hg: Sχ i k j= - Sχ i j k:=by
              funext p; unfold skyH; rw [show shelC i k j=shelC i j k from pais _ _ (List.Perm.cons _ (List.Perm.swap ..)), show G i k j= - G i j k from ?_,map_neg,map_neg]; rfl
              unfold gamma6; rw [trio_adj i k, Carnal.push_neg]
          unfold branch; rw [hg]; rw [neg_one_smul ℂ (_ : Cover→Insertion c 6)]; funext b; change (_ :ℝ) • (-_ - -_)= - ((_:ℝ) • (_-_): Insertion c 6); rw [← smul_neg]; apply congr_arg; abel
     unfold brook; simp_rw [he]; exact Eq.symm (Finset.smul_sum ..)
variable (q:(Axis×Axis)→Label D)(h:∀ j k, Tally T 0 (q (j,k)) (A.density 0) (trolley A (brook A B F u j k) (shelS j k) 0 0))
include hW hA hH h
lemma bridge_pin(hp:p.Lifts s): (sym.pin D p) (q (i,k)) = (↑(signT s i * signT s k):ℂ) • q (s.perm i,s.perm k):=by
    let r:ℂ:= signT s i*signT s k; -- coerced product ambiguous
    let X':=(↑(signT s i * signT s k):ℂ) • brook A B F u (s.perm i) (s.perm k); apply Attain.auth A T sym H hH W hA hW (Vχ i k) X' s _ _ (h i k) p hp (fun b=> omega_pin A T sym B hT F hf u s p i k b hp) _ _; unfold X'; rw [show Averaging.permute s (shelS i k)=shelS (s.perm i) (s.perm k) from pays_rotate _ _,Rolls.scopeY]; exact Needle.quotaY _ _ _ _ _ _ (h _ _)
lemma Flavor_pure : sym.flavor D g  (q (i,k))= q (i,k):=by
       apply Attain.eon A T sym H hH W hA hW (brook A B F u i k) (shelS i k) (q (i,k)) (h i k) g 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=stroll c g; let U':Grid c:=(fun U=>U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i k b U') = Yχ j i k b U:=by
            intro j b; apply aux_g; intro y; let z:=G j i k; let t:= shelC j i k; have hh: sym.flavor 6 g z=z:=by
                apply Subtype.ext; rw [sym.flavorActs]; exact ((sober u j i k).1).2 g
            unfold skyH; have hp: Action.flavor g (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.flavor c (F t z) y g,hf.flavorO,hh]
            exact congr_fun hp U
       change L' ((Vχ i k) b U')=_; unfold brook; rw [Finset.sum_apply, ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma quiet_pure : sym.parity D  (q (i,k))= q (i,k):=by
       apply Attain.dew A T sym H hH W hA hW (brook A B F u i k) (shelS i k) (q (i,k)) (h i k) 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=QCD.Grass.grade; let U':Grid c:=(fun U=>U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i k b U') = Yχ j i k b U:=by
            intro j b; apply aux_g; intro y; let z:=G j i k; let t:= shelC j i k; have hh: sym.parity 6 z=z:=by
                apply Subtype.ext; rw [sym.parityActs]; exact ((sober u j i k).1).1
            unfold skyH; have hp: Action.parity (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.parity c (F t z) y,hf.parityO,hh]
            exact congr_fun hp U
       change L' ((Vχ i k) b U')=_; unfold brook; rw [Finset.sum_apply, ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma sea_pure : sym.charge D  (q (i,k))= q (i,k):=by
       apply Attain.hour A T sym H hH W hA hW (brook A B F u i k) (shelS i k) (q (i,k)) (h i k) 
       intro b; funext U; let L': Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6:=eveN c; let U':Grid c:=(fun U=> conjugate ∘ U) U
       have he: ∀ (j:Axis)(b:Cover), L' (Yχ j i k b U') = Yχ j i k b U:=by
            intro j b; apply aux_g; intro y; let z:=G j i k; let t:= shelC j i k; have hh: sym.charge 6 z=z:=by
                apply Subtype.ext; rw [sym.chargeActs]; exact (sober u j i k).2
            unfold skyH; have hp: Action.charge (B c y (F t z))= ⇑(B c y (F t z)):=by rw [show _=_ from hT.charge c (F t z) y,hf.chargeO,hh]
            exact congr_fun hp U
       change L' ((Vχ i k) b U')=_; unfold brook; rw [Finset.sum_apply, ContinuousMap.sum_apply,ContinuousMap.sum_apply,map_sum]; exact sum_congr rfl fun i _=> he ..
lemma spinal : q ∈ RawTensor (-1) D:=by
    refine ⟨fun i=>⟨?_,fun g=>?_⟩,fun i=>?_,fun s p hp i=>?_,fun i=>?_⟩
    · rw [← RawSym.parityActs,quiet_pure A T sym B hT H hH W hW hA F hf u _ _ q h]
    · rw [← RawSym.flavorActs,Flavor_pure A T sym B hT H hH W hW hA F hf u g _ _ q h] -- args
    · rw [← RawSym.chargeActs,sea_pure A T sym B hT H hH W hW hA F hf u _ _ q h]
    · rcases i with ⟨i,k⟩; rw [← RawSym.pinActs,bridge_pin A T sym B hT H hH W hW hA F hf u s p _ _ q h hp]; rfl
    rcases i with ⟨i,k⟩; let θ:= trolley A (Vχ k i) (shelS k i) 0 0; apply Canvas.consensus T 0 θ (h _ _) ((-1:ℂ) • q (i,k)) _; unfold θ; rw [omega_flip A T sym B hT F hf u, signP k i, Rolls.scopeY]; exact Needle.quotaY _ _ _ _ _ _ (h _ _)
end Onyx.Gourd
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.spinal
