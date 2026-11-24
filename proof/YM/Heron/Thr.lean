import YM.Heron.Yawn
import YM.Heron.Blink
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
noncomputable def deck(i:Pinor):Faces:= Pi.single i 1
lemma deckP(i:Pinor)(q:Faces): dotL (deck i) q=q i:=by simp [bore, dotProduct, deck, Pi.single_apply,ite_mul]
noncomputable def formT (t:Bool):TinG:= if t then FlipT gamma else gamma
abbrev whirT (t:Bool):= formT t
lemma actual(t:Bool): TrueC (formT t):=by cases t; exact learn; exact flips gamma learn
lemma live(t:Bool): formT (!t)=FlipT (formT t):=by cases t<;>rfl
variable (t:Bool)(i j:Pinor)(z:E4)(L M:List Axis)(hz:z ≠0)
local notation "f"=> hull (formT t) (deck i)
local notation "A"=> formT t
include hz
lemma hues : f z j= if t then dirac j i z else dirac i j z :=by
   change -(enD (FlipT A) (stocked 0 0 (deck i)) z j)=_; unfold enD
   let c:Faces:=deck i; have he:0≠z:= hz.symm; have h(a) : grad a (stocked 0 0 (deck i)) z = grad a Maxwell.Green z • deck i:=by rw[bark, soften_zero,sub_zero]; rw[soften_zero,sub_zero]; exact Maxwell.freeSmooth hz
   rw [Finset.sum_apply]; simp_rw [h,map_smul]; cases t
   · change -(∑ x:Axis,_)= -∑ a:Axis,gamma a i j*_ ; apply congr_arg; refine Finset.sum_congr rfl fun i' _=>?_ ; rw [cogP]; change grad i' Maxwell.Green z • (_:ℂ)=_; simp [Matrix.mulVec,dotProduct, deck, Pi.single_apply,mul_ite,grad, Matrix.transpose_apply, formT, FlipT,Complex.real_smul]; ring
   · change -(∑ x:Axis,_)= -∑ a:Axis,gamma a j i*_ ; apply congr_arg; refine Finset.sum_congr rfl fun i' _=>?_ ; rw [cogP]; change grad i' Maxwell.Green z • (_:ℂ)=_; simp [Matrix.mulVec,dotProduct, deck, Pi.single_apply,mul_ite,grad, Matrix.transpose_apply, formT, FlipT,Complex.real_smul]; ring
lemma portH (F G:E4→ ℂ)(hu:F=ᶠ[𝓝 z] G): deriveL L F z=deriveL L G z:=by
  induction L generalizing z with
  | nil=> exact hu.self_of_nhds
  | cons i L ih=> exact GermD _ (((hu.eventuallyEq_nhds).and (eventually_ne_nhds hz)).mono fun y h=> ih y h.2 h.1)
lemma able : deriveL L f z j= if t then derivatives L (dirac j i) z else derivatives L (dirac i j) z :=by
    have he : deriveL L f z j= deriveL L ((dotL (deck j)) ∘ f) z:= by rw [← deckP j (deriveL L f z)]; exact (spiral open_away f (fun y h=>hotH _ _ _ h) L (dotL (deck j)) z hz).symm -- maybe namespace
    rw [he]; apply Eq.trans (b:=deriveL L (fun x=> if t then dirac j i x else dirac i j x) z); apply portH z L hz; filter_upwards [eventually_ne_nhds hz] with x hx; rw [comp_apply,deckP,hues t _ _ x hx]
    cases t<;>rfl
lemma perP : derivatives L (dirac i j) z = (-1:ℂ)^(L.length+1) * derivatives L (dirac i j) (-z):=by
    let h:=dirac i j; induction L generalizing z with
    | nil=>
        change _= (-1:ℂ)^(([]:List Axis).length+1)*_
        have hh(a:Axis) : ((Maxwell.grad a Maxwell.Green z:ℝ):ℂ) = -((Maxwell.grad a Maxwell.Green (-z):ℝ):ℂ):=by
             rw [← soften_zero, soften_first, soften_first, PiLp.neg_apply]; simp; first|ring|skip
             all_goals have ht:=norm_pos_iff.mpr hz; simp [hz]; -- obligations
        change -∑ i':Axis,gamma i' i j* _= (-1:ℂ)^1 *(-∑ i':Axis,gamma i' i j*_); simp only [pow_one, neg_one_mul]; apply congr_arg; change (∑ a:Axis,gamma a i j*_) = -(∑ a:Axis,gamma a i j * _); rw[← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun a _=>?_ ; rw[show (↑(Analysis.D _ Maxwell.Green z):ℂ) =_ from hh a, mul_neg]; rfl --
    | cons a l ih=>
        let F:=deriveL l h; let c:ℂ:=(-1)^(l.length+1) -- alternative
        have hp : F=ᶠ[𝓝 z] fun y=> c*F (-y) := (eventually_ne_nhds hz).mono fun y hy=> ih y hy
        change grad a F z= _*grad a F (-z); rw [List.length_cons, show grad a F z=D (basis a) (fun y=> c*F (-y)) z from GermD _ hp]; unfold grad D; have hF :DifferentiableAt ℝ F (-z):=(balla l h _ open_away (is_hot i j) _ (neg_ne_zero.mpr hz)).differentiableAt (by simp); let B:= -(ContinuousLinearMap.id ℝ E4); let r:ℂ:=(-1)^ (l.length+1)
        rw [show fderiv ℝ (fun y=> c*F (-y)) z (basis a)= _ from (Hail.amen B z F (-z) rfl _ (-(basis a)) rfl hF c)]; rw [map_neg]; change c* (-_) = (-1:ℂ)^_*_; rw[pow_succ', neg_one_mul,neg_mul, mul_neg]
omit hz
variable (p x : E4) (hp:p≠x)(a:Axis)
local notation "P"=>pose A (deck i)
include hp
lemma pearls : deriveL M (P L p) x= ((-1:ℝ)^M.length) • pose A (deck i) (M++L) p x:=by
   induction M generalizing x with
   | nil=> change _= (-1:ℝ)^0 • _; rw[pow_zero,one_smul]; rfl
   | cons a M ih=>
       let Q:= pose (formT t) (deck i) (M++L) p; have hv:ContDiffAt ℝ ∞ Q x:=nicePose A (deck i) p x hp _; let c:ℝ:=(-1)^M.length; change grad a (deriveL M (P L p)) x=(-1:ℝ)^ (M.length+1) • _; have he: deriveL M (P L p) =ᶠ[𝓝 x] (fun y=> c • Q y):=(eventually_ne_nhds (Ne.symm hp)).mono fun y h=> ih y h.symm; rw [grad, GermD _ he]; rw [D, fderiv_fun_const_smul (hv.differentiableAt (by simp))]; change c • grad a Q x= _; rw[loveK, smul_neg,pow_succ',neg_one_mul,neg_smul]; rfl; exact hp
end YM.Heron
#print axioms YM.Heron.able
#print axioms YM.Heron.perP
#print axioms YM.Heron.pearls
