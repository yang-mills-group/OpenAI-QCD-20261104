import YM.Poised.Fund
import YM.QCD.Dust.Pages
/-!
# Vector Moves, any panel image; uniform row currency.
# Ember analytic composing old and new spin jets; width-tests keep exact exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n r:ℕ}{c:Side}
namespace Pipes
open Pointwise Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre
section finance
variable {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y] {V:Support c} {P:BudgetPoint}{F:Grid c → Y}{x:Directions su c}{t:ℝ}{U:Grid c}{o:Site c}
lemma pest (h:Ease.Charm P V F)(he : Healthy P.threshold V (increment U x)) : ContDiffAt ℝ P.order (F ∘ increment U) x:=by
    let B:=Module.finBasis ℝ Y; let L i:= (B.coord i).toContinuousLinearMap; let X:= F∘increment U
    rw [show F ∘ increment U=(fun p=>∑ i,L i (X p) • B i) from funext fun i=> (B.sum_repr _).symm]; apply ContDiffAt.sum; intro i _; exact (Hera.along (h.scales (L i)) he).smul contDiffAt_const
variable (H : Hera.Rights su n)(hp:Ease.Charm P V F)(hb:P.supBounds o V F t)(hr:r ≤ n)(he:r ≤ P.order)(u : Fin r→Directions su c)(f : Fin r→ ℝ)(hg : ∀ i,Sized (f i) (u i) P o)
include H hp hb hr he hg
lemma voyager (ht:Healthy P.threshold V (increment U x)) (hx : ∀ i,Mom.needed V i→ ‖x i‖≤1∧width P o i≤1) : ‖iteratedFDeriv ℝ r (F ∘ increment U) x u‖ ≤ (∏ i,f i)*H.fee*t:=by
   let A:= iteratedFDeriv ℝ r (F ∘ increment U) x u
   by_cases hy:A=0; · change ‖A‖ ≤ _; rw [hy,norm_zero]; exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=> (hg i).1) (zero_le_one.trans H.large)) hb.1
   obtain ⟨L,hL,hY⟩:= exists_dual_vector ℝ A (norm_ne_zero_iff.mpr hy); have hx' : ‖A‖=‖iteratedFDeriv ℝ r ((L∘F) ∘ increment U) x u‖:=by
        have h0:= L.iteratedFDeriv_comp_left (pest hp ht) (Nat.cast_le.mpr he); rw [show iteratedFDeriv ℝ r ((L∘F) ∘ increment U) x u=L A from DFunLike.congr_fun h0 u]; change L A=‖A‖ at hY; rw [hY,Real.norm_of_nonneg (norm_nonneg _)]
   apply le_trans hx'.le; apply H.moves U x u f hr he (hp.scales L) _ ht hx hg; refine ⟨hb.1,fun X hU l hl hv=>?_⟩; rw [Push.Local.left_linear L _ (hp.smooth X hU) hl]; exact (L.le_opNorm _).trans (hL ▸ (one_mul _).le.trans (hb.2 X hU l hl hv)) -- eq
-- linear pullback on translated path
end finance
private lemma stepped_affine {X Y Z:Type*} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y] [NormedAddCommGroup Z][NormedSpace ℝ Z](L : X→L[ℝ]Y)(g:Y→Z)(x:Y)(hf:ContDiffAt ℝ (↑k) g x) : iteratedFDeriv ℝ k (fun y=>g (x+ L y)) 0=(iteratedFDeriv ℝ k g x).compContinuousLinearMap (fun _=>L):=by
   let A(y:Y):=g (x+y); have ht:ContDiffAt ℝ (↑k) A 0:= (show ContDiffAt ℝ k g (x+0) by rw [add_zero]; exact hf).comp (f:=fun y=>x+y) _ (contDiffAt_const.add contDiffAt_id)
   have he:= YM.Next.Foundations.jets_linear L ht; unfold A at he; rw [iteratedFDeriv_comp_add_left, add_zero] at he; exact he
local notation "A₀"=> Faces (Site c)
variable (F:Grid c→ Lat.Fields c 6) [Fintype B] (x: Path c B){P:BudgetPoint}(f : Faces (Site c) → ℝ) (g:B→ℝ)
variable (Q:Hera.Rights su n){V:Support c}{o:Site c}{p C t:ℝ}
variable (hf:Ease.Charm P V F) (hg:P.supBounds o V (framesF f∘F) t) (he:∀ i,0<f i)(hp:Healthy P.threshold V (increment 1 x.1))(hW:∀ i,Mom.needed V i → ‖x.1 i‖≤1∧width P o i ≤ 1)
include hf hg Q he hp hW
variable [NormedAddCommGroup E][NormedSpace ℝ E]
set_option quotPrecheck false
private lemma embersV (L:E→L[ℝ]Directions su c) (hr:r ≤ n)(ht:n ≤ P.order)(hC:1 ≤ C)(hX:∀ i,Sized (C*‖i‖) (L i) P o) : Ember r (fun i=> framesF f (F (increment 1 (x.1+L i)))) ((C^r*Q.fee)*t):=by
   let T:=framesF f∘F; have hG: ContDiffAt ℝ r (T ∘ increment 1) (x.1+L 0):=by rw [map_zero,add_zero]; exact (pest (hf.scales (framesF f)) hp).of_le (Nat.cast_le.mpr (hr.trans ht))
   have hz:=Q.large; have hs:=hg.1
   refine ⟨hG.comp (f:=fun i=>x.1+L i) _ (contDiffAt_const.add L.contDiff.contDiffAt),by positivity,fun j hj=>?_⟩
   rw [map_zero,add_zero] at hG; have ht := stepped_affine (k:=j) L (T∘increment 1) x.1 (hG.of_le (Nat.cast_le.mpr hj))
   rw [show iteratedFDeriv ℝ j (fun i=>framesF f (F (increment 1 (x.1+L i)))) 0= _ from ht]
   refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v=> ?_
   apply (voyager Q (hf.scales _) hg (hj.trans hr) (hj.trans (hr.trans (by assumption))) (L ∘ v) (fun i=>C*‖v i‖) (fun i=> hX (v i)) hp hW).trans
   rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]; calc
     _=C^j*Q.fee*t*∏ i, ‖v i‖:=by ring
     _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hj) (zero_le_one.trans Q.large)) hs) (prod_nonneg fun _ _=>norm_nonneg _)
omit hf hg Q he hp hW

private lemma sync [DecidableEq A][Fintype A](Z:Alg A)(n:ℕ)(h:Z∈ layer A n): panel n Z=Z:= by rw [past _ _ h,if_pos rfl]
def Venture (w:ℝ)(u:Path c B) : Prop:= Sized w u.1 P o ∧SeatD f g u.2 w -- takes implicit H? 
abbrev mouth (C:ℝ)(Q:Hera.Rights su n)(r d:ℕ):= 2^r*(2^r*(C+C))^d*(C^r*Q.fee)
include hf hg Q he hp hW
lemma affordable (d:ℕ)(A:E→L[ℝ] Path c B)(hr:r ≤ n)(ht:n ≤ P.order)(h:∀ V:Grid c,F V∈layer A₀ d)(hv:∀ y,Sized (C*‖y‖) (A y).1 P o)(hy:SeatD f g x.2 C) (hX:∀ y,SeatD f g (A y).2 (C*‖y‖))(hC:1≤C) : Ember r (fun y=> framesF g (lotsF F (x+A y))) (mouth C Q r d*t):=by
   let L' := (ContinuousLinearMap.snd ℝ (Directions su c) (VectorD (Site c) B)).comp A; let R := (ContinuousLinearMap.fst ℝ (Directions su c) (VectorD (Site c) B)).comp A
   have he' : (fun y=> framesF g (lotsF F (x+A y)))=(fun y=>banner (orderR f g (x.2+L' y)) d (framesF f (F (increment 1 (x.1+R y))))) :=by
      funext y; let z:=F (increment 1 (x.1+R y)); let M:=x.2+L' y; change wscale g (changeVars M z)=changeVars _ (panel d _); rw [← equivalent_scale f he, ← frames_panel (f:=f) _ (n:=d), sync z d (h _)]; rfl
   rw [he']; have hx:= affine_panel f g x.2 L' C C hy hX (zero_le_one.trans hC) (n:=r) (d:=d)
   apply (renamed (weakening (budgeted_app r _ _ _ _ hx (embersV F x f Q hf hg he hp hW R hr ht hC hv)) _) _) -- redundant renamed
   · unfold mouth; apply le_of_eq; ring
   exact EventuallyEq.rfl
omit hf hg Q he hp hW
namespace Venture
lemma scaledM (p:ℝ)(h: Venture f g (P:=P) (o:=o) C x): Venture f g (P:=P) (o:=o) (‖p‖*C) (p • x):=by
   refine ⟨⟨mul_nonneg (norm_nonneg _) h.1.1,fun i=>?_⟩,SeatD.scaledR f g x.2 _ h.2 p⟩
   change ‖p • (x.1 i)‖≤_; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.1.2 _) (norm_nonneg _)
omit [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma togetherM (p:E→Path c B)(t:E→ℝ)(I: Finset E)(h:∀ i∈I,Venture f g (P:=P) (o:=o) (t i) (p i)): Venture f g (P:=P) (o:=o) (∑ i∈I,t i) (∑ i∈I,p i):=by
   refine ⟨⟨Finset.sum_nonneg fun i hi=>(h i hi).1.1,fun i=>?_⟩,?_⟩
   · rw [Prod.fst_sum, Finset.sum_apply, Finset.sum_mul]; exact (norm_sum_le _ _).trans (sum_le_sum (fun j hj=> (h j hj).1.2 i))
   rw [Prod.snd_sum]; exact SeatD.bills f g _ _ _ (fun i hi=> (h i hi).2)
lemma absorbedM (h: Venture f g (P:=P) (o:=o) C x)(he:C≤p): Venture f g (P:=P) (o:=o) p x:= ⟨⟨h.1.1.trans he,fun i=>le_trans (h.1.2 i) (mul_le_mul_of_nonneg_right he (width_pos ..).le)⟩,SeatD.less _ _ _ _ _ h.2 he⟩
end Venture
lemma sighted (F:Grid c→ Lat.Fields c 6)(hv:Ease.Charm P V F)(ht:Healthy P.threshold V (increment 1 x.1))(h:n≤P.order) : ContDiffAt ℝ n (framesF g∘ lotsF F) x :=by
    apply (framesF g).contDiff.contDiffAt.comp (f:=lotsF F); exact aperture ((F∘increment 1) ∘ Prod.fst) Prod.snd x _ (((pest hv ht).of_le (Nat.cast_le.mpr h)).comp _ contDiffAt_fst) contDiffAt_snd
include hf hg Q he hp hW
lemma shellW (d:ℕ)(h:∀ V:Grid c,F V∈layer A₀ d)(hr:r≤n)(ht:n≤P.order)(hy:SeatD f g x.2 C) (Y:Fin r→Path c B)(hv:∀ i:Fin r, Venture (P:=P) (o:=o) f g 1 (Y i)) :
    ‖iteratedFDeriv ℝ r (framesF g ∘ lotsF F) x Y‖ ≤ mouth (1+n+C) Q r d*t:=by
    have hC:=hy.1; let N:ℝ:=1+n+C; have hN:1≤N:=by unfold N; linarith [Nat.cast_nonneg (α:=ℝ) n]
    let X : (Fin r→ℝ) →L[ℝ] Path c B := ∑ i,(ContinuousLinearMap.proj (R:=ℝ) i).smulRight (Y i); have hs (v : Fin r→ℝ) : X v=∑ i,v i • Y i := by simp [X]
    have hX(v):Venture f g (P:=P) (o:=o) (N*‖v‖) (X v):=by
       rw [hs]; refine Venture.absorbedM _ f g (Venture.togetherM f g _ _ _ (fun i _=> Venture.scaledM (Y i) _ _ (v i) (hv i))) ?_
       refine (sum_le_sum (g:=fun _=> ‖v‖) fun i _=> by rw [mul_one]; exact norm_le_pi_norm ..).trans ?_; rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (le_trans (Nat.cast_le.mpr hr) (by unfold N; linarith)) (norm_nonneg _)
    have hu:= affordable F x f g Q hf hg he hp hW d X hr ht h (fun i=>(hX i).1) (SeatD.less _ _ _ _ _ hy (by unfold N; linarith [Nat.cast_nonneg (α:=ℝ) n])) (fun i=>(hX i).2) hN
    let q:= framesF g ∘ lotsF F
    have hh:= hu.2.2 r le_rfl
    change ‖iteratedFDeriv ℝ r (fun y=>q (x+X y)) 0‖ ≤ _ at hh; rw [stepped_affine X q x (sighted x g F hf hp (hr.trans ht))] at hh
    let W (i:Fin r): Fin r→ℝ:= Pi.single i (1:ℝ); let R := iteratedFDeriv ℝ r q x; have hp':∀ i,Y i=X (W i):=fun i=> by simp [hs,W,Pi.single_apply,ite_smul]
    rw [show (iteratedFDeriv ℝ r (framesF g ∘ lotsF F) x) Y=(R.compContinuousLinearMap (fun _=>X)) W from congr_arg R (funext hp')]
    exact (ContinuousMultilinearMap.unit_le_opNorm _ (show ‖W‖ ≤ 1 from (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=> by simp only [W, Pi.single_apply]; split <;> norm_num)).trans hh
lemma risingW (d:ℕ)(h:∀ V:Grid c,F V∈layer A₀ d)(hr:r≤n)(ht:n≤P.order)(hy:SeatD f g x.2 C) (Y:Fin r→Path c B)(w: Fin r→ ℝ)(hX:∀ i,0 < w i)(hv:∀ i:Fin r, Venture (P:=P) (o:=o) f g (w i) (Y i)) :
    ‖iteratedFDeriv ℝ r (framesF g ∘ lotsF F) x Y‖ ≤ (∏ i,w i)*mouth (1+n+C) Q r d*t:=by
    let p i:=(w i)⁻¹ • Y i; rw [show Y=(fun i=>w i • p i) from funext fun i=> by unfold p; rw [smul_inv_smul₀ (hX i).ne'],ContinuousMultilinearMap.map_smul_univ,norm_smul]; have hw:0 ≤ ∏ i,w i:= prod_nonneg fun i _=> (hX i).le; rw [Real.norm_of_nonneg hw,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hw; refine shellW F x f g Q hf hg he hp hW d h hr ht hy p fun i=> ?_
    have h:= Venture.scaledM (Y i) f g ((w i)⁻¹) (hv i); rw [Real.norm_of_nonneg (inv_pos.mpr (hX i)).le, inv_mul_cancel₀ (hX i).ne'] at h; exact h
end Pipes
end YM.Massive.Poised
