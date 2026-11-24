import YM.Eden.Opera
/-! # mixed tag parity preservation on true unweighted label.T.Choose Slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Filter Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP Arise.Bill
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r g q N:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit
open MassiveQCD.Inky
variable (p:UV.Pol d)
lemma boarded (h: p∈ Rtg d k g q):∃ P:Cups d (Gallery.polarity q),fareC d (Gallery.polarity q) P=introduce d p:=by
    let f:=fareC d (Gallery.polarity q); let U:= f.range; suffices he:introduce _ p∈ U from he
    refine Submodule.span_induction (p:=fun p _=>introduce d p∈U) ?_ (by simp) (fun a b _ _ h hp=>by rw [map_add]; exact U.add_mem h hp) (fun i x _ h=>by rw[map_smul]; exact U.smul_mem _ h) h
    rintro _ ⟨P,h,rfl⟩; obtain ⟨h1,h2,h3⟩:=h; let X:= mono P.2; have ht:X ∈Grace d (Gallery.polarity q):=by
        have hh:=grade_mono P.2; rw [h3] at hh; by_cases h: Odd q; · rw [show Gallery.polarity q=true from decide_eq_true h]; change Grass.grade X= -X ; rw [h.neg_one_pow,neg_one_smul] at hh; exact hh
        rw [show Gallery.polarity q=false from decide_eq_false h]; change Grass.grade X=X; rw[(Nat.not_odd_iff_even.mp h).neg_one_pow,one_smul] at hh; exact hh
    refine ⟨loCast su d (MvPolynomial.monomial P.1 1) ⊗ₜ[ℂ] (⟨X,ht⟩: Grace d (Gallery.polarity q)),?_⟩; unfold f fareC introduce UV.gen; rw[TensorProduct.map_tmul,TensorProduct.map_tmul]; rfl
lemma parcelO (b:Bool) (p:Cups d b): meaning d b p=revere d (fareC d b p):=by
   induction p using TensorProduct.induction_on with
   | zero=>simp
   | add x y hx hy=>rw[map_add,map_add,map_add,hx,hy]
   | tmul p q=> unfold meaning fareC revere; rw[TensorProduct.map_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul]; rfl
lemma mo_P (p:PowerPair d)(e:∀ i,Module.End ℝ (Labels.Taylor su i))(y:SpinPol d) (hc: y∈ layer (Pairs (SpinMode d)) p.2.card)(hz:y∈ UV.Rim.grains _ letterWeight (∑ i∈ p.2, letterWeight i)) : Labels.changed e (MvPolynomial.monomial p.1 1)⊗ₜ[ℂ] y∈ Rtg d (UV.weight p) (Poised.Sieve.life p.1) p.2.card:=by
      let w:= Labels.changed e (MvPolynomial.monomial p.1 1); let V:= Rtg d (UV.weight p) (Poised.Sieve.life p.1) p.2.card; change w⊗ₜ[ℂ]y∈_; rw [w.as_sum,TensorProduct.sum_tmul]; refine V.sum_mem fun i hi=> ?_; rw [← Grass.write y,TensorProduct.tmul_sum]; refine V.sum_mem fun j _ =>?_; rw [TensorProduct.tmul_smul];
      by_cases he:(coef j y)=0; rw [he,zero_smul]; exact V.zero_mem;
      have hj:j.card=p.2.card:= Classical.byContradiction fun h=>he (Grass.spectrum hc j h); have hm : ∑ i∈j,letterWeight i=∑ i∈p.2,letterWeight i:=Classical.byContradiction fun h=>he ((UV.Rim.grain_test ..).mp hz j h); apply V.smul_mem; rw[show (MvPolynomial.monomial i (MvPolynomial.coeff i w))=(MvPolynomial.coeff i w) • (MvPolynomial.monomial i 1:GPol) from (by rw [←map_smul,smul_eq_mul,mul_one]),← TensorProduct.smul_tmul']; apply V.smul_mem
      have ht:= Labels.pure_moved (fun i=> i+2) e p.1 1 (MvPolynomial.mem_support_iff.mp hi); have hv:= Labels.pure_moved (fun _=> (1:ℕ)) e p.1 1 (MvPolynomial.mem_support_iff.mp hi); have hh:Labels.height i=Labels.height p.1:=ht; refine Submodule.subset_span ⟨(i,j),⟨show 2*Labels.height i+ _=_ from (?_), show life i= life p.1 from (?_),hj⟩,rfl⟩
      · change 2*Labels.height i+ _=2*Labels.height p.1+ _; rw [hm,hh]
      unfold Poised.Sieve.life; simpa only [Finsupp.weight_apply,Finsupp.sum, nsmul_eq_mul,mul_one,Nat.cast_id] using hv
lemma twilight_Q (a:Axis)(h:p∈Rtg d k g q): UV.adj a p∈ Rtg d k g q:=by
     refine Submodule.span_induction ?_ (by rw[map_zero]; exact Submodule.zero_mem _) (fun x y _ _ h hp=>by rw[map_add]; exact Submodule.add_mem _ h hp) (fun i x _ h=>by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ h) h
     rintro x ⟨i,h,rfl⟩; obtain ⟨rfl,rfl,rfl⟩:=h; unfold UV.adj UV.gen; rw [TensorProduct.map_tmul]; change Labels.rotated _ (Labels.conjPol _) ⊗ₜ[ℂ] (aSpin d a (mono i.2))∈ _; rw [Labels.conjPol,MvPolynomial.map_monomial,map_one]; apply mo_P; · exact exterior_layer _ (Grass.dagger_degree (Grass.homogeneous i.2))
     exact UV.Rim.step letterWeight (f:=(changeVars _).toLinearMap) (UV.Rim.keeps _ (eyeTracks _)) (UV.Rim.dkeeps _ _ _ rfl)
lemma reflected (a:Axis)(X:RawSym) (p:UV.Label d)(h:p.val∈ Rtg d k g q): (X.adj d a p).val ∈ Rtg d k g q:= X.adjActs d a p |>.symm ▸ twilight_Q p.val a h
lemma canCut (K: Poised.Plans.Grade)(p:UV.Pol d): Poised.Plans.kind d K p∈ Rtg d K.1 K.2.1 K.2.2:=by
    let B:= Poised.Display.zBasis d; rw [← B.linearCombination_repr p]; simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]; apply Submodule.sum_mem; intro i hi; apply Submodule.smul_mem; rw [show B i= _ from Poised.Display.minted i,Poised.Plans.kind_gate]; split; swap; · exact Submodule.zero_mem _
    next h=> rw [← h]; exact Submodule.subset_span ⟨i,⟨rfl,rfl,rfl⟩,rfl⟩
end YM.Massive.Evo
#print axioms YM.Massive.Evo.reflected
#print axioms YM.Massive.Evo.boarded
