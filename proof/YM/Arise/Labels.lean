import YM.Arise.Volts
import YM.Arise.Rex
/-! # Ambient label morphisms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Labels Maxwell
variable {r n m i j k d:ℕ}
variable {G : Gauge}
local notation "aₜ" => G.Color
-- explicit polynomial section all gauge colors ANY d.
abbrev Lily (G:Gauge)(d:ℕ):=MvPolynomial (Tube G d) ℂ
noncomputable def nestK (Y: Ink G d): Lily G d→ₐ[ℂ]ℂ:=MvPolynomial.aeval fun i=>(Y i:ℂ)
lemma futon (p q:Lily G d)(h:∀ X: Ink G d, nestK X p=nestK X q):p=q:=by
    refine MvPolynomial.funext_set (fun _ => Set.range fun x:ℝ=> (x:ℂ)) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective) ?_; intro x hx; choose f hf using fun i=> hx i (Set.mem_univ i); rw [show x=fun i=>(f i:ℂ) from funext fun i=>(hf i).symm]; exact h f
-- order grade center, no radial kernel here.
noncomputable def loCast (G: Gauge)(d:ℕ) : Labels.Pol G→ₐ[ℂ] Lily G d := MvPolynomial.aeval fun i:Labels.Key G=> ∑ k: Tube G d, MvPolynomial.C (Labels.coord (phone d G (Pi.single k 1)) i)*MvPolynomial.X k
noncomputable def rollK (G:Gauge)(d:ℕ): Lily G d→ₐ[ℂ] Labels.Pol G := MvPolynomial.aeval fun k:Tube G d=> ∑ i: Fin (Labels.dim G k.1.1.val), MvPolynomial.C ((rootLeg (axes G k.1.1.val i) k.1.2 k.2:ℝ):ℂ)* MvPolynomial.X ⟨k.1.1.val,i⟩
lemma postK(X:Ink G d): (nestK X).comp (loCast G d)=Labels.read (phone d G X):=by
     have h:X=∑ i:Tube G d,X i • Pi.single i 1:=funext fun i=> by simp [Pi.single_apply]
     -- maybe done
     ext z; rcases z with ⟨j,i⟩; simp only [AlgHom.comp_apply, loCast,MvPolynomial.aeval_X,map_sum,map_mul,nestK,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,Labels.read]
     unfold Labels.coord phone; nth_rw 2 [h]; -- X occ either all.Type.G
     simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Complex.ofReal_sum, Complex.ofReal_mul]; exact sum_congr rfl fun v _=>mul_comm _ _
lemma hillG (Y:Jet G)(d:ℕ): (Labels.read Y).comp (rollK G d) = nestK (pub d G Y):=by
    ext k; simp only [AlgHom.comp_apply, rollK,MvPolynomial.aeval_X,map_sum,map_mul,Labels.read, MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,nestK]
    rcases k with ⟨⟨⟨n,hn⟩,p,v⟩,a⟩; let K := (p,v); let F(x:Taylor G n):ℝ:= rootLeg x (p,v) a; let B:=axes G n; change ∑ i, (F (B i):ℂ)* ((↑(B.repr (Y n) i):ℂ)) = ↑(F (Y n)); let X:= Y n
    let L: Taylor G n →ₗ[ℝ]ℝ:= (Nat.factorial n) • ((((EuclideanSpace.proj a).toLinearMap ∘ₗ (ContinuousMultilinearMap.apply ℝ (fun _: Fin n=>E4) G.Color (basis ∘ v)).toLinearMap) ∘ₗ (LinearMap.proj p.val.2)) ∘ₗ (LinearMap.proj p.val.1) ∘ₗ ((formSpace n G.Color).subtype ∘ₗ potential.toLinearMap))
    have he(s:Taylor G n):F s=L s:=rfl
    simp_rw [he]; conv_rhs=> rw [← B.sum_repr (Y n),map_sum]
    simp only [map_smul,smul_eq_mul,Complex.ofReal_sum, Complex.ofReal_mul]; exact sum_congr rfl fun _ _=>mul_comm _ _
lemma returnsX (v: Labels.Key G →₀ℕ)(h:Labels.height v≤d)(x:ℂ) : rollK G d (loCast G d (MvPolynomial.monomial v x))=MvPolynomial.monomial v x:=by
    open MvPolynomial in
      apply Labels.eval_ext; intro Y; rw [← AlgHom.comp_apply,hillG, ← AlgHom.comp_apply,postK (pub d G Y)]; change Labels.read _ _=Labels.read _ _; rw [monomial_eq,map_mul,map_mul,Labels.read, Labels.read,MvPolynomial.aeval_C, MvPolynomial.aeval_C]; congr 1
      unfold Finsupp.prod; rw [map_prod,map_prod]; refine prod_congr rfl fun i hi=>?_ ; rw [map_pow,map_pow,MvPolynomial.aeval_X,MvPolynomial.aeval_X]; unfold Labels.coord; rw [minted d G _ (?_)]
      have hz:Labels.generation i≤ Labels.height v:=by have hL:=single_le_sum (f:=fun i=>v i • Labels.generation i) (fun i _=>Nat.zero_le _) hi; exact le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))) hL
      unfold Labels.generation at hz; omega
variable {E:Type}
section
noncomputable def stainK (s:Signed)(k:Tube G d): ℝ:=petal s k.1.2.1 (List.ofFn k.1.2.2)
noncomputable def tideK (s: Signed)(k:Tube G d): Tube G d:=(⟨k.1.1,swing s k.1.2⟩,k.2)
noncomputable def swingK (s:Signed)(X:Ink G d): Ink G d:= fun i=>stainK s i*X (tideK s i)
lemma moving (s:Signed)(X:Ink G d): phone d G (swingK s X) i= Taylor.turn (s.ortho)⁻¹ (phone d G X i):=by
       have ht(h:d < i)(X:Ink G d):phone d G X i=0:=by rw [phone,spinA,LinearMap.comp_apply,show scrim _ _ _ X=0 from dif_neg (not_le_of_gt h),map_zero] -- whitespace
       by_cases hp:i ≤ d; swap; · rw [ht (lt_of_not_ge hp), ht (lt_of_not_ge hp),map_zero]
       change wheel (stripeJ G d i _)=Taylor.turn _ (wheel (stripeJ G d i X)); rw [show stripeJ _ _ _ _= tiltZ s (stripeJ G d i X) from ?_,motes]
       funext a; unfold tiltZ stripeJ; rw [dif_pos hp,dif_pos hp]; ext k; rfl
noncomputable def posedK (s:Signed): Lily G d→ₐ[ℂ] Lily G d:=MvPolynomial.aeval fun i=> (↑(stainK s i):ℂ) • MvPolynomial.X (tideK s i)
lemma swirls (s: Signed)(X: Ink G d)(p:Lily G d): nestK X (posedK s p)=nestK (swingK s X) p:=by
    suffices h:(nestK X).comp (posedK s)=nestK (swingK s X) from DFunLike.congr_fun h p
    ext i; rw [AlgHom.comp_apply,posedK,MvPolynomial.aeval_X,map_smul,nestK,MvPolynomial.aeval_X,nestK,MvPolynomial.aeval_X, swingK,Complex.ofReal_mul]; rfl
lemma poles_eq (s:Signed)(v:Pol G):posedK s (loCast G d v)=loCast G d (Labels.rotated s.ortho v):=by
    apply futon; intro X; rw [swirls, ← AlgHom.comp_apply,← AlgHom.comp_apply, postK (swingK s X), postK X]; unfold rotated; rw [Labels.eval_changed]; apply congr_arg (fun x :Jet G=>Labels.read x v); exact funext (fun i=> moving (i:=i) s X)
lemma real_back (v:Pol G): loCast G d (conjPol v)=MvPolynomial.map (starRingEnd _) (loCast G d v):=by
     apply futon; intro X; rw [← AlgHom.comp_apply,postK X, Labels.conj_value,← postK X]; let p:=loCast G d v; change star (nestK X p)=nestK X _
     suffices h:∀ p: Lily G d,star (nestK X p)=nestK X (MvPolynomial.map (starRingEnd _) p) from h p
     intro p; induction p using MvPolynomial.induction_on with
     | C a=> simp [nestK]
     | add a b h hp=> rw [map_add,map_add,map_add,star_add,h,hp]
     | mul_X a i h=> rw [map_mul,map_mul,map_mul,star_mul',h,MvPolynomial.map_X,nestK,MvPolynomial.aeval_X]; simp
end
end YM.Arise.Range
#print axioms YM.Arise.Range.returnsX
#print axioms YM.Arise.Range.poles_eq
