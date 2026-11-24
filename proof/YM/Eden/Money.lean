import YM.Eden.Leaf
import YM.Bloom.Shrimp
import YM.Massive.Ribbon.Ball
/-! # Scaling, earnings.Boot Ph. Precise grade powers.shifts -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m n j:ℕ}{c f:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
-- d stamp price already. grade dilation. use W>0 (can be W=w^n)
noncomputable def stemsP (G:Gauge)(k:ℕ)(w:ℝ) : Lily G k →ₐ[ℂ] Lily G k:= MvPolynomial.aeval fun z:Zinc G k=> (↑(favorU w z):ℂ) • (MvPolynomial.X z)
noncomputable def gateP (d:ℕ)(w:ℝ) : Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ:= Matrix.diagonal (fun i=> (w:ℂ)^letterWeight i)
noncomputable def padU (k:ℕ)(w:ℝ) : Module.End ℂ (Bard k):= TensorProduct.map (stemsP su k w).toLinearMap (changeVars (gateP k w)).toLinearMap
variable (L:ℝ)
lemma weighed(q:Grimo d):(padU d L) (sketch q)=(L:ℂ)^((tagwt q).1.1) • sketch q:=by
    unfold padU sketch; rw[TensorProduct.map_tmul]; let k:=q.1; let f:Finsupp (Tube su d) ℕ:=k
    let Z: Lily su d:=MvPolynomial.monomial k 1; have he: stemsP su d L Z=(L:ℂ)^(2*(Finsupp.weight legwt k).1) • Z:=by
        unfold Z; rw [MvPolynomial.monomial_eq]; simp_rw [map_mul,MvPolynomial.C_1,one_mul,map_one,one_mul, Finsupp.prod,map_prod,map_pow]; unfold stemsP; simp_rw [MvPolynomial.aeval_X,smul_pow, favorU,pongs]; rw[Finset.prod_smul]; congr 1
        simp_rw [Complex.ofReal_pow,← pow_mul]; rw[prod_pow_eq_pow_sum,Finsupp.weight_apply,Finsupp.sum, Prod.fst_sum, Finset.mul_sum]; congr 1; apply sum_congr rfl; intro i _; change (4+2*↑i.1.1)*k i=2*(k i*(↑i.1.1+2)); ring
    change stemsP su d L Z ⊗ₜ[ℂ] changeVars _ _= _
    have hx:gateP d L= Matrix.diagonal fun i:Pairs (SpinMode d)=> ((↑(L ^ letterWeight i):ℂ)):=by ext i j; by_cases he:i=j <;> simp[gateP,he, Matrix.diagonal_apply]
    have hv:changeVars (gateP d L)=endor L:=by unfold endor adapter; apply congr_arg; ext (i|i) (j|j) <;> simp only [gateP,SourceRead.scaled,Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂] <;> by_cases h:i=j <;> simp [h,UV.letterWeight]
    rw [he,hv,pieces]; unfold tagwt; dsimp only; rw [← TensorProduct.smul_tmul',← TensorProduct.tmul_smul,pow_add,smul_smul,TensorProduct.tmul_smul]; rfl

lemma rates (x:Bard d)(h:x∈Rgl d n i j): padU d L x=(L:ℂ)^n • x:=by
     refine Submodule.span_induction (p:=fun x _=>padU d L x=(L:ℂ)^n • x) ?_ (by simp) (fun x y _ _ hx hy=>by rw[map_add,hx,hy, smul_add]) (fun r x _ h=>by rw[map_smul,h,smul_comm]) h
     rintro x ⟨s,h,rfl⟩; rw[weighed,show tagwt s=_ from h]
lemma shines_g (P:Lily G d)(s:Signed):stemsP G d L (posedK s P)=posedK s (stemsP G d L P):=by
    apply DFunLike.congr_fun (f:=(stemsP G d L).comp (posedK s)) (g:= (posedK s).comp (stemsP G d L)) _ P; ext1 i; simp only [AlgHom.comp_apply,stemsP,posedK,MvPolynomial.aeval_X,map_smul]; rw [smul_comm]; unfold favorU; rw [pongs,pongs]; rfl
lemma burns_g (P:Lily G d): stemsP G d L (MvPolynomial.map (starRingEnd _) P)=MvPolynomial.map (starRingEnd _) (stemsP G d L P):=by
    induction P using MvPolynomial.induction_on with
    | C a=> simp [stemsP]
    | add a b h hp=>rw [map_add,map_add,h,hp,map_add,map_add]
    | mul_X x i h=> rw [map_mul,map_mul,map_mul,map_mul,h,MvPolynomial.map_X]; congr 1; rw[stemsP,MvPolynomial.aeval_X,← MvPolynomial.C_mul']; simp -- simp
lemma flowing (P:Lily G d)(u:G.Color→ₗ[ℝ] G.Color): stemsP G d L (pigmentK u P) = pigmentK u (stemsP G d L P):=by
    apply DFunLike.congr_fun (f:=(stemsP G d L).comp (pigmentK u)) (g:= (pigmentK u).comp (stemsP G d L)) _ P; ext1 i; simp only [AlgHom.comp_apply, pigmentK,stemsP,MvPolynomial.aeval_X,map_sum,map_smul]; rw[smul_sum]; refine sum_congr rfl (fun j _=>?_); rw[smul_comm]; rfl
lemma wagesS (P:Matrix (Sings k) (Sings k) ℂ)(h:∀ i j,letterWeight i≠letterWeight j→P i j=0): gateP k L* P=P*gateP k L:=by
     ext i j; unfold gateP; rw[Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases he:letterWeight i=letterWeight j; rw[he,mul_comm]; rw [h _ _ he,zero_mul,mul_zero]
lemma dignity : Mstar (gateP k L)=gateP k L:=by ext i j; by_cases h:i=j <;> simp [gateP,Matrix.diagonal_apply,h,Mstar]
noncomputable abbrev gradientE (k:ℕ)(u:FlavorTorus): Matrix (Sings k) (Sings k) ℂ:= QCD.Eden.slab (byFlavor u (fun i:SpinMode k=>i.2))
lemma ingots(P:Matrix (Sings k) (Sings k) ℂ)(h:∀ i j,letterWeight i≠letterWeight j→P i j=0)(X:SpinPol k): changeVars P (changeVars (gateP k L) X)= changeVars (gateP k L) (changeVars P X):=by rw [multipleChange,multipleChange, wagesS _ _ h]
lemma wagesFlavor (u:FlavorTorus) (i j:Sings k)(h:letterWeight i≠ letterWeight j): gradientE k u i j=0:=by
    unfold gradientE QCD.Eden.slab; have hi:i≠j:=fun he=> h (congr_arg _ he); cases i <;> cases j <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,mstar_sq, Matrix.zero_apply,byFlavor]; all_goals simp at hi; simp [Matrix.diagonal_apply, hi, Ne.symm hi, Matrix.star_eq_conjTranspose]
lemma wagesPin (s:Signed)(P: EuPin) (i j:Sings k)(h:letterWeight i≠ letterWeight j): pinTT k s P i j=0:=by
    unfold pinTT; rcases i with i|i<;> rcases j with j|j <;> first| rfl| exact trails _ _ _ _ h
lemma wagesColor (z:su.El)(i j:Sings k)(h:letterWeight i≠letterWeight j): noir z k i j=0:=by
    unfold noir; rw [alcohol, groom]; rcases i with i|i <;> rcases j with j|j <;> first|rfl|exact trails _ _ _ _ h
end YM.Eden
#print axioms YM.Eden.weighed
#print axioms YM.Eden.ingots
