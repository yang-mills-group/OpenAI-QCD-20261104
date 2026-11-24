import YM.Play.Lago
import YM.Play.Joints
import YM.Play.Quick
/-! Cumulative cut excursion and its normalized tag semantics. -/
set_option autoImplicit false
noncomputable section
namespace YM.Vest
open Function MvPolynomial
open scoped BigOperators ContDiff Classical
open QCD QCD.Creek QCD.Bera QCD.Anomaly QCD.Grass QCD.Cove Finset Next.Rank Next.Rank.Normal
variable {A B C D U V X Y Z I:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype U][Fintype V][Fintype X][Fintype Y][Fintype Z][Fintype I]
-- regulator kernel facing both.
structure Tone (A X B Y: Type)[Fintype A][Fintype X][Fintype B][Fintype Y] where
    P:Matrix A B ℂ
    Q:Symmetric A
    M:Matrix X Y ℂ
    V:Matrix X X ℂ
namespace Tone
variable (T:Tone A X B Y)(S:Tone B Y C Z)
def after : Tone A X C Z:=⟨T.P*S.P,scope (spool T.P) S.Q+T.Q,T.M*S.M,T.M*S.V*T.M.transpose+T.V⟩
def read : Papers A (Patio X)→ₗ[ℂ] Papers B (Patio Y):=shootsW T.P T.Q T.M T.V
lemma spree (p:poly A)(x:Patio X) : T.read (outer p x)=outer (Normal.pipe (spool T.P) T.Q p) (splash T.M T.V x):= covert ..
-- scope helpers
section Lin
open Finsupp
private lemma purse {M:Type*}[AddCommMonoid M][Module ℂ M](G:A→M)(L:A→₀ℂ) : linearCombination ℂ G L=∑ i,L i • G i := by
    rw [linearCombination_apply,Finsupp.sum]; apply sum_subset (subset_univ _); intro a _ h; rw [Finsupp.notMem_support_iff.mp h,zero_smul]
lemma spi (P:Matrix A B ℂ)(i j):spool P i j=P i j:= congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply _) j
lemma spools (P : Matrix A B ℂ)(R:Matrix B C ℂ) (i:A): Finsupp.linearCombination ℂ (spool R) (spool P i)=spool (P*R) i:=by
    ext1 j; rw [purse,Finset.sum_apply']; simp only [Finsupp.smul_apply, spi,smul_eq_mul,Matrix.mul_apply]
lemma scalM (P: Matrix A B ℂ)(Q:Symmetric B): Matrix.of (scope (spool P) Q).cov=P*Matrix.of Q.cov*P.transpose:=by
    ext i j; change treats Q (spool P i) (spool P j)=_; rw [Matrix.mul_apply]; unfold treats; rw [purse,purse]; refine Finset.sum_congr rfl (fun a _=>?_); rw [Finset.sum_apply]; simp only [Pi.smul_apply,spi, Matrix.mul_apply,Matrix.of_apply,Matrix.transpose_apply,smul_eq_mul]; rw [mul_comm]
lemma camped (P R: Symmetric A): Matrix.of (P+R).cov= Matrix.of P.cov+Matrix.of R.cov:=by ext; rfl
end Lin
lemma spoke (p: Papers A (Patio X)) : (T.after S).read p=S.read (T.read p):=by
    rw [as_sum p] -- from Bera
    simp only [_root_.map_sum]; apply sum_congr rfl; intro i _
    let y:=coeff i p; rw [show (monomial i) (coeff i p)= _ from (show (monomial i) y=outer (monomial i 1) y by rw [outmono,one_smul])]
    rw [spree, spree, spree]; unfold after; dsimp only; rw [piped, stitches]; simp_rw [spools]
lemma noneW : T.read 1=1:= alights ..
section
-- do not set DecidableEq extra
noncomputable def monoT (A X: Type)[Fintype A][Fintype X] : Tone A X A X:=⟨1,0,1,0⟩
lemma monoid (p:Papers A (Patio X)): (monoT A X).read p=p:=by
   have hp (p:poly A) : Normal.pipe (spool (1:Matrix A A ℂ)) 0 p=p:=by
      unfold Normal.pipe; rw [LinearMap.comp_apply,froze]; apply DFunLike.congr_fun (f:=exchange (spool (1:Matrix A A ℂ))) (g:=AlgHom.id ..); ext i; rw [wool]; simp [Matrix.one_apply]
   have ht (x: Patio X): splash (1:Matrix X X ℂ) 0 x=x:=by
      apply Subtype.ext; change changeVars (1:Matrix X X ℂ) (birth (Wand 0) x.val)=x.val; have hz:Wand (0:Matrix X X ℂ)=0:=by unfold Wand; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; ext x; change (0:ℂ) • ((QCD.Creek.v j*QCD.Creek.v i) x)=0; rw [zero_smul]
      rw [hz]; simp [birth]
   rw [as_sum p,map_sum]; apply sum_congr rfl; intro i _
   let y:=coeff i p; rw [show (monomial i) (coeff i p)=_ from (show (monomial i) y=outer (monomial i 1) y by rw [outmono,one_smul]),spree]; unfold monoT; dsimp only; rw [hp,ht]
end
end Tone
end YM.Vest
#print axioms YM.Vest.Tone.spoke
#print axioms YM.Vest.Tone.scalM
#print axioms YM.Vest.Tone.monoid
