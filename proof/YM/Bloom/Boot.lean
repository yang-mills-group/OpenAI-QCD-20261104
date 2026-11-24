import YM.Bloom.Inky
/-! # self Wick initialization.T one glyph per marker polar link. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Inky
open QCD QCD.Lat Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Precision Exterior Bloch Laurent
open QCD.Creek QCD.Cove QCD.Flume QCD.Free YM.Next.Free
open YM.Arise YM.Arise.Count YM.Bloom YM.Bloom.TreeP YM.Bloom.Jar
open Ribbon Cape Play Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit
open Rebus Matrix Vest TimesV Arise.Bill Arise.Range
open QCD.Bloom QCD.Bloom.Buzz YM.Next.Rank.Normal Massive.UV
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L B₀ t' D q:ℕ} {Q R:Tone (Kh f) (Dh f 6 I) (Kh c) (Dh c 6 I)}
variable {a b v y' ε s C μ θ ξ ν z X₁ X₂:ℝ}
variable (Dg:Eyes su D L (2*n) j a v b ε s C)
-- moment.N. Atlas
noncomputable def beamG (d:I→ℕ)(x:I→ Cover)(w:ℝ)(f:Side): Matrix (Svg d) (Kh f) ℂ:=Matrix.of fun i z=> pots w f i.2 (x i.1) () z
noncomputable def beamL (d:I→ℕ)(x:I→ Cover)(w:ℝ)(f:Side): Matrix (Arms d) (Keys f 6) ℂ:=Matrix.of fun i z=> splice w f i.2 (x i.1) () z -- Arms ns
lemma twist_sym (P:Matrix A J ℂ)(R:Matrix J J ℂ)(h:R.IsSymm): (P* R*P.transpose).IsSymm :=by unfold Matrix.IsSymm at *; simp [Matrix.transpose_mul,h,Matrix.mul_assoc]
noncomputable def frostU (Q:A→ I)(M: Matrix A A ℂ)(h:M.IsSymm): YM.Next.Rank.Normal.Symmetric A where
    cov i j:= if Q i=Q j then - M i j else 0
    symm i j:=by by_cases ht:Q i=Q j; · rw [if_pos ht,if_pos ht.symm,h.apply]
                 rw [if_neg ht,if_neg (Ne.symm ht)]
noncomputable def oxide (Q:A→I)(M: Matrix A A ℂ): Matrix A A ℂ:= of fun i j=>if Q i=Q j then -M i j else 0
variable (p:I→ℕ)(x:I→ Cover)(w:ℝ)
local notation "Kx"=> Arms p
local notation "Z"=> Spine I
local notation "W"=> (Svg p)
local notation "Ug"=> beamG p x w f
local notation "Us"=> beamL p x w f
local notation "Tz"=> (Tv p)
noncomputable def shone (d:I→ℕ)(x:I→ Cover)(w:ℝ) (f:Side)(H: Bed)(F:Train j)(h:(chalkW f H).IsSymm): Tone (Svg d) (Tv d) (Kh f) (Dh f 6 I):= let K:=beamG d x w f; let P:= beamL d x w f
    ⟨K,frostU Sigma.fst (K*chalkW f H*K.transpose) (twist_sym K _ h),breezeP (Spine I) P,breezeX (Spine I) (oxide Sigma.fst (P* Buzz.start f F 6*P.transpose))⟩ -- lean layout let
-- Telescope high.M preservation ABI.
variable (H H':Bed)(F F':Train j)(hw:(chalkW f H).IsSymm) (g:Ratio c f)(ht:Canon k j H H' F F' R g)
local notation "Tπ"=> shone p x w f H F hw
local notation "Tg"=> Tone.after (shone p x w f H F hw) R
local notation "𝒦"=> (chalkW f H)
lemma beam_aG {t:Type}[Fintype t](K:Matrix (Kh f) t ℂ)(i:W)(j:t): (Ug*K) i j=(pots w f i.2 (x i.1)*K) () j:=by simp [Matrix.mul_apply,beamG]
lemma beam_aS {t:Type}[Fintype t](K:Matrix (Keys f 6) t ℂ)(i:Kx)(j:t): (Us*K) i j=(splice w f i.2 (x i.1)*K) () j:=by simp [Matrix.mul_apply,beamL]
lemma plankG (K:Matrix (Kh f) (Kh f) ℂ)(i j:W): (Ug*K*(Ug).transpose) i j=(pots w f i.2 (x i.1)*K*(pots w f j.2 (x j.1)).transpose) () ():=by simp [Matrix.mul_apply,beamG]
lemma plankS (K:Matrix (Keys f 6) (Keys f 6) ℂ)(i j:Kx): (Us*K*(Us).transpose) i j=(splice w f i.2 (x i.1)*K*(splice w f j.2 (x j.1)).transpose) () ():=by simp [Matrix.mul_apply,beamL]
lemma blockish [DecidableEq I] (P: Matrix A J ℂ)(Q:Matrix J J ℂ):breezeP I P*breezeX I Q*(breezeP I P).transpose=breezeX I (P*Q*P.transpose):=by unfold breezeP breezeX; rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]; simp
lemma blockaged [DecidableEq I](P Q:Matrix A A ℂ): breezeX I (P+Q) = breezeX I P+breezeX I Q :=by ext i j; cases i<;>cases j <;> first|rfl| exact (zero_add _).symm
lemma breezeP_comm [DecidableEq I](P:Matrix A J ℂ)(R: Matrix J K ℂ): breezeP I P*breezeP I R=breezeP I (P*R):=by unfold breezeP; rw [Matrix.fromBlocks_multiply]; simp
lemma sloganP(i j:W): (Tπ).Q.cov i j= if i.1=j.1 then -(Ug*chalkW f H*(Ug).transpose) i j else 0:=rfl
lemma sloganS(i j:Kx): (Tπ).V (.inl i) (.inl j)= if i.1=j.1 then -(Us*Buzz.start f F 6*(Us).transpose) i j else 0:=rfl
include ht
lemma refineG(i j:W): (Tg).Q.cov i j=(if i.1=j.1 then 0 else (Ug*chalkW f H*(Ug).transpose) i j)-(Ug*(R.P*chalkW c H'*R.P.transpose)*(Ug).transpose) i j:=by
     let L:= Ug; let X:= Matrix.of (Tπ).Q.cov; let P:= Matrix.of R.Q.cov
     have he:= ht.berg; let R':= R.P* chalkW c H'* R.P.transpose
     have hA: Matrix.of (Tg).Q.cov = Ug *P*(Ug).transpose + X:=by unfold Tone.after; dsimp only; rw [Tone.camped,Tone.scalM]; rfl
     rw [show (Tg).Q.cov i j=(Matrix.of (Tg).Q.cov) i j from rfl,hA,Matrix.add_apply]; unfold X; rw [of_apply,sloganP, he,Matrix.mul_add,Matrix.add_mul, Matrix.add_apply]; unfold P; split <;> abel
lemma refineS(M: Matrix (Keys f 6) (Keys c 6) ℂ)(hM:R.M=breezeP Z M) :
       let P:=Us; let Y:=P*Buzz.start f F 6*P.transpose; let X:=P*(M*Buzz.start c F' 6*M.transpose)*P.transpose; (Tg).V=breezeX Z (of fun i j:Kx=> (if i.1=j.1 then 0 else Y i j)- X i j):=by
    intro P Y X; let A:= Buzz.start f F 6; let B:= Buzz.start c F' 6; let V:= M*B*M.transpose
    have he:=ht.plain; rw [hM] at he; change breezeX Z A = R.V+breezeP Z M*breezeX Z B*(breezeP Z M).transpose at he; rw [blockish] at he; unfold Tone.after; dsimp only; rw [show R.V = breezeX Z A-breezeX Z V from by rw [he]; exact (add_sub_cancel_right ..).symm ] -- simplify
    unfold shone; dsimp only; simp only [Matrix.mul_sub,Matrix.sub_mul, blockish]; ext i j; cases i <;> cases j <;> try simp only [Matrix.add_apply, Matrix.sub_apply]
    next i j=> simp only [breezeX,Matrix.fromBlocks_apply₁₁,of_apply,oxide]; unfold X Y P A V B; split <;> abel
    all_goals simp [breezeX]
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.refineS
#print axioms YM.MassiveQCD.Inky.refineG
