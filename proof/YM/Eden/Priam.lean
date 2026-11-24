import YM.Eden.Port
import YM.Bloom.Omen
/-! # full compatibility in actual Estate. Loom over.A -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Inky
open QCD QCD.Lat Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Precision Exterior Bloch Laurent
open QCD.Creek QCD.Cove QCD.Flume QCD.Free YM.Next.Free
open YM.Arise YM.Arise.Count YM.Bloom YM.Bloom.TreeP YM.Bloom.Jar
open Ribbon Cape Play Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit
open Rebus Matrix Vest TimesV Arise.Bill Arise.Range Grass QCD.Eden YM.Eden
open QCD.Bloom QCD.Bloom.Buzz YM.Next.Rank.Normal Massive.UV Arise.Parcel
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L D:ℕ}{a b ε s C C' v:ℝ}
variable (W:ℝ) (x:I→ Cover) (p:I→ℕ)(q:I→Bool)(i:I)
local notation "Wi"=>p i
local notation "x₀"=>x i
abbrev linkG (p:I→ℕ)(i:I) (x:Zinc su (p i)): Svg p:=⟨i,x⟩
abbrev linkS (p:I→ℕ)(i:I)(x:Sings (p i)): Arms p:=⟨i,x⟩
noncomputable def shape (t:A→J): Matrix A J ℂ:= of fun i j=> if j=t i then 1 else 0
lemma yarnM (t:A→J)(u: MvPolynomial A ℂ): MvPolynomial.rename t u=exchange (spool (shape t)) u:=by
    apply AlgHom.congr_fun _ u; ext1 i; rw[MvPolynomial.rename_X,QCD.Bera.wool]; simp [shape, ite_smul]
lemma keeper (t:A→J) (x:Alg A): changeVars (shape t) x=embed t x:=by
    apply AlgHom.congr_fun _ x; exact ext_atoms fun i=>by rw[change_atom,embed_atom]; simp [shape,ite_smul]
lemma leg_a (t:A→J)(M:Matrix J K ℂ)(i:A)(j:K): (shape t*M) i j=M (t i) j:=by simp [Matrix.mul_apply,shape,ite_mul]
lemma leg_v (t:A→J)(M:Matrix J J ℂ)(i j:A): (shape t*M*(shape t).transpose) i j=M (t i) (t j):=by rw [Matrix.mul_apply]; simp_rw [leg_a]; simp [shape,mul_ite]
lemma turnV (P:Matrix A J ℂ)(Q:Matrix J K ℂ)(x:MvPolynomial A ℂ): exchange (spool Q) (exchange (spool P) x)=exchange (spool (P*Q)) x:=by
    apply AlgHom.congr_fun (φ₁:= (exchange (spool Q)).comp (exchange (spool P))) _ x; ext1 i; rw [AlgHom.comp_apply,wool,map_sum,wool]; simp_rw [map_smul, wool, smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp only [smul_smul]; rw[← Finset.sum_smul]; rfl
variable (H: Bed)(F: Train j) (ht:(chalkW f H).IsSymm) (hQ:(YM.Eden.milky 0 H f (G:=su) (d':=p i)).IsSymm)
local notation "Tπ" => shone p x W f H F ht
local notation "δ"=> shape (linkG p i)
local notation "γ"=> shape (linkS p i)
local notation "Z"=> Tv p
local notation "Yp"=> beamG p x W f
local notation "Yq"=> beamL p x W f
local notation "Kₚ"=> payD Wi W
local notation "J₀"=>chartD (n:=f) x₀ Wi
local notation "E"=>gateP Wi W
local notation "Vg"=>mood Wi x₀ (1:Grid f)
lemma lottG : δ * Yp= Kₚ * J₀:=by
    ext v j; rw [leg_a]; erw [diagonal_mul (fun v=> (favorU W v:ℂ))]; rfl
lemma lottS : γ * Yq= E*Vg:=by
    ext v j; rw [leg_a,gateP,Matrix.diagonal_mul]; change splice W f v x₀ () j= _; unfold Buzz.splice; rw [Matrix.smul_apply,pinned_zero]; simp only [smul_eq_mul]; congr 1; unfold spig; rw [order_p,Arise.spine_cost,Complex.ofReal_pow]; rfl
local notation "Q₀"=> wager 0 H f hQ
variable {r:Clip} (hh:Floor H r f a b)(ha:0<a)
include hh ha
lemma strataG: scope (spool δ) (Tπ).Q = scope (spool Kₚ) Q₀:=by
    apply Next.Rank.Normal.Symmetric.ext; change Matrix.of (scope (spool δ) (Tπ).Q).cov = Matrix.of (scope (spool Kₚ) Q₀).cov; rw [Tone.scalM,Tone.scalM];
    let X:= YM.Eden.milky x₀ H f (G:=su) (d':=p i); have hp : Matrix.of (Q₀).cov = - X:=by unfold X; rw [silky hh ha x₀]; rfl
    let M:= chalkW f H; have hx:X= J₀*M*(J₀).transpose:=by
        -- Instance issue
        exact (chores x₀).symm
    rw [hp,hx]; ext j l; rw [leg_v,Matrix.of_apply, sloganP, if_pos (show _=_ from rfl)]; let L:=Yp*M*(Yp).transpose; have he:L (linkG p i j) (linkG p i l) = (δ * L * (δ).transpose) j l:=(leg_v ..).symm; change -L (linkG p i j) (linkG p i l)=_; rw [he]; unfold L; rw [← Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc _ ((Yp).transpose),← Matrix.transpose_mul,lottG]; unfold M; rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rfl
lemma gloria (P:Lily su Wi): Next.Rank.Normal.pipe (spool (Yp)) (Tπ).Q (nameG p i P)= exchange (spool (J₀)) (Next.Rank.Normal.milk Q₀ (stemsP su Wi W P)):=by
    change _=exchange _ ((Next.Rank.Normal.milk Q₀) _); rw [boughtS, Next.Rank.Normal.prepared,turnV,pipes, show nameG p i P=exchange (spool δ) P from yarnM .., Next.Rank.Normal.prepared,turnV, lottG, strataG W x p i H F ht hQ hh ha]
omit hh ha
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.gloria
#print axioms YM.MassiveQCD.Inky.lottS
