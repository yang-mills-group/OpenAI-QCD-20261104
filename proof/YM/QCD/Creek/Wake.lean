import YM.QCD.Grass.Schur
import YM.QCD.Grass.Wick

/-! # Auxiliary Grass Laplace transforms on mixed alphabets
Exact commutative even derivation spans. No distribution extension taken.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Function Finset Grass NormedSpace
open scoped Topology BigOperators ContDiff Classical
variable {I : Type*}{A B M: Type*} [Fintype A][Fintype B][Fintype M]
-- use CLM Ends
abbrev EndA (A : Type*)[Fintype A] := Alg A →L[ℂ] Alg A
def v (i:A): EndA A:= (vary i).toContinuousLinearMap
def l (i:A): EndA A:= (LinearMap.mulLeft ℂ (atom i)).toContinuousLinearMap
lemma circulate (i j:A) : v i * v j= -(v j * v i):= ContinuousLinearMap.ext fun x=> CliffordAlgebra.contractLeft_comm _ _ x
lemma follow (i j:A) : l i * l j = -(l j*l i):=by ext1 x; change atom i*(atom j*x)=-(atom j*(atom i*x)); rw [← mul_assoc,← mul_assoc,show atom i*atom j=_ from line_line ..,neg_mul]; rfl
lemma bid (i j:A): v i*l j+l j*v i= if i=j then (1:EndA A) else 0:=by
  ext1 x; split
  next h => subst j; change vary i (atom i*x)+atom i*vary i x=x; rw [vary_head]; simp [probe]
  next h => change vary i (atom j*x)+atom j*vary i x=0; rw [vary_head]; simp [probe,h,Ne.symm h]

lemma negst (D E:EndA A): (-D)*E=-(D*E):= neg_mul D E
lemma negstu (D E:EndA A): D*(-E)=-(D*E):=mul_neg D E
lemma spins (D E: EndA A) (x:ℂ): (x • D)*E=x • (D*E):= ContinuousLinearMap.ext fun _=> rfl
lemma spinner (D E: EndA A) (x:ℂ): D*(x • E)=x • (D*E):= ContinuousLinearMap.ext fun u=> D.map_smul x (E u)
lemma spun (D E:EndA A)(x:ℕ) : D*(x • E)=x • (D*E):=ContinuousLinearMap.ext fun u=> map_nsmul D x (E u)
lemma rotates (D E F:EndA A)(h:D*E=-(E*D))(g:D*F=-(F*D)): Commute D (E*F):=by unfold Commute SemiconjBy; rw [← mul_assoc,h,negst,mul_assoc,g,negstu,neg_neg,mul_assoc]
lemma swapsV (i j k:A) : Commute (v i) (v j * v k):=rotates _ _ _ (circulate ..) (circulate ..)
lemma paid_v (i j k:A)(hi:k ≠ i): Commute (v k) (l i*v j) := rotates _ _ _ (eq_neg_of_add_eq_zero_left (by rw [bid,if_neg hi])) (circulate ..)
lemma swirl (i j k:A)(hi:j≠k): Commute (l k) (l i*v j):=rotates _ _ _ (follow ..) (eq_neg_of_add_eq_zero_left (by rw [add_comm,bid,if_neg hi]))
lemma whittle (i j k:A) (z:EndA A):(v i*v j)*l k-l k*(v i*v j)=(if j=k then v i else 0)-(if i=k then v j else 0):=by
  have h:=bid i k; have he:=bid j k
  split_ifs at * <;> calc
    _ = v i*(v j*l k + l k*v j) -(v i*l k+l k*v i)*v j:= by noncomm_ring
    _ = _ :=by rw [h,he]; simp -- if signs

lemma thin (i j k:A)(h:k ≠ i) (f:k ≠ j): v k*l i * l j=l i*l j*v k:=by rw [mul_assoc]; exact (rotates _ _ _ (eq_neg_of_add_eq_zero_left (by rw [bid,if_neg h])) (eq_neg_of_add_eq_zero_left (by rw [bid,if_neg f])))
lemma liftWing (i j k:A): (l i*v j)*l k-l k*(l i*v j)=if j=k then l i else 0:=by
  have H : (l k*l i)=-(l i*l k):=follow ..
  rw [← mul_assoc (l k),H]; rw [show (l i*v j)*l k-_= l i*(v j*l k+l k*v j) by rw [negst]; noncomm_ring,bid]; split <;> simp

-- cost exponent identities in arbitrary algebra. ℚ instance
local instance {A:Type*}[Fintype A] : NormedAlgebra ℚ (EndA A) := .restrictScalars ℚ ℂ _
-- conflicts exponential? Exp actually uses NormedAlgebra ℚ installed local; notation after exporting def. tests
noncomputable def birth (D:EndA A) := exp D
lemma swerve (D R V:EndA A)(h:D*R-R*D=V)(hp:Commute V D): birth D * R = (R+V)*birth D :=by
  have hx (k:ℕ): D^k * R = R*D^k + k • (V*D^(k-1)):=by
    induction k with
    | zero=> simp
    | succ k ih=>
      rw [pow_succ' D k,mul_assoc,ih,mul_add,← mul_assoc,show D*R=V+R*D from sub_eq_iff_eq_add.mp h,add_mul]
      cases k with
      | zero=> simp [add_comm]
      | succ k=> rw [spun,← mul_assoc D V,hp.symm.eq, mul_assoc V D,_root_.add_smul,one_smul, Nat.add_sub_cancel,Nat.add_sub_cancel,← pow_succ' D k]; simp only [mul_assoc,add_comm,add_left_comm]; simp only [add_smul,one_smul]; ac_rfl
  let f (n:ℕ):=(n.factorial:ℂ)⁻¹ • D^n; let g (n:ℕ):=(n.factorial:ℂ)⁻¹ • n • (V*D^(n-1)); have hh:HasSum f (birth D) := exp_series_hasSum_exp' D
  have he n:f n * R - R*f n=g n:=by unfold f g; rw [spins,spinner,hx,smul_add]; abel
  have hw n:g (n+1)= V*f n:=by unfold f g; rw [spinner,Nat.add_sub_cancel,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]; congr 1; rw [Nat.factorial_succ,Nat.cast_mul]; field_simp
  have hg: HasSum g (birth D * R - R*birth D):= (HasSum.congr_fun ((hh.mul_right R).sub (hh.mul_left _)) (fun i=>(he i).symm))
  have hn : HasSum g (V*birth D):=by
    rw [← hasSum_nat_add_iff' (k:=1)] -- syntax
    simp_rw [hw]; simp only [sum_range_one,g,zero_smul,zero_nsmul, smul_zero, sub_zero]; exact hh.mul_left V
  exact (sub_eq_iff_eq_add.mp (hg.unique hn)).trans (by rw [add_mul, add_comm])
lemma powers (D:EndA A)(x:Alg A)(h:D x=0) : birth D x=x:=by
  let t (n:ℕ):=(n.factorial:ℂ)⁻¹ • D^n; have hm:HasSum t (birth D):=exp_series_hasSum_exp' D
  have hs:= (ContinuousLinearMap.apply ℂ (Alg A) x).hasSum hm -- check
  change HasSum (fun n=> t n x) (birth D x) at hs
  rw [← hs.tsum_eq,tsum_eq_single 0]
  · simp [t]
  intro i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hi; unfold t; rw [pow_succ]; change ((↑(j+1).factorial:ℂ)⁻¹) • (((D^j):EndA A) (D x)) = 0; rw [h,map_zero,smul_zero]
end YM.QCD.Creek
