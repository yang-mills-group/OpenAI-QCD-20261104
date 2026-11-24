import YM.QCD.Creek.Scoop
/-! # Replacement generator exponent kills/wipes and locality of vacuum Laplacian. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Creek
open Function Finset Grass NormedSpace
open scoped Topology BigOperators ContDiff Matrix
variable {A B M:Type*} [Fintype A][Fintype B] [Fintype M]
variable {f:A ↪ M}{g:B ↪ M}(h : ∀ i j,f i ≠ g j)
variable (S T:Matrix (A) (B) ℂ)
def barkG (f:A↪M)(g:B↪M) (F : Matrix (A) (B) ℂ): EndA M:= ∑ i,∑ j,F i j • (l (g j) * v (f i))
include h
lemma barkCom : Commute (barkG f g S) (barkG f g T):= by
  refine finiteComm _ _ fun i _=> finiteComm _ _ fun j _=> timesComm ?_ _
  refine Commute.mul_right ?_ ?_
  · exact (finiteComm _ _ fun u _=> finiteComm _ _ fun p _=>timesComm (swirl _ _ _ (h _ _)) _).symm
  exact (finiteComm _ _ fun u _=> finiteComm _ _ fun p _=> timesComm (paid_v _ _ _ (h _ _)) _).symm
omit h in
lemma barkSum : barkG f g (T+S)=barkG f g T+barkG f g S:=by unfold barkG; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; exact add_smul (T i j) (S i j) (l (g j) * v (f i))

def wingG (g:B↪M) (i: A):EndA M:=∑ j,S i j • l (g j)
lemma wagesWing (i:A): Commute (barkG f g S) (wingG S g i):= finiteComm _ _ fun j _=>timesComm ((finiteComm _ _ fun u _=> finiteComm _ _ fun p _=> timesComm (swirl _ _ _ (h _ _)) _).symm) _
lemma whistles (i:A): birth (barkG f g S)*l (f i)=(l (f i)+wingG S g i)*birth (barkG f g S):=by
  classical
  apply swerve _ _ _ _ ((wagesWing h S i).symm); unfold barkG; rw [sum_mul,mul_sum,← sum_sub_distrib, sum_eq_single i]
  · rw [sum_mul,mul_sum,← sum_sub_distrib,wingG]; refine sum_congr rfl fun j _=>?_ ; rw [spins,spinner]; erw [← smul_sub]; rw [liftWing,if_pos rfl]
  · intro j _ h; rw [sum_mul,mul_sum,← sum_sub_distrib]; apply sum_eq_zero; intro k _; rw [spins,spinner]; erw [← smul_sub]; erw [liftWing,if_neg ((f).injective.ne h),smul_zero]
  simp
lemma skirt (i: B): Commute (l (g i)) (birth (barkG f g S)):=roundP (finiteComm _ _ fun j _=> finiteComm _ _ fun p _=> timesComm (swirl _ _ _ (h _ _)) _)
omit h in
lemma ticks : birth (barkG f g S) (1:Alg M)=1:= powers _ _ (by simp only [barkG,ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]; simp [v,vary_one])
lemma whistles_at (i:A)(x:Alg M): birth (barkG f g S) (atom (f i)*x)= (atom (f i)+(∑ j,S i j • atom (g j)))*birth (barkG f g S) x:=by
  let B':=birth (barkG f g S); rw [show B' (atom (f i)*x)= (B'*l (f i)) x from rfl]; rw [show B'*l (f i)=_ from whistles h S i,add_mul]
  change l _ (B' x) + wingG S g i (B' x)=_; rw [add_mul,sum_mul,wingG,ContinuousLinearMap.sum_apply]; exact congr_arg (l (f i) (B' x)+ ·) (sum_congr rfl (fun j _=> (show _ = _*B' x from (smul_mul_assoc (S i j) (atom (g j)) (B' x)).symm)))


end YM.QCD.Creek
