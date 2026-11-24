import YM.QCD.Rudder.Grove
import YM.Gauge.Chart

/-!
# Complex Cartan waves along one arbitrary real color.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat NormedSpace Wilson Function Finset Lattice Metric
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology InnerProductSpace ContDiff
attribute [local instance] Gauge.frobInner
-- do generally for easier proof
variable {G : Gauge}
def metricC (G : Gauge) (i : G.ColorIndex): G.Mat →ₗ[ℂ] ℂ where
 toFun X := -( (X * G.colorMat (EuclideanSpace.basisFun G.ColorIndex ℝ i)).trace)/(G.repDim:ℂ)
 map_add' X Y:=by simp [add_mul]; ring
 map_smul' p X:=by simp [Matrix.smul_mul,Matrix.trace_smul]; ring
lemma trace_r (X Y : G.Mat) (h:star X= -X) (ht : star Y= -Y): (X*Y).trace.im=0:=by
  have he : star (X*Y).trace=(X*Y).trace:=by rw [← Matrix.trace_conjTranspose,← Matrix.star_eq_conjTranspose,star_mul,h,ht,neg_mul_neg]; exact Matrix.trace_mul_comm _ _
  exact Complex.conj_eq_iff_im.mp he
lemma league (G : Gauge) (i : G.ColorIndex) (X : G.Mat) (h:star X= -X): metricC G i X= ((G.projectColor X i:ℝ):ℂ):=by
  let c:= G.projectColor X; let V := EuclideanSpace.basisFun G.ColorIndex ℝ i; let T:= G.colorMat V
  have he : inner ℝ X T=inner ℝ (G.colorMat c) T:=by
    have hh: inner ℝ (X-G.lie.starProjection X) T=0:= Submodule.starProjection_inner_eq_zero _ _ (G.colorMat_mem _)
    exact sub_eq_zero.mp (by simpa only [inner_sub_left, c,G.colorMat_project] using hh) -- simp RHS
  have hi : inner ℝ (G.colorMat c) T=(G.repDim:ℝ) * c i:= (G.inner_frob_color c V).trans (by rw [real_inner_comm,EuclideanSpace.basisFun_inner])
  have ht : star T= -T:= G.colorMat_skew _
  change (X*star T).trace.re=(G.colorMat c*star T).trace.re at he; rw [ht, mul_neg,mul_neg,Matrix.trace_neg, Matrix.trace_neg,Complex.neg_re,Complex.neg_re] at he
  have hr : (X*T).trace.re= - (G.repDim:ℝ)* c i:=by
    change (G.colorMat c*star T).trace.re=_ at hi; rw [ht,mul_neg,Matrix.trace_neg,Complex.neg_re] at hi; linarith
  change -(X*T).trace/(G.repDim:ℂ)=(↑(c i):ℂ)
  rw [div_eq_iff (show (G.repDim:ℂ)≠0 by exact_mod_cast G.dimPos.ne')]; apply Complex.ext
  · simp [hr]; ring
  simp [trace_r X T h ht]

variable (C : su.Color)
def echo : Mat:= su.colorMat C
def bird (x : ℝ): su.El:=su.lieExp (x • C)
def lunar (z : ℂ): Mat:= exp (z • echo C)
lemma markC (x:ℝ): lunar C x=colour (bird C x):=by
  change _=su.mat (su.lieExp _); rw [Gauge.mat_lieExp,map_smul]; exact congr_arg (NormedSpace.exp (𝔸:=Mat)) (by ext i j; change (x:ℂ) • (echo C i j) = x • (echo C i j); simp)
lemma bright (x y : ℝ): bird C x*bird C y= bird C (x+y):=by
  change su.lieExp _*su.lieExp _=_; apply su.mat_injective; rw [Gauge.mat_mul]
  change colour (bird C x)*colour (bird C y)=colour (bird C (x+y)); simp_rw [← markC]; unfold lunar
  haveI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℂ _
  rw [Complex.ofReal_add,add_smul]; exact (exp_add_of_commute (show Commute ((x:ℂ) • echo C) ((y:ℂ) • echo C) from ((Commute.refl _).smul_left _).smul_right _)).symm
lemma bird_inv (x : ℝ): (bird C x)⁻¹=bird C (-x):=by
  apply inv_eq_of_mul_eq_one_right; rw [bright]; simp [bird]
lemma lunar_nil : lunar C 0=1:= by simp [lunar]
lemma shine (z:ℂ): HasDerivAt (lunar C) (lunar C z * echo C) z:= hasDerivAt_exp_smul_const ..

def stringC (i : su.ColorIndex) (X : Mat): ℂ := metricC su i X
lemma chartC (X:su.Mat) (i:su.ColorIndex): metricC su i X=stringC i X:=rfl

/-- analytic continuation of plaquette curvature along Cartan line -/
def bore (i : su.ColorIndex)(z:ℂ):= stringC i ((1/2:ℂ) • (lunar C z-lunar C (-z)))
lemma core_r (i : su.ColorIndex)(x:ℝ): bore C i x= ((su.curvature (bird C x) i:ℝ):ℂ):=by
  unfold bore; rw [markC, ← Complex.ofReal_neg, markC, ← bird_inv]
  let V:=bird C x; let H : su.Mat:= (1/2:ℝ) • (su.mat V-su.mat V⁻¹)
  have he: H=(show Mat from (1/2:ℂ) • (colour V-colour V⁻¹)):=by -- cast
    apply Matrix.ext; intro i j; change (1/2:ℝ) • (_:ℂ)=(1/2:ℂ) • (_:ℂ); simp [V,colour,Matrix.sub_apply]; rfl
  refine Eq.trans (show _ = metricC su i H from ?_) (league su i H ?_)
  · rw [he, chartC]
  unfold H; rw [star_smul,Gauge.mat_inv,star_sub,star_star]; simp only [star_trivial,smul_sub]; abel
end YM.QCD.Rudder
