import YM.Lobo.Walt
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
open scoped YM.Massive.Poised.Plans.Stamp
variable (k i j: Tri)(x y: Axis)
-- real deriv.Hoist
noncomputable abbrev waveT (k i j:Tri):ℂ:= ((Omega k).val (lieu j) (lieu i):ℂ)
lemma discder : HasDerivAt (fun t:ℝ=>disk k t j i) (waveT k i j) 0:=by
      let F:= pathW k; have h:=treks k; have hv:HasDerivAt (fun t:ℝ=> (F t).coord.val (lieu j) (lieu i)) ((Omega k).val (lieu j) (lieu i)) 0:= cSpan (Omega k) F h (lieu j) (lieu i); simp_rw [show ∀ t:ℝ,(F t).coord= Thr k t from h.2.2] at hv; exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ hv
noncomputable def charI(k j:Tri) : ℝ:=if j=backK k then -1 else 1
noncomputable def roof(k j:Tri):Tri:= Equiv.swap (backK k) (edgeK k) j
noncomputable abbrev barge(k:Tri):= SpinQ k
lemma coar : ((Cup k).perm) (lieu i)=lieu (roof k i):=by fin_cases k<;>fin_cases i<;>decide
lemma viaC: signT (Cup k) (lieu i)=charI k i:=by unfold signT Cup Maxwell.Free.Corners.quarter charI; simp only [decide_eq_true_eq]; congr 1; exact propext Fin.castSucc_inj
lemma coreTime :(Cup k).perm timeAxis=timeAxis∧signT (Cup k) timeAxis=1:=by fin_cases k <;> constructor <;>rfl
noncomputable abbrev quarterR:=Real.pi/2
lemma sBeta : disk k quarterR j i= if roof k i=j then (charI k i:ℂ) else 0:=by
     have hx:(Thr k quarterR)=(Cup k).ortho:= Eq.trans ((treks k).2.2 quarterR).symm (fL k); unfold disk; rw[hx,Signed.ortho]; simp only [Signed.matrix_at]; rw [coar]; have hs:=viaC k i; by_cases h:roof k i=j; · subst j; rw[if_pos rfl,if_pos rfl]; exact congr_arg Complex.ofReal hs
     rw [if_neg (fun e=>h (Fin.castSucc_inj.1 e)),if_neg h,Complex.ofReal_zero]
variable {W:Type}[AddCommGroup W][Module ℂ W]
lemma wing_Q(f:Tri→W): wing k quarterR f i=(charI k i:ℂ) • f (roof k i):=by unfold wing; simp_rw [sBeta]; simp [ite_smul]
lemma carry_one : Ortho.oneParameter (Omega k) 0=(1: Ortho):=by -- lemma
        simp [Ortho.oneParameter] -- try
lemma d_zero : disk k 0 j i= if j=i then 1 else 0:=by unfold disk Thr; rw [carry_one]; change (↑((1:M4) (lieu j) (lieu i)):ℂ)=_; simp only [Matrix.one_apply,lieu,Fin.castSucc_inj]; split <;> norm_num
lemma w_zero(v:Tri→W): wing k 0 v i=v i:=by unfold wing; simp_rw [d_zero]; simp[ite_smul]
-- discrete derivative operator of triples
noncomputable def drive(k:Tri)(v:Tri→W)(i:Tri):W:=∑ j:Tri, waveT k i j • v j
lemma signsU : waveT k i j = if i =edgeK k ∧ j=backK k then 1 else if i=backK k∧ j=edgeK k then -1 else 0:=by fin_cases i<;> fin_cases k<;>fin_cases j <;> simp +decide [waveT,Omega,Ortho.plane,Matrix.single_apply]
lemma eOG : waveT k i j= -(waveT i k j):=by rw[signsU,signsU]; fin_cases k<;>fin_cases i<;>fin_cases j<;>simp +decide
lemma gammaE(p:Tri→W):drive k p k=0:=by unfold drive; simp only [signsU,if_neg (mt And.left (disjointI k).1),if_neg (mt And.left (disjointI k).2.1),zero_smul, sum_const_zero]
lemma gammaY(p:Tri→W):drive k p (edgeK k)=p (backK k):=by unfold drive; simp only[signsU,true_and, if_neg (mt And.left (disjointI k).2.2)]; simp [ite_smul]
lemma gammaZ(p:Tri→W):drive k p (backK k)= -p (edgeK k):=by unfold drive; simp only[signsU,if_neg (mt And.left (disjointI k).2.2.symm),true_and]; simp [ite_smul]
-- Labels.Real proper
variable {d:ℕ}
noncomputable scoped instance (d:ℕ):NormedSpace ℝ (Label d):=NormedSpace.restrictScalars ℝ ℂ _ -- instead local in file.Mana. field instance scopes globally Lobo leaks.Keep scoped
private lemma seed (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousSMul ℝ V:=inferInstance
noncomputable scoped instance (d:ℕ) : ContinuousSMul ℝ (Label d):= by exact seed (Label d)
variable (p:Tri→ℝ→Label d)(f:Tri→ Label d)(V:Tri→Label d)(hv:∀ i,p i 0=f i)(h:∀ i,HasDerivAt (p i) (V i) 0)
include h hv
lemma swellP : HasDerivAt (fun t:ℝ=>wing k t (fun i=>p i t) i) (drive k f i+V i) 0:=by
     have ht : HasDerivAt (fun t:ℝ=>wing k t (fun i=>p i t) i) (∑ j:Tri,(waveT k i j • p j 0+disk k 0 j i • V j)) 0:=HasDerivAt.fun_sum (fun j _=> HasDerivAt.congr_deriv ((discder k i j).smul (h j)) (add_comm ..)) -- derivative order
     simp_rw [hv,sum_add_distrib,d_zero] at ht; simp only [ite_smul,sum_ite_eq',zero_smul,one_smul, mem_univ,↓reduceIte] at ht; exact ht
omit h hv
lemma wingD(p:Tri→Label d): HasDerivAt (fun t:ℝ=>wing k t p i) (drive k p i) 0:= by simpa only [Pi.zero_apply,add_zero] using swellP k i (fun i _=>p i) p 0 (fun _=>rfl) (fun i=>hasDerivAt_const 0 (p i))
end YM.Lobo
#print axioms YM.Lobo.eOG
#print axioms YM.Lobo.wing_Q
#print axioms YM.Lobo.wingD
