import YM.QCD.Pearl.Pose
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # finite, exact discrete subtraction on the charged line. Euler branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n:Side}{I J D:Type}{p:Site n}{z:Momentum}{j : ℕ}{G:I→Gleam}{U:J→Bloom 1}{V:D→Bloom 2}{P:Plan j}{v:Train j}{η a b c:ℝ}(C : su.Color)
abbrev Cher (n:Side):=Site n→ℂ

def gradient (A:Cher n):Weather n:=fun i=> A i.1-A (i.1+step i.2)
def fond (A:Cher n):Sheet n:= rides (Equiv.refl _) fun x=> TouchL (lunar C (A x))
lemma exit (A:Cher n)(w:Walk)(x): bill (gradient A) x w=A x-A (stop x w):=by
  induction w generalizing x with
  | nil=> simp[bill,stop]
  | cons i w ih=> rw [bill,ih, stop]; unfold gradient Step.used Step.vec; split
                  · simp [sub_eq_add_neg]
                  abel
lemma blink' (A:Cher n):fond C A*fond C (-A)=1:=by
  unfold fond; rw [ride_mul]; simp only [Equiv.refl_apply]
  simp_rw [show ∀ x:Site n, TouchL (lunar C (A x))*TouchL (lunar C ((-A) x))=1 from fun x=>
    (touch_mul ..).trans (by rw [spend]; simp only [Pi.neg_apply,add_neg_cancel,lunar_nil,touch_one])]; exact ridden
lemma belang (A:Cher n) (w:Walk) : amass C 0 w (gradient A)=fond C A*routeM 0 1 w* fond C (-A):=by
  have he (i:Step):amass C 0 [i] (gradient A)=fond C A*routeM 0 1 [i]*fond C (-A):=by
    unfold amass fond; rw [show routeM _ _ _=leg (0:Site n) 1 i from by simp[routeM],leg_day,ride_mul,ride_mul,ride_mul]; congr 1
    funext x; simp only [exit,stop]
    simp only [Equiv.refl_apply,hitch,Equiv.trans_apply, Equiv.coe_addRight,Pi.neg_apply, show ∀ M:Mat,TouchL M=touch M from fun M=>rfl]
    change touch (lunar C (A x - A (x+i.vec))) * touch (glint 0 x i • colour (i.read (1:Grid n) x))=touch (lunar C (A x))*touch (glint 0 x i • colour (i.read (1:Grid n) x))*touch (lunar C (-(A (x+i.vec))))
    rw [touch_mul,touch_mul,touch_mul]
    have hh: colour (i.read (1:Grid n) x)=1 := by cases hv:i.neg <;> simp only [Step.read, hv,Pi.one_apply,Bool.false_eq_true,↓reduceIte,inv_one] <;> rfl
    rw [hh]; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,spend, sub_eq_add_neg]
  induction w with
  | nil=> unfold amass; simp only [bill,lunar_nil,routeM,List.map_nil,List.prod_nil,mul_one,blink']; change rides _ (fun _=>touch 1)=_; simp only [touch_one]; exact ridden
  | cons i w ih=>
    rw [am_append,he,ih,show routeM (0:Site n) 1 (i::w)=routeM (0:Site n) 1 [i]*routeM (0:Site n) 1 w from appendM _ _ [i] w];
    simp only [mul_assoc]; rw [← mul_assoc (fond C (-A)), mul_eq_one_comm.mp (blink' C A),one_mul] -- check
lemma soloGrad (A:Cher n)(G:Gleam): silo C 0 G (gradient A)=fond C A*silo C 0 G 0*fond C (-A):= by
  unfold silo; rw [belang, amass0]; rw [mul_assoc _ (fond C (-A)), ← mul_assoc (fond C A),mul_assoc (fond C A*routeM _ _ _)]; congr 1; exact (commutes_ride G.B _ _).eq
lemma siltGrad {m:ℕ}(A:Cher n)(G:Bloom m)(hp:0<m):silt C 0 G (gradient A)=0:=by
  have he (x:Site n): blossom C G (gradient A) x=0:=by unfold blossom; refine sum_eq_zero fun i _=> ?_; simp only [tick,exit,square_stop,sub_self,bore_nil]; rw [prod_eq_zero (Finset.mem_univ (⟨0,hp⟩:Fin m)) rfl,zero_smul]
  unfold silt; rw [funext he,ride_zero,zero_mul]
lemma warmth (h:Package η a b c P v G U V)(A:Cher n): actual (extent C G U V n) (gradient A)=0:=by
  let M:=extent C G U V n
  have hp : Summable fun i:I=> silo C 0 (G i) (0:Weather n):=by
    have hh (i:I):silo C 0 (G i) (0:Weather n)=(G i).dept 0 1:=by rw [silo,amass0]; rfl
    simp_rw [hh]; exact (h.matchA ..).summable
  have he : M (gradient A)=fond C A*M 0 *fond C (-A):=by unfold M extent; simp_rw [reachouts, fun i=> siltGrad C A (U i) (by decide), fun i=>siltGrad C A (V i) (by decide),low_silt C _ _ (show 0<1 by decide), low_silt C _ _ (show 0<2 by decide),tsum_zero,add_zero]; unfold totals; simp_rw [soloGrad, (hp.mul_left _).tsum_mul_right,hp.tsum_mul_left]
  change Complex.log ((M 0).det⁻¹*_)=0; change Complex.log ((M 0).det⁻¹*(M (gradient A)).det)=_; rw [he,Matrix.det_mul,Matrix.det_mul,mul_right_comm (fond C A).det,← Matrix.det_mul,blink',Matrix.det_one,one_mul,inv_mul_cancel₀ (path_nonzero C h n).ne_zero, Complex.log_one]

def gradients (n:Side): Cher n→L[ℂ] Weather n:= LinearMap.toContinuousLinearMap { toFun:=gradient,map_add':=fun _ _=>by ext1 i; simp[gradient]; ring,map_smul':=fun i p=>by ext1 j; simp [gradient,Pi.smul_def,mul_sub] }
lemma dig_manual {E F D: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
    (f : F→ D) (g:E→L[ℂ] F) (u v:E)(h:AnalyticAt ℂ f 0) : dig u v (f∘g) 0=dig (g u) (g v) f 0:=by
  have ht : dew v (f∘g) =ᶠ[𝓝 0] dew (g v) f ∘g:=by
    have hh : Tendsto g (𝓝 0) (𝓝 0):= by simpa using g.continuous.tendsto 0
    filter_upwards [hh.eventually h.eventually_analyticAt] with i hi; rw [dew_chain g.differentiableAt hi.differentiableAt,dewp]; rfl
  unfold dig; rw [dew_var ht,dew_chain g.differentiableAt (by rw [map_zero]; exact voiced _ h),dewp,map_zero]
lemma glens (p : Site n)(x : Axis)(he: p ≠0)(ht: ∀ i,i≠x→cell p (step i)=1) :∃ u : Cher n, gradients n u=flashT p x:= by
  have hp: 1-cell p (step x) ≠0 := sub_ne_zero.mpr (by
    obtain ⟨i,hi⟩:=step_picks p he; by_cases h:i=x; · subst i; exact hi.symm
    exact False.elim (hi (ht i h)))
  refine ⟨fun i=> (1-cell p (step x))⁻¹ *cell p i, funext (fun i=> ?_)⟩
  change _-_ = flashT p x i; -- infer?
  unfold flashT; by_cases h:x=i.2
  · subst x; simp only [if_true]; change _ * _-(1-cell p (step i.2))⁻¹ *cell p (i.1+step i.2)=_; rw [cell_add]; field_simp
  rw [if_neg h]; change _ - _*cell p (i.1+step i.2)=0; rw [cell_add,ht _ (Ne.symm h),mul_one,sub_self]
lemma transverse (h:Package η a b c P v G U V)(p:Site n)(i:Axis)(he:p≠0)(ht:∀ j,j≠i→cell p (step j)=1) : polarization (extent C G U V n) i p=0:=by
  let M:=extent C G U V n
  obtain ⟨u,hu⟩:=glens p i he ht; obtain ⟨w,hw⟩:=glens (-p) i (neg_ne_zero.mpr he) (fun j hj=>by rw [fan_cell,ht j hj,inv_one])
  change -(dig _ _ (actual M) 0)= _; rw [← hu,← hw,← dig_manual _ (gradients n) u w (actualA (aria C (packBill h) h.scale n) (path_nonzero C h n)), show actual M ∘ (gradients n)=fun x=>0 from funext fun x=> warmth C h x];
  simp only [dig,dew_zero,neg_zero]; rw [show dew w (fun _=> (0:ℂ))=fun _=>0 from funext fun _=> dew_zero ..]; simp [dew]
lemma pol_even (h:Package η a b c P v G U V)(i:Axis)(p:Site n): polarization (extent C G U V n) i p = polarization (extent C G U V n) i (-p):=by
  let M:=extent C G U V n; have hp : AnalyticAt ℂ (actual M) 0 := actualA (aria C (packBill h) h.scale n) (path_nonzero C h n)
  change polarization M i p=polarization M i (-p); unfold polarization; rw [neg_neg,dig_two _ _ hp,dig_two _ _ hp]; congr 1; exact ContDiffAt.isSymmSndFDerivAt_of_omega hp.contDiffAt _ _ -- inspect
end YM.QCD.Pearl
