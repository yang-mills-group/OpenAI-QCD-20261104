import YM.Poised.Cask
import YM.QCD.Dust.Peak
/-!
# Rotation paid without costing volume. Bound seats on the whole spin slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry
open YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform
variable (b:Cover) [Fintype B]
private abbrev pinC (i:Pipes.Shell) : Flet Unit:= (Pi.single i fun _=>1)
def frameQ (y:su.Color) (i j:Pipes.Shell):ℂ:= scaleG (y,pinC j) i ()
def yaw (i j:Pipes.Shell)(y:su.Color):ℂ:= frameQ y i j-frameQ 0 i j
lemma quote (z:su.Color)(x:Flet B)(i:Pipes.Shell)(j:B): scaleG (z,x) i j=∑ k:Pipes.Shell, frameQ z i k * x k j:=by
   unfold frameQ scaleG stepF; refine Finset.sum_congr rfl fun k _=>?_ ; dsimp only; congr 1; symm; rw [sum_eq_single k]; · simp only [pinC, Pi.single_eq_same,mul_one]
   · intro u _ hu; simp only [pinC,Pi.single_eq_of_ne hu,Pi.zero_apply,mul_zero]
   simp
lemma yaw_smooth (i j:Pipes.Shell): ContDiff ℝ ω (yaw i j) :=by
   unfold yaw; apply ContDiff.sub _ contDiff_const; exact contDiff_pi.mp (contDiff_pi.mp (((scaleG_live (B:=Unit))).comp (f:=fun x=>(x,pinC j)) (contDiff_id.prodMk contDiff_const)) i) ()
lemma charterY (n:ℕ):∃ C:ℝ,1≤C ∧ ∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x C:=by
   choose C hC H using fun i j=> exists_allows (f:=yaw i j) (isCompact_closedBall 0 1) (fun v hv=> (yaw_smooth i j).contDiffAt) n
   let V:=∑ i:Pipes.Shell,∑ j:Pipes.Shell,C i j
   refine ⟨1+V,le_add_of_nonneg_right (sum_nonneg fun i _=> sum_nonneg fun j _=> hC ..),fun i j x hx=>?_⟩
   exact (Through.control (H i j x (mem_closedBall_zero_iff.mpr hx))).mono (((single_le_sum (f:=C i) (fun j _=>hC ..) (mem_univ j)).trans (single_le_sum (f:=fun i=>∑ j:Pipes.Shell,C i j) (fun i _=>sum_nonneg fun j _=>hC ..) (mem_univ i))).trans (le_add_of_nonneg_left zero_le_one))

variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable {C v t p:ℝ}{y: E→ Site c→su.Color}
def diffQ (y:E→Site c→su.Color) (z:VectorD (Site c) B) (x:E):= hailC (sealsZ (y x)) z-z
lemma callsQ(v:Pipes.Shell)(z:VectorD (Site c) B)(s:Site c) (x:E)(i:B): diffQ y z x (stretch _ (s,v)) i=∑ j:Pipes.Shell,yaw v j (y x s)*z (stretch _ (s,j)) i:=by
    change asks (hailC _ z) s v i-asks z s v i=_; rw [hailF]
    nth_rw 2 [← step_one (asks z s)]
    unfold sealsZ; rw [show stepF (su.mat _) (asks z s)=_ from (show stepF (su.mat (su.lieExp (y x s))) (asks z s)=scaleG (y x s,asks z s) from rfl)]; rw [show stepF 1 (asks z s)=scaleG (0,asks z s) from by simp [scaleG]]; simp_rw [quote,yaw,sub_mul,sum_sub_distrib]; rfl
variable (z:VectorD (Site c) B)(C M:ℝ) (hM:Through n y 0 M) (hv:M ≤1) (ht :1 ≤ n) (h:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x C)
include hM hv ht h
local notation "W"=> (1+patterns n)*(C*M)
lemma headQ (i j:Pipes.Shell)(s:Site c) : Through n (fun x=>yaw i j (y x s)) 0 W:=by
    let L : (Site c →su.Color)→L[ℝ]su.Color:= ContinuousLinearMap.proj s; have hx:‖L‖ ≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun V=> by rw [one_mul]; exact norm_le_pi_norm V s)
    have he:Through n (L ∘ y) 0 M:= (one_mul M) ▸ linear_through L hM hx
    exact Dust.jersey (L ∘ y) (yaw i j) 0 he (h i j) hv ht (sub_self _)
lemma diff_live: ContDiffAt ℝ n (diffQ y z) 0:=by
   refine contDiffAt_pi.mpr fun i=>?_ ; obtain ⟨⟨i,j⟩,rfl⟩:= (stretch _).surjective i; refine contDiffAt_pi.mpr fun k=>?_ ; simp_rw [callsQ]; exact ContDiffAt.sum fun w _=> ((headQ C M hM hv ht h j w i).smooth).mul contDiffAt_const
lemma line_cost (k:ℕ)(s:Site c)(w:B→ℝ)(pw:0<p)(hw':∀ i:B,0<w i)(H: SeatD (purseX s k p) w z v) (A:ℕ)(hr:A ≤ n)(x : Fin A → E)(hx:∀ i,‖x i‖ ≤1): SeatD (purseX s k p) w (iteratedFDeriv ℝ A (diffQ y z) 0 x) (W*((Fintype.card Pipes.Shell:ℝ)*v)):=by
   have hW:0 ≤ W:= (headQ C M hM hv ht h (Sum.inl 0) (Sum.inr 0) s).nonneg
   have hV' := (SeatD.from_weights _ _ _ _ (purse_pos s k p pw) (fun i=> (hw' i).le)).1 H
   apply (SeatD.from_weights _ _ _ _ (purse_pos s k p pw) (fun i=> (hw' i).le)).2; refine ⟨mul_nonneg hW (mul_nonneg (by positivity) H.1),fun i=>?_⟩
   obtain ⟨⟨u,v'⟩,rfl⟩:= (stretch _).surjective i; let j:= stretch (Site c) (u,v'); let V:=diffQ y z; let f i' s:=yaw v' i' (y s u); have he(i':Pipes.Shell): ContDiffAt ℝ A (f i') 0:= (headQ C M hM hv ht h v' i' u).smooth.of_le (Nat.cast_le.mpr hr)
   have ht(k:B):‖iteratedFDeriv ℝ A V 0 x j k‖≤∑ a:Pipes.Shell,W * ‖z (stretch _ (u,a)) k‖ :=by
       let L :VectorD (Site c) B →L[ℝ] ℂ:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:B=>ℂ) k).comp (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Faces (Site c)=>B→ℂ) j); let g a:=z (stretch _ (u,a)) k
       have hh : L ∘ V=∑ a:Pipes.Shell, g a • f a:=funext fun s=>by rw [Finset.sum_apply]; exact (callsQ ..).trans (sum_congr rfl fun i _=>mul_comm ..)
       rw [show iteratedFDeriv ℝ A V 0 x j k=iteratedFDeriv ℝ A (L ∘ V) 0 x from (DFunLike.congr_fun (L.iteratedFDeriv_comp_left (diff_live z C M hM hv ht h) (Nat.cast_le.mpr hr)) x).symm,hh, iteratedFDeriv_sum_apply (fun i _=>  (show ContDiffAt ℝ (↑A) (g i • f i) 0 from (he i).const_smul (g i))), _root_.sum_apply] -- name
       apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_ ; rw [iteratedFDeriv_const_smul_apply (he i), _root_.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left (((iteratedFDeriv ℝ A (f i) 0).unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hx)).trans ((headQ C M hM hv ht h v' i u).pay A hr)) (norm_nonneg _)).trans_eq (mul_comm ..)
   apply le_trans (Finset.sum_le_sum (g:=fun i:B=> w i * ∑ a:Pipes.Shell,W * ‖z (stretch _ (u,a)) i‖) (fun i _=>mul_le_mul_of_nonneg_left (ht i) (hw' i).le)); simp_rw [Finset.mul_sum,mul_left_comm _ W]; rw [sum_comm]; simp_rw [← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hV'.2 (stretch _ (u,i)))) hW).trans_eq ?_; unfold purseX; simp_rw [life]; simp only [Finset.sum_const,nsmul_eq_mul,card_univ]; ring -- simplify lh
end Pipes
end YM.Massive.Poised
