import YM.Next.FOUNDATIONS.Readout
import YM.Massive.Target.Calibration
/-!
# Tapered read, full-volume wager ANY anchor/lift
Actual taper of Goal. Weight conventions. `phase` for field readings at a requested
lift; use Lattice representatives in left derivative costs. No Sym enforced yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {c : Side}{d : ℕ}
namespace Beacon
variable (H:TaperHol)
-- depend even ambient horizon & both integer levels
abbrev Ln (d:ℕ):= Snap su (d/2)
abbrev spark (n:Side)(d:ℕ)(X:Ln d)(p:Edge Cover): su.El:= H.flow n d (expand _ X) 1 p 1
lemma focused (n:Side)(p:Edge Cover)(J:Labels.Jet su)(d:ℕ)(t:ℝ): H.flow n d J t p= H.flow n d (expand _ (trunk (d/2) (scaleJet J (t^2)))) 1 p:=by
   apply SolvesLink.unique (H.solves ..)
   have h := H.solves n d (expand _ (trunk (d/2) (scaleJet J (t^2)))) 1 p
   rw [show H.T.connection n d (expand _ (trunk (d/2) (scaleJet J (t^2)))) 1 p=H.T.connection n d J t p from ?_] at h -- unsolved placeholder
   exact h
   funext r; unfold Taper.connection; rw [one_pow]; apply congr_arg (fun v' : su.Color => _ • v')
   simp only [partConnection,one_smul,potential, Finset.smul_sum]; apply Finset.sum_congr rfl; intro j hj
   rw [Labels.Taylor.value_hom,smul_smul,show t^2*(t^2)^(j+1)=(t^2)^(j+2) by ring]
   simp only [expand,trunk,dif_pos (Finset.mem_range.mp hj)]
   simp [scaleJet,Labels.Taylor.value,Tensor.diagonal]; try rfl
lemma listens (n : Side)(d:ℕ)(p : Edge Cover) : AnalyticAt ℝ (fun J:Ln d => su.mat (spark H n d J p)) 0 ∧ spark H n d 0 p = 1 ∧ ∀ J : Ln d,
 HasDerivAt (fun t:ℝ=> su.mat (spark H n d (t • J) p)) (∫ s in (0:ℝ)..1, su.colorMat (H.T.connection n d (expand _ J) 1 p s)) 0:= by
   have hc (J:Ln d):Continuous (H.T.connection n d (expand _ J) 1 p):=by
      apply ((Taper.smooth H.T).continuous.comp (show Continuous (fun t:ℝ=> (n.val:ℝ)⁻¹ • (vector p.1 + t • basis p.2)) from by fun_prop)).smul
      unfold partConnection; simp only [one_pow,potential,one_smul]; refine continuous_finsetSum _ fun j _=>?_ ; exact (Tensor.diag_smooth _ 1).continuous.comp (by fun_prop)
   let L:Ln d →ₗ[ℝ] ℝ→su.Mat:={toFun:=fun (J:Ln d) t=> su.colorMat (H.T.connection n d (expand _ J) 1 p t),map_add':= ?_,map_smul':= ?_}
   rotate_left
   · intro J K; funext s; change su.colorMat _=su.colorMat _ + su.colorMat _
     rw [← map_add]; apply congr_arg; unfold Taper.connection; rw [← smul_add]; apply congr_arg
     simp only [partConnection,potential,one_smul,one_pow,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; simp only [Labels.Taylor.value, Tensor.diagonal,expand,dif_pos (Finset.mem_range.mp hi)]; rfl
   · intro r J; funext t; change su.colorMat _= r • su.colorMat _
     rw [← map_smul]; apply congr_arg; unfold Taper.connection; rw [smul_comm r]; apply congr_arg
     simp only [partConnection,potential,one_smul,one_pow,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; simp only [Labels.Taylor.value, Tensor.diagonal,expand,dif_pos (Finset.mem_range.mp hi)]; rfl
   obtain ⟨ha,hz,hw⟩:=Work.G02.endpointGerm L (fun J=>su.colorMat.continuous_of_finiteDimensional.comp (hc J)) (fun X t=>su.mat (H.flow n d (expand _ X) 1 p t)) (fun x=>by simp only [(H.solves ..).1, su.mat_one]) (fun x t=> (H.solves ..).2 t)
   exact ⟨ha,su.mat_injective (hz.trans su.mat_one.symm),hw⟩
-- use o mod c, integer lift b. AP price orientation on copied anchor. if b crossing, sign mapping from expression in absolute to relative. For profile winding convention: argument modes at unsigned, test at lift ABSOLUTE = b+relative with AP sign. Thus ap c (lift(y -o)+b)
variable (b : Cover)
abbrev offset (b : Cover)(x:Site c): Cover := lift (x-wrap c b)
def views (d:ℕ)(x:Ln d): Grid c:=fun i=> spark H c d x (offset b i.1,i.2)
abbrev current (d:ℕ) (J:Labels.Jet su)(t:ℝ) : Grid c := views H b d (trunk (d/2) (scaleJet J (t^2)))
def lamp (x:Ln d): Directions su c:= fun i=> su.plog (su.mat (views H b d x i))
lemma fluent (d:ℕ) (c:Side): AnalyticAt ℝ (lamp (c:=c) (d:=d) H b) 0 := by
   apply ContDiffAt.analyticAt
   refine contDiffAt_pi.mpr fun i=>?_
   have he:= listens H c d (offset b i.1,i.2)
   exact (show ContDiffAt ℝ ω su.plog (su.mat (spark H c d 0 (offset b i.1,i.2))) from by rw [he.2.1,su.mat_one]; exact su.plog_diff).comp (0:Ln d) he.1.contDiffAt
lemma at_home (d:ℕ) (c:Side): views (c:=c) H b d 0=1:= funext fun i=> (listens H c d _).2.1
lemma at_dark : lamp (d:=d) (c:=c) H b 0=0:= funext fun i=> by simp only [lamp,at_home, Pi.one_apply, su.mat_one,su.plog_one]; exact rfl
lemma at_east : views (c:=c) H b d =ᶠ[𝓝 (0:Ln d)] increment 1 ∘ lamp H b:=by
   suffices hh:∀ i : Edge (Site c), ∀ᶠ x in 𝓝 (0:Ln d), views H b d x i = increment 1 (lamp H b x) i by filter_upwards [eventually_all.mpr hh] with x h; exact funext h
   intro i; let f x:= views H b d x i; have he:=listens H c d (offset b i.1,i.2); have hh : ContinuousAt f 0:= (su.continuous_mat.isClosedEmbedding su.mat_injective).isInducing.continuousAt_iff.mpr he.1.continuousAt
   have ht : Tendsto f (𝓝 0) (𝓝 1):=by
      have h0:f 0=1 := he.2.1; rw [← h0]; exact hh
   filter_upwards [ht.eventually su.plog_right] with x hx; change _=su.lieExp (su.plog (su.mat (f x)))*1; rw [mul_one]; exact hx.symm
lemma current_read (d:ℕ)(n:Side)(J:Labels.Jet su)(v:ℝ): current (c:=n) H 0 d J v = H.links n d J v :=by
   funext l; unfold current views spark offset TaperHol.links; rw [map_zero,sub_zero]; symm; exact congr_fun (focused H ..) 1 -- may rew both
abbrev spun (T:Taper)(b : Cover)(x:Site c):ℂ:= let u:=offset b x; (T.χ ((c.val:ℝ)⁻¹ • vector u):ℂ)*ap c (u+b)
def glow (T:Taper) (b:Cover)(v:ℝ): Matrix (Modes c 6) (SpinMode d) ℂ:= Matrix.of fun i j=> if i.1.2=j.1.2 ∧ i.2=j.2 then spun T b i.1.1*profile j.1.1 (offset b i.1.1) v else 0
lemma glow_read (T:Taper)(v:ℝ):glow (d:=d) (c:=c) T 0 v=T.spin v:= by ext i j; simp [glow,spun,Taper.spin,offset]
end Beacon
end YM.Massive.Poised
