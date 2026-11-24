import YM.Poised.Halcyon
import YM.Planned.PRIMARY_INTEGRAL_295.ZeroPath
/-! # Both stack readings in polynomial units, not linearized only -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d a k n:ℕ}{c:Side}
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
namespace Palette
open Beacon Gem MultiNext.SignedSource YM.Next.Foundations QCD.Cove QCD.Creek Pipes Display QCD.Kites Film
-- profile leading arbitrary gate,
variable (d)(J:Labels.Jet su) (θ h:ℝ)
abbrev ZBand (d:ℕ):=Faces (UV.Multi d)
abbrev lode (c:Side)(b:Cover)(H:TaperHol) := lamp (c:=c) H b ∘ scaledD d J
variable {d}
lemma lode_smooth (d:ℕ)(H:TaperHol)(c:Side)(b:Cover): ContDiffAt ℝ d (lode d J c b H) 0:= (show ContDiffAt ℝ (d:WithTop ℕ∞) (lamp (c:=c) (d:=d) H b) (scaledD d J 0) from (scaled_zero d _).symm ▸ ((fluent H b d c).contDiffAt.of_le le_top)).comp _ (scaled_smooth d J)
lemma inPlace (d:ℕ)(H:TaperHol)(c:Side)(b:Cover): lode d J c b H 0=0:= by unfold lode; rw [Function.comp_apply,scaled_zero,at_dark] -- transport fragile
local instance : NormedSpace ℝ (Snap su d):= inferInstance
private lemma grain (i:Fin (d/2-1))(hn:n≤d): iteratedDeriv n (scaledD d J) 0 i=(if n=2*(i.val+2) then (n.factorial:ℝ) else 0) • J i.val:=by
    let p:= Fin (d/2-1)
    let A(i:p):Snap su (d/2):=Pi.single i (J i.val)
    let f(i:p)(t:ℝ):=t^(2*(i.val+2)) • A i
    have h(i:p): ContDiffAt ℝ n (f i) 0:= ContDiffAt.smul (contDiffAt_id.pow _) contDiffAt_const
    have hg(i:p):iteratedDeriv n (f i) 0=(if n=2*(i.val+2) then (n.factorial:ℝ) else 0) • A i:=by unfold f; rw [iteratedDeriv_smul_const (contDiffAt_id.pow _), iteratedDeriv_fun_pow_zero]; split_ifs with hh <;> simp [*]
    rw [show scaledD d J=(fun t=>∑ i:p,f i t) from ?_, iteratedDeriv_fun_sum (fun i _=>h i)]
    · simp_rw [hg]; rw [Finset.sum_apply]; change ∑ j:p, _= _; rw [Finset.sum_eq_single i]; · rw [Pi.smul_apply]; simp [A]
      · intro q _ h; rw [Pi.smul_apply,show A q i=0 from Pi.single_eq_of_ne h.symm _,smul_zero]
      simp
    funext t j; rw [Finset.sum_apply,Finset.sum_eq_single j]; · change (t^2)^(j.val+2) • _= _; rw [← pow_mul]; simp [f,A]
    · intro q _ h; unfold f; rw [Pi.smul_apply,show A q j=0 from Pi.single_eq_of_ne h.symm _,smul_zero]
    simp
def pore (d:ℕ)(J:Labels.Jet su)(n:ℕ)(X:E4)(i:Axis): su.Color := iteratedDeriv n (lane X i ∘ scaledD d J) 0
lemma lode_mem (H:TaperHol) (b:Cover)(V:Support c)(hx:Nonwrapping V (wrap c b))(hV:100 ≤ c.val)(i:Edge (Site c))(he: Mom.needed V i)(hn:n≤d): iteratedDeriv n (lode d J c b H) 0 i=pore d J n (vector (Beacon.offset b i.1)) i.2:=by
   obtain ⟨A⟩:=Source.Hol.exists_ode su; let L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ :Edge (Site c)=>su.Color) i
   change L (iteratedDeriv n (lode d J c b H) 0)= _; rw [←Display.clm_step _ _ _ ((lode_smooth J d H c b).of_le (show (n:WithTop ℕ∞)≤d from Nat.cast_le.mpr hn)) L]
   unfold pore; apply congr_arg (fun f=>iteratedDeriv n f 0); funext t; change su.plog (su.mat (views H b d (scaledD d J t) i))= _; rw [traverse b hx hV H A (scaledD d J t) i he]; exact (lane_truth A (Beacon.offset b i.1,i.2) (scaledD d J t)).symm
private def agent (r:OrderedFinpartition n) (d:ℕ)(J:Labels.Jet su) : Potential su := fun x i=> iteratedFDeriv ℝ r.length (lane x i (d:=d/2)) 0 (fun j=>iteratedDeriv (r.partSize j) (scaledD d J) 0)
private lemma ownership (hn:n≤d): pore d J n= ∑ r:OrderedFinpartition n,agent r d J:=by
   funext x i; rw [Finset.sum_apply,Finset.sum_apply,pore,iteratedDeriv_vcomp_eq_sum_orderedFinpartition _ (scaled_smooth d J) (Nat.cast_le.mpr hn),scaled_zero]; exact rfl
   rw [scaled_zero]; exact (lane_smooth x i (G:=su) (d:=d/2)).of_le le_top
private lemma oddHole (hn:n≤d)(r:OrderedFinpartition n)(j:Fin r.length)(he:r.partSize j%2=1): agent r d J=0:=by
   funext x i; exact (iteratedFDeriv ℝ _ (lane x i (G:=su) (d:=d/2)) 0).map_coord_zero j (show iteratedDeriv (r.partSize j) (scaledD d J) 0=0 from funext fun i=>by rw [grain J i ((r.partSize_le j).trans hn),if_neg (by omega),zero_smul]; rfl)
private lemma weightsSum (r:OrderedFinpartition n) : (∑ i, r.partSize i)=n:=by simpa using r.sum_sigma_eq_sum (fun _=>(1:ℕ))
lemma pore_blank (hn:n≤d)(he:n%2=1) : pore d J n=0:=by
   rw [ownership J hn]; apply Finset.sum_eq_zero; intro i _; by_contra ht; have h (l): i.partSize l%2=0:= by have h : i.partSize l%2≠1:=fun hx=> ht (oddHole J hn i l hx); omega
   have H:n=(∑ l,i.partSize l/2)*2:= by apply Eq.trans (weightsSum i).symm; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _=> by have:=h j; omega
   omega
lemma pore_sign (hn:n≤d): pore d J n∈ rangeLt (Axis→su.Color) (n/2):=by
    rw [ownership J hn]; apply Submodule.sum_mem; intro i _; by_cases h:∃ j,i.partSize j%2=1
    · obtain ⟨j,hj⟩:=h; rw [oddHole J hn i j hj]; exact Submodule.zero_mem _
    have hl(j):0 < i.partSize j / 2:=by have he:i.partSize j%2≠1:=fun hx=>h ⟨j,hx⟩; have:=i.partSize_pos j; omega
    apply grows (Axis→su.Color) ((share i.partSize).trans (by rw [weightsSum])); refine lane_polynomial _ _ (fun j p hp=>?_) hl; rw [grain J p ((i.partSize_le j).trans hn),if_neg (by omega),zero_smul]
section Spin
-- normalization: unscaled function.Support.Local.
abbrev woe (T:Taper)(b:Cover)(v t:ℝ)(d:ℕ) : VectorD (Site c) (ZBand d):= v • (show VectorD _ _ from chain T b t d)
private lemma woe_rake (T:Taper)(b:Cover)(v t:ℝ)(i:Site c)(u j:Shell)(p:UV.Multi d): asks (woe T b v t d) i u ((stretch _) (p,j))=t^spinWeight p • (if u=j then v • (Beacon.spun T b i * (score p (vector (Beacon.offset b i)):ℂ)) else (0:ℂ)):=by -- score p ℝ, cast
   change v • (chain (c:=c) T b t d _ _)= _; rw [scion]; split; swap; · simp
   rw [show profile p _ t=(↑(t^spinWeight p * (score p (vector (Beacon.offset b i))):ℝ):ℂ) from rfl]
   simp only [Complex.real_smul, Complex.ofReal_mul];ring -- p score.
lemma woe_smooth (T:Taper)(b:Cover)(v:ℝ)(d:ℕ): ContDiffAt ℝ d (fun t=> woe (c:=c) T b v t d) 0:=by
   apply contDiffAt_pi.mpr; intro i; obtain ⟨⟨x,i⟩,rfl⟩:= (stretch _).surjective i
   apply contDiffAt_pi.mpr; intro j; obtain ⟨⟨p,j⟩,rfl⟩:= (stretch _).surjective j; change ContDiffAt ℝ _ (fun t=> asks (woe T b v t d) x i _) _; simp_rw [woe_rake]; exact (contDiffAt_id.pow _).smul contDiffAt_const
lemma woe_nil (T:Taper)(b:Cover)(v:ℝ)(d:ℕ): woe (c:=c) T b v 0 d=0:=by
   apply flat_ext; intro x; funext i j; obtain ⟨⟨p,j⟩,rfl⟩:= (stretch _).surjective j; rw [woe_rake, zero_pow (by simp [spinWeight]),zero_smul]; rfl
-- real scaleS v.
def poseS (d n:ℕ)(v:ℝ)(x:E4): Flet (ZBand d):=fun i j=> let t:=(stretch (UV.Multi d)).symm j; if i=t.2 ∧ n=spinWeight t.1 then v • (n.factorial:ℝ) • (score t.1 x:ℂ) else 0
lemma posesS (d n:ℕ)(T:Taper)(b:Cover)(v:ℝ)(hn:n≤d)(x:Site c) : asks (iteratedDeriv n (fun t=> woe (c:=c) T b v t d) 0) x = Beacon.spun T b x • poseS d n v (vector (Beacon.offset b x)):=by
   funext i j; obtain ⟨⟨p,j⟩,rfl⟩:= (stretch _).surjective j;
   let L:VectorD (Site c) (ZBand d)→L[ℝ]ℂ:= (ContinuousLinearMap.proj ((stretch _) (p,j))).comp ((ContinuousLinearMap.proj i).comp (askCL x))
   let g(t:ℝ):=woe (c:=c) T b v t d
   change L (iteratedDeriv n g 0)= _; rw [← Display.clm_step g n 0 ((woe_smooth T b v d (c:=c)).of_le (Nat.cast_le.mpr hn)) L]; change iteratedDeriv n (fun t=>asks (woe T b v t d) x i _) 0= _; simp_rw [woe_rake]; rw [iteratedDeriv_smul_const (contDiffAt_id.pow _), iteratedDeriv_fun_pow_zero]
   by_cases hi:i=j <;> by_cases he:n=spinWeight p <;> simp only [Pi.smul_apply,poseS,Equiv.symm_apply_apply,hi,he,ite_true, true_and] <;> simp [he,hi,Complex.real_smul] <;> ring
lemma pose_band (d n:ℕ)(v:ℝ): poseS d n v∈ rangeLt (Flet (ZBand d)) ((n-1)/2):=by
   apply vector_band; intro i; apply vector_band; intro j; obtain ⟨⟨p,j⟩,rfl⟩:= (stretch _).surjective j; simp only [poseS,Equiv.symm_apply_apply]; split; swap; · exact Submodule.zero_mem _
   next h=>
      have he:=h.2
      let V:= (n.factorial:ℝ); refine Submodule.smul_mem _ v (Submodule.smul_mem _ V (show (fun x=> (score p x:ℂ))∈ _ from ?_))
      rw [show (fun x:E4=> (score p x:ℂ))=fun x=> score p x • (1:ℂ) from funext fun _=> by rw [Complex.real_smul,mul_one]]; apply exact_le_band _ (Gem.homogeneous p _); unfold spinWeight at h; omega
lemma pose_empty (d:ℕ)(v:ℝ)(h:n%2=0): poseS d n v=0:=by
   funext x i j; unfold poseS; dsimp only; split; next hi=> unfold spinWeight at hi; omega
   next=>rfl
end Spin
end Palette
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Palette.lode_mem
