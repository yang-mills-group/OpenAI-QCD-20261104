import YM.Poised.Skiffs
/-! # AP exact polynomial incl bar moments. Translate at root.Filtration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Steed
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
variable (P:Flight j k) (h:l.val=c.val*P.L.val) (hk:4≤k) {q:Cover →ℂ}{σ C:ℝ}(hσ :0<σ)(hW:Width σ C q)
abbrev spawn (q:Cover→ℂ)(f:E4→ℂ)(x:E4):ℂ:= ∑' z, q z*f (x+Place.seat z)
include hW hσ
private lemma fish (x:E4)(f:E4→ℂ)(hf:f∈ rangeLt ℂ n): Summable fun z=>q z*f (x+Place.seat z):=by
    apply Summable.of_norm; have he:=band_shift hf x; obtain ⟨A,hA,h⟩:= band_growth he; apply ((width_billG hσ hW n).2.1.mul_left A).of_nonneg_of_le (fun _=>norm_nonneg _); intro i; rw [norm_mul,add_comm x]; refine (mul_le_mul_of_nonneg_left ((h (Place.seat i)).trans (mul_le_mul_of_nonneg_left ?_ hA)) (norm_nonneg _)).trans_eq (mul_left_comm ..); exact pow_le_pow_left₀ (by positivity) (add_le_add_right (shade_seat i) 1) _
omit hσ hW
lemma compress_band {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{f:E4→F}(h:f∈rangeLt F n) (a:ℝ): (fun t:E4=> f (a • t))∈rangeLt F n:=by
   obtain ⟨W,H,rfl⟩:= range_decompose h
   rw [show (fun t:E4=>(∑ i,W i) (a • t))= ∑ i:Fin n,a^i.val • W i from funext fun t=>by
      rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> exact_scale (H i) t a]
   exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (exact_le_band i.isLt (H i))
private instance : FiniteDimensional ℝ (rangeLt ℂ n):=by
   induction n with
   | zero=> rw [rangeLt]; infer_instance
   | succ n ih=> rw [rangeLt_succ]; letI := ih; unfold exactDegree; infer_instance
include hσ hW
lemma castS (v:E4)(f g:E4→ℂ)(hf:f∈ rangeLt ℂ n)(hg:g∈rangeLt ℂ k): spawn q (f+g) v=spawn q f v+spawn q g v:=by
   unfold spawn; simp only [Pi.add_apply,mul_add]; exact (fish hσ hW v f hf).tsum_add (fish hσ hW v g hg)
lemma dart (f:E4→ℂ)(a:ℝ)(hf:f∈rangeLt ℂ n):
    (fun t:E4=> spawn q f (a • t)) ∈ rangeLt ℂ n:=by
   let Z:= (rangeLt ℂ n)
   have h: HasSum (fun k:Cover=> fun p:E4=> q k * f (a • p + Place.seat k)) (fun t:E4=>spawn q f (a • t)):= Pi.hasSum.mpr (fun i=> (fish hσ hW (a • i) f hf).hasSum)
   refine Z.closed_of_finiteDimensional.mem_of_tendsto h (Eventually.of_forall (fun u=>?_))
   apply Submodule.sum_mem; intro i _; let L:ℂ→L[ℝ]ℂ:= q i • ContinuousLinearMap.id ℝ _; exact linear_band L _ (compress_band (band_shift hf (Place.seat i)) a)
lemma dart_sway (f:E4→ℂ)(a:ℝ)(hf:f∈rangeLt ℂ (n+1)):
    (fun t:E4=> spawn q f (a • t)-((∑' z,q z)*a^n)*f t)∈rangeLt ℂ n:=by
   rw [rangeLt_succ] at hf; obtain ⟨X,hX,F,hF,rfl⟩:= Submodule.mem_sup.mp hf
   let W(z : Cover)(t:E4):= q z*(X (a • t + Place.seat z)-X (a • t)); let p:ℂ:= (∑' z,q z)* (a:ℂ)^n; have h(t:E4): HasSum (fun z=>W z t) (spawn q X (a • t)-p*X t):=by
      have h : ((∑' z,q z)* X (a • t))= p*X t:=by unfold p; rw [exact_scale hX, Complex.real_smul]; simp only [Complex.ofReal_pow]; ring
      refine ?_ -- tsum
      simp only [W,mul_sub]; rw [←h]; exact (fish hσ hW _ X (exact_le_band n.lt_succ_self hX)).hasSum.sub (((hW.unweighted hσ.le).2.1.of_norm.hasSum).mul_right _)
   have he:(fun t:E4=> spawn q X (a • t)-p*X t)∈rangeLt ℂ n:=by
       have hv : HasSum W (fun t:E4=> spawn q X (a • t)-p*X t):= Pi.hasSum.mpr h
       apply (rangeLt ℂ n).closed_of_finiteDimensional.mem_of_tendsto hv (Eventually.of_forall (fun i=>Submodule.sum_mem _ (fun z _=>?_))) -- syntax
       let L:ℂ→L[ℝ]ℂ:= q z • ContinuousLinearMap.id ℝ _; exact linear_band L _ (compress_band (pure_step hX _) a)
   let L : ℂ→L[ℝ]ℂ:= p • ContinuousLinearMap.id ℝ _; have hx: ∀ i:E4,L (F i)=p*F i:=fun _=>rfl
   convert Submodule.add_mem _ he (Submodule.sub_mem _ (dart hσ hW F a hF) (linear_band L n hF)) using 1
   funext i; simp only [Pi.sub_apply,Pi.add_apply, hx]; rw [castS hσ hW (a • i) -- fix args
     X F (exact_le_band n.lt_succ_self hX) hF]; unfold p; push_cast; ring
omit hW hσ
-- adapted Paint.R.Plan
private def soul (n : ℕ) (p : E4) : Tensor.T RouteProbe ℝ n :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap (fun _ => ContinuousLinearMap.apply ℝ ℝ p)
private lemma soul_price (n : ℕ) (p : E4) : ‖soul n p‖ ≤ ‖p‖^n := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun x => ?_
  change ‖∏ i,x i p‖≤ _; rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (x i).le_opNorm p)).trans ?_
  rw [Finset.prod_mul_distrib,mul_comm]; simp
private def harpC (p:ℂ)(x:E4) : Tensor.T RouteProbe ℂ n := (p • Complex.ofRealCLM).compContinuousMultilinearMap (soul n x)
private lemma harpC_price (p:ℂ)(x:E4) : ‖harpC (n:=n) p x‖ ≤ ‖p‖*‖x‖^n:=by
   refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun h=> ?_; change ‖p*(soul n x h:ℂ)‖ ≤ _; rw [norm_mul,Complex.norm_real,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply ((soul n x).le_opNorm _).trans; exact mul_le_mul_of_nonneg_right (soul_price ..) (prod_nonneg fun _ _=> norm_nonneg _)
include hσ hW
set_option maxHeartbeats 600000 in
private lemma passageL (v :E4)(w:Fin n→RouteProbe): HasSum (fun z=> q z*(∏ i,w i (v+Place.seat z):ℝ)) ((∑' z, harpC (n:=n) (q z) (v+Place.seat z)) w):=by
   have ht : Summable (fun z=>harpC (n:=n) (q z) (v+Place.seat z)):=by
       apply Summable.of_norm; apply ((width_billG hσ hW n).2.1.mul_left ((1+‖v‖)^n)).of_nonneg_of_le (fun _=>norm_nonneg _); intro i
       refine (harpC_price ..).trans ((mul_le_mul_of_nonneg_left (c:=( (1+‖v‖)*(1+(size i:ℝ)))^n) ?_ (norm_nonneg _)).trans_eq ?_)
       · apply pow_le_pow_left₀ (norm_nonneg _); refine (norm_add_le ..).trans ((add_le_add_right (shade_seat i) _).trans ?_); nlinarith [norm_nonneg v, Nat.cast_nonneg (α:=ℝ) (size i)]
       unfold liftCost; rw [mul_pow,mul_left_comm]
   exact (ContinuousMultilinearMap.apply ℝ _ ℂ w).hasSum ht.hasSum
private lemma soul_spec (w : E4) : Tensor.Sym (∑' z,harpC (n:=n) (q z) (w+Place.seat z)) := by
  intro x s
  rw [← (passageL hσ hW w (x ∘ s)).tsum_eq, ← (passageL hσ hW w x).tsum_eq]; refine tsum_congr fun z => ?_; exact congr_arg (fun t:ℝ=> q z*t) (Equiv.prod_comp s (fun a => x a _))
private def chips (A:Tensor.T E4 ℂ n) (p:Fin n→Axis) (x:E4):= (∏ i,x (p i)) • A (basis∘p)
private lemma cam (A:Tensor.T E4 ℂ n)(u:E4): spawn q (Tensor.diagonal A) u=∑ i:Fin n→Axis, (∑' z,q z*(∏ j,(u+Place.seat z) (i j):ℝ))*A (basis ∘ i):=by
    let v(i:Fin n→ Axis)(j:Fin n):RouteProbe:= EuclideanSpace.proj (i j)
    have he (x:E4):Tensor.diagonal A x=∑ p,chips A p x:= by
       unfold Tensor.diagonal; rw [show (fun _:Fin n=>x)=(fun _=>∑ i:Axis, x i • basis i) from funext fun _=>by ext a; simp]; rw [A.map_sum (fun _ a=>x a • basis a)]; simp_rw [A.map_smul_univ]; rfl
    have ht i:Summable fun z=> q z*(∏ k,(v i k) (u+Place.seat z):ℝ):=(passageL hσ hW u (v i)).summable
    unfold spawn; simp_rw [he,mul_sum,chips,Complex.real_smul,← mul_assoc]
    change (∑' z, ∑ i,q z*(∏ k,(v i k) (u+Place.seat z):ℝ)*A (basis ∘ i))= _
    rw [Summable.tsum_finsetSum (fun i _=> (ht i).mul_right _)]
    refine sum_congr rfl fun i _=> by simp only [tsum_mul_right]; rfl
omit hσ hW
include hk
lemma roll_pure (u v:Pipes.Shell)(x:Cover)(f:E4→ℂ)(h:f∈exactDegree ℂ n)(hn:n<j):spawn (arch P u v x) f (Place.seat (cellar P.L x))=spawn (arch P u v 0) f ((P.L.val:ℝ)⁻¹ • Place.seat x):=by
   obtain ⟨A,B,hA,hB,H⟩:=archG P hk; let q:=arch P u v; have hq(y) : Width A B (q y):= H _ _ _; let X:=Place.seat (cellar P.L x); let Y:=(P.L.val:ℝ)⁻¹ • Place.seat x
   have hp : (∑' z, harpC (n:=n) (q x z) (X+Place.seat z))=(∑' z,harpC (q 0 z) (Y+Place.seat z)):=by
       apply Tensor.ext_diag _ _ (soul_spec hA (hq _) _) (soul_spec hA (hq _) _)
       funext Z; unfold Tensor.diagonal; rw [← (passageL hA (hq x) X _).tsum_eq,← (passageL hA (hq 0) Y _).tsum_eq]
       have h:=roll_probe P hk u v x Z hn
       simp only [Complex.real_smul] at h; simp_rw [prod_const,card_univ,Fintype.card_fin, mul_comm _ (↑((Z _:ℝ)^n):ℂ)]; exact h
   obtain ⟨M,rfl⟩:= can_write.mp h
   rw [cam hA (hq _) M,cam hA (hq _) M]; refine sum_congr rfl fun i _=> ?_; apply congr_arg (· * M (basis ∘ i)); let W(k:Fin n):RouteProbe:= EuclideanSpace.proj (i k); exact (passageL hA (hq x) X W).tsum_eq.trans ((DFunLike.congr_fun hp W).trans (passageL hA (hq 0) Y W).tsum_eq.symm)
lemma roll_band (u v:Pipes.Shell)(x:Cover)(f:E4→ℂ)(h:f∈rangeLt ℂ n)(hn:n≤j):spawn (arch P u v x) f (Place.seat (cellar P.L x))=spawn (arch P u v 0) f ((P.L.val:ℝ)⁻¹ • Place.seat x):=by
    induction n generalizing f with
    | zero=> rw [rangeLt,Submodule.mem_bot] at h; simp [h,spawn]
    | succ n ih=>
       obtain ⟨A,B,hA,hB,H⟩:=archG P hk
       rw [rangeLt_succ] at h; obtain ⟨U,hU,Y,hY,rfl⟩:= Submodule.mem_sup.mp h
       rw [castS hA (H u v x) _ U Y (exact_le_band n.lt_succ_self hU) hY, castS hA (H u v 0) _ U Y (exact_le_band n.lt_succ_self hU) hY, ih Y hY (by omega),roll_pure P hk u v x U hU hn]
end Steed
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Steed.roll_band
#print axioms YM.Massive.Poised.Steed.dart_sway
