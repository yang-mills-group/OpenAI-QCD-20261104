import YM.Poised.Prism
import YM.Next.FOUNDATIONS.TestBounds
/-! # Tapered link calculus: uniform post entirely in native prices.
No cost from support length on torus except normal left directions at the chosen root. Reuse G02. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus
variable {c : Side} {d k : ℕ}
namespace Beacon
variable (H:TaperHol)(b : Cover)
local notation "F" => Lat.Fields c 6
local notation "G" => SpinPol d
local notation "N" => Pairs (SpinMode d)
-- use general continuous path space at matrix value.Norm.E.Entry
namespace Verse
section General
variable {Y R : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedRing R][NormedAlgebra ℝ R][CompleteSpace R]
local notation "W"=>C(unitInterval,R)
private def primitive [CompleteSpace Y] : C(unitInterval, Y) →L[ℝ] C(unitInterval, Y) := by
  let π := projIcc (0 : ℝ) 1 zero_le_one
  have hint (U : C(unitInterval, Y)) (a b : ℝ) :
      IntervalIntegrable (fun s => U (π s)) volume a b :=
    (U.continuous.comp continuous_projIcc).intervalIntegrable a b
  let L : C(unitInterval, Y) →ₗ[ℝ] C(unitInterval, Y) := {
    toFun U := ⟨fun t => ∫ s in 0..(t : ℝ), U (π s),
      (intervalIntegral.continuous_primitive (hint U) 0).comp continuous_subtype_val⟩
    map_add' U W' := ContinuousMap.ext fun t => intervalIntegral.integral_add
      (hint U 0 (t : ℝ)) (hint W' 0 (t : ℝ))
    map_smul' r U := ContinuousMap.ext fun t => by
      change (∫ s in 0..(t : ℝ), r • U (π s)) = r • ∫ s in 0..(t : ℝ), U (π s)
      rw [intervalIntegral.integral_smul] }
  refine L.mkContinuous 1 fun U => ?_
  rw [one_mul]
  refine (ContinuousMap.norm_le (L U) (norm_nonneg U)).2 fun t => ?_
  change ‖∫ s in 0..(t : ℝ), U (π s)‖ ≤ ‖U‖
  calc
    _ ≤ ‖U‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => U.norm_coe_le_norm (π s)
    _ ≤ ‖U‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg U) t.property.2


def valve : (Y →L[ℝ] Y) →L[ℝ] (Y →L[ℝ] Y):= ContinuousLinearMap.id _ _
private lemma payInv {Z E : Type*}[NormedAddCommGroup Z][NormedSpace ℝ Z][NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] [CompleteSpace Y] (L:Y→L[ℝ]Z)(g:Y)(P:Z→E)(hp:AnalyticAt ℝ P (L g))(n:ℕ) : ∃ t:ℝ,0≤t ∧ ∀ {X: Type}[NormedAddCommGroup X][NormedSpace ℝ X] (F':X→L[ℝ]Y→L[ℝ]Y)(A:X→Y),(∀ x,A x=g+F' x (A x))→ ‖iteratedFDeriv ℝ n (P ∘ L ∘ A) 0‖ ≤ t*‖F'‖^n :=by
    let I : (Y→L[ℝ]Y) → Y := fun T=> Ring.inverse (1 - T) g
    have he : AnalyticAt ℝ I 0:= ((ContinuousLinearMap.apply ℝ Y g).analyticAt _).comp (analyticAt_inverse_one_sub ℝ _)
    have hv : I 0=g:=by unfold I; rw [sub_zero,Ring.inverse_one]; rfl
    have hX:AnalyticAt ℝ (P ∘ L ∘ I) 0:=((show AnalyticAt ℝ P (L (I 0)) from hv.symm ▸ hp).comp (L.analyticAt _)).comp he
    refine ⟨_,norm_nonneg (iteratedFDeriv ℝ n (P ∘ L ∘ I) 0), ?_⟩
    intro X _ _ T A h
    have hT:Tendsto T (𝓝 0) (𝓝 0) := by simpa only [map_zero] using T.continuous.tendsto 0
    have hu:P ∘ L ∘ A=ᶠ[𝓝 0] (P ∘ L ∘ I) ∘ T:=by
       filter_upwards [hT.eventually (Metric.ball_mem_nhds 0 one_pos)] with x hx; have hp : IsUnit (1-T x):= isUnit_one_sub_of_norm_lt_one (show ‖T x‖<1 by simpa using hx)
       have hg : (1-T x) (A x) = g := sub_eq_iff_eq_add.mpr (h x)
       refine congr_arg (P ∘ L) (show A x= I (T x) from ?_); unfold I; rw [← hg, ← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hp,one_apply_eq_self]
    rw [(hu.iteratedFDeriv ℝ n).eq_of_nhds, Next.Foundations.jets_linear T (hX.contDiffAt.of_le le_top)]
    -- op norm
    simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ n (P ∘ L ∘ I) 0) (fun _=> T)

private lemma glueInv {Z E : Type*}[NormedAddCommGroup Z][NormedSpace ℝ Z][NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] [CompleteSpace Y] (L:Y→L[ℝ]Z)(g:Y)(P:Z→E)(hp:AnalyticAt ℝ P (L g))(n:ℕ)(T:Y→L[ℝ]Y→L[ℝ]Y) : ∃ t:ℝ,0≤t ∧ ∀ {X: Type}[NormedAddCommGroup X][NormedSpace ℝ X] (V:X→L[ℝ]Y)(w:ℝ),‖V‖≤ w → ∀ A:X→Y,(∀ x,A x=g+T (V x) (A x))→ ‖iteratedFDeriv ℝ n (P ∘ L ∘ A) 0‖ ≤ t*w^n :=by
   obtain ⟨s,hs,h⟩:= payInv L g P hp n
   refine ⟨s*‖T‖^n,by positivity,?_⟩; intro X _ _ V w hw A he
   exact (h (T.comp V) A he).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ((T.opNorm_comp_le V).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg T))) n) hs).trans_eq (by rw [mul_pow,mul_assoc]))
private lemma pricing {Z:Type*}[NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z] (L:R→Z) (hp:AnalyticAt ℝ L 1)(n:ℕ) : ∃ C':ℝ,0≤C' ∧ ∀ {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] (A : X →ₗ[ℝ] ℝ→R)(hA:∀ p,Continuous (A p)) (a:X→ℝ→R)(ht0:∀ p, a p 0=1)(ha:∀ p t, HasDerivAt (a p) (a p t * A p t) t) (w:ℝ)(_ :0 ≤ w), (∀ x:X,∀ t:unitInterval, ‖A x t.val‖ ≤ w*‖x‖)→ ∀ B:Fin n→X, ‖iteratedFDeriv ℝ n (fun z:X=> L (a z 1)) 0 B‖ ≤ C'*w^n*∏ i,‖B i‖:=by
   let T : W→L[ℝ] (W →L[ℝ] W) := ContinuousLinearMap.compL ℝ W W W primitive ∘L (ContinuousLinearMap.mul ℝ W).flip
   let B : W →L[ℝ] R := ContinuousMap.evalCLM ℝ (1:unitInterval)
   obtain ⟨t,ht,hΓ⟩:= glueInv B 1 L hp n T
   refine ⟨t,ht,?_⟩
   intro X _ _ _ A hA a h0 ha w hw he
   let V : X →L[ℝ] W := LinearMap.toContinuousLinearMap {
    toFun x := ⟨fun t => A x t.val, (hA x).comp continuous_subtype_val⟩
    map_add' x y := ContinuousMap.ext fun t => congr_fun (A.map_add x y) (t : ℝ)
    map_smul' r x := ContinuousMap.ext fun t => congr_fun (A.map_smul r x) (t : ℝ) }
   let ψ:= T.comp V

   have hc(x:X): Continuous (a x):= continuous_iff_continuousAt.2 fun t=> (ha x t).continuousAt
   let v(x:X) : W:= ⟨fun i=> a x i.val,(hc x).comp continuous_subtype_val⟩
   let π:=projIcc (0:ℝ) 1 zero_le_one
   have hv(x:X):v x= 1+ ψ x (v x):=by
      ext t'; let y:= (t':ℝ)
      change a x y=1+(∫ s in 0..y, a x (π s).val * A x (π s).val)
      rw [intervalIntegral.integral_congr (show EqOn (fun s=> a x (π s).val * A x (π s).val) (fun s=> a x s * A x s) (uIcc 0 y) from fun s hs=>by
        rw [uIcc_of_le t'.property.1] at hs; change a x _ * _= _; rw [show (π s).val=s by unfold π; rw [projIcc_of_mem _ (show s ∈ unitInterval from ⟨hs.1,hs.2.trans t'.property.2⟩)]]), intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>ha x s) (((hc x).mul (hA x)).intervalIntegrable _ _), h0]; abel
   intro D
   exact ((iteratedFDeriv ℝ n (L ∘ B ∘ v) 0).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hΓ V w (ContinuousLinearMap.opNorm_le_bound _ hw (fun i=>(ContinuousMap.norm_le (V i) (mul_nonneg hw (norm_nonneg _))).2 (he i))) v hv) (prod_nonneg fun i _=> norm_nonneg _))
end General
variable (T:Taper)(d:ℕ)(c:Side)(p:Edge Cover)
local notation "M"=> su.Mat
/-- Pay uniform from duration-1. -/
abbrev Kline (J:Ln d)(s:ℝ):=T.connection c d (expand _ J) 1 p s
lemma continuousK (J:Ln d):Continuous (Kline T d c p J):=by
   apply ((Taper.smooth T).continuous.comp (show Continuous (fun t:ℝ=> (c.val:ℝ)⁻¹ • (vector p.1 + t • basis p.2)) from by fun_prop)).smul
   unfold partConnection; simp only [one_pow,potential,one_smul]; exact continuous_finsetSum _ fun j _=>(Tensor.diag_smooth _ 1).continuous.comp (by fun_prop)
lemma position_norm (x: Site c): ‖vector (lift x)‖ ≤ 2 * (pdist x:ℝ):= by
    let y:=vector (lift x); let m:ℝ:=pdist x
    have hh i: ‖y i‖≤ m:=calc ‖(((lift x i):ℤ):ℝ)‖=((lift x i).natAbs:ℝ) := by rw [← norm_natAbs,Real.norm_natCast]
                               _≤ m := by unfold m; exact_mod_cast component_le x i
    have hb : ‖y‖^2 ≤ (4:ℝ)*m^2 :=by
       rw [PiLp.norm_sq_eq_of_L2]; refine (Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)).trans_eq ?_
       --
       simp [Axis]
    change ‖y‖ ≤ 2*m; nlinarith [show 0≤m by unfold m; positivity]
lemma rangeT (T:Taper) (J:Ln d)(x : Site c)(a:Axis)(z:unitInterval) : ‖Kline T d c (lift x,a) J z‖ ≤ ↑(d/2-1) * (2*(1+(pdist x:ℝ)))^d * ‖J‖ :=by
   let V:=vector (lift x)+(z:ℝ) • basis a; let w:=2*(1+(pdist x:ℝ)); have hx:1 ≤ w:=by unfold w; linarith [Nat.cast_nonneg (α:=ℝ) (pdist x)]
   have hV: ‖V‖ ≤ w := (norm_add_le ..).trans (by rw [norm_smul,basis_norm,mul_one, Real.norm_of_nonneg z.property.1]; unfold w; linarith [position_norm c x,z.property.2])
   unfold Kline Taper.connection; rw [norm_smul, Real.norm_of_nonneg (T.interval _).1]; apply (mul_le_of_le_one_left (norm_nonneg _) (T.interval _).2).trans; unfold partConnection; simp only [one_pow,potential,one_smul]; apply (norm_sum_le ..).trans
   conv_rhs=> rw [mul_assoc]
   change ∑ i∈_, ‖(expand _ J i).value a V‖ ≤ ((d/2-1:ℕ):ℝ)*(w^d*‖J‖)
   trans ∑ i∈Finset.range (d/2-1), w^d*‖J‖; swap; · simp
   apply Finset.sum_le_sum; intro i hi; let j:= (⟨i,Finset.mem_range.mp hi⟩:Fin (d/2-1)); let k:= (J j).val a; have ht:‖k‖ ≤ ‖J‖:= ((norm_le_pi_norm (J j).val a).trans (norm_le_pi_norm J j)); unfold expand; rw [dif_pos (Finset.mem_range.mp hi)]; change ‖Tensor.diagonal k V‖ ≤ _
   apply (k.le_opNorm (fun _=> V)).trans; simp only [Finset.prod_const,card_univ,Fintype.card_fin]; rw [mul_comm (w^_)]; apply mul_le_mul ht _ (pow_nonneg (norm_nonneg _) _) (norm_nonneg _); exact (pow_le_pow_left₀ (norm_nonneg _) hV _).trans (pow_le_pow_right₀ hx (by have h:= Finset.mem_range.mp hi; omega))
private lemma boundL {X Z: Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Z][NormedSpace ℝ Z](p:X→ₗ[ℝ]Z)[FiniteDimensional ℝ X]: ∃ L:ℝ,0≤L∧∀ i,‖p i‖≤L*‖i‖:= ⟨_,norm_nonneg p.toContinuousLinearMap,fun i=> p.toContinuousLinearMap.le_opNorm _⟩
lemma charter (d n:ℕ):∃ C:ℝ,0≤C ∧ ∀ (H:TaperHol)(c: Side)(p:Edge (Site c))(b: Cover)(v:Fin n→Ln d), ‖iteratedFDeriv ℝ n (fun x: Ln d=> lamp (c:=c) (d:=d) H b x p) 0 v‖ ≤ C*(1+(separation p.1 (wrap c b):ℝ))^(d*n)*∏ i,‖v i‖ :=by
   obtain ⟨t,ht,hC⟩:= pricing (R:=su.Mat) su.plog su.plog_diff.analyticAt n
   obtain ⟨Z,hZ,hV⟩:=boundL su.colorMat; let L:=su.colorMat.toContinuousLinearMap; let A:ℝ:=Z*((d/2-1:ℕ):ℝ)*2^d; have hA:0≤A:=by unfold A; positivity
   refine ⟨t*A^n,by positivity,?_⟩; intro H c e b v; let x:=e.1-wrap c b; let p:Edge Cover:=(offset b e.1,e.2)
   let K:Ln d →ₗ[ℝ] ℝ→su.Mat:= { toFun:=fun J s=>L (Kline H.T d c p J s),map_add':=?_,map_smul':=?_ }; rotate_left
   · intro J K; funext t
     change L _=L _+ L _; rw [← map_add]; apply congr_arg; unfold Kline Taper.connection; rw [← smul_add]; apply congr_arg; simp only [partConnection,potential,one_smul,one_pow,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; simp only [Labels.Taylor.value, Tensor.diagonal,expand,dif_pos (Finset.mem_range.mp hi)]; rfl
   · intro r J; funext t
     change L _= r • L _; rw [← map_smul]; apply congr_arg; unfold Kline Taper.connection; rw [smul_comm r]; apply congr_arg; simp only [partConnection,potential,one_smul,one_pow,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; simp only [Labels.Taylor.value, Tensor.diagonal,expand,dif_pos (Finset.mem_range.mp hi)]; rfl
   let w:=1+(pdist x:ℝ); have hW:0≤w:=by unfold w; positivity
   have HE(z:Ln d)(s:unitInterval): ‖K z s.val‖≤A*w^d *‖z‖:=(hV _).trans ((mul_le_mul_of_nonneg_left (rangeT _ _ _ z x e.2 s) hZ).trans_eq (by unfold A w; rw [mul_pow]; ring))
   have he:= hC K (fun J=> L.continuous.comp (continuousK _ _ _ p J)) (fun v s=>su.mat (H.flow c d (expand _ v) 1 p s)) (fun v=> by rw [(H.solves ..).1,su.mat_one]) (fun v t=>(H.solves ..).2 t) _ (show 0 ≤ A*w^d by positivity) HE v
   exact he.trans_eq (by rw [mul_pow]; unfold separation w x; rw [pow_mul]; rw [mul_assoc t (A^n) _]; rfl)
lemma lampFee (d n : ℕ) : ∃ C:ℝ,0 ≤ C ∧ ∀ (H:TaperHol)(c:Side)(b : Cover)(e:Edge (Site c))(A:Fin n→Ln d), ‖iteratedFDeriv ℝ n (lamp (d:=d) H b) 0 A e‖ ≤ C*(1+(separation e.1 (wrap c b):ℝ))^(d*n)*∏ i,‖A i‖ :=by
    obtain ⟨C,h,H⟩:=charter d n; refine ⟨C,h,fun X c b e A=>?_⟩
    let p : Directions su c→L[ℝ]su.Color:= ContinuousLinearMap.proj e; let f:= p ∘ lamp (d:=d) (c:=c) X b
    rw [show iteratedFDeriv ℝ n (lamp (d:=d) X b (c:=c)) 0 A e=iteratedFDeriv ℝ n f 0 A from (by unfold f; rw [p.iteratedFDeriv_comp_left (fluent X b d c).contDiffAt le_top]; rfl)]; exact H X c e b A
end Verse
end Beacon
end YM.Massive.Poised
