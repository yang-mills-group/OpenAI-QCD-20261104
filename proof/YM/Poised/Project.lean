import YM.Poised.Display
import YM.Massive.Papyrus.Avel
import YM.QCD.Grass.Time
/-!
# Actual tapered projection

Unmarked horizon all real independent variables. Reuse `Next.FOUNDATIONS.Readout` proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus
variable {c : Side} {d : ℕ}
namespace Beacon
variable (H:TaperHol)(b : Cover)
local notation "F" => Lat.Fields c 6
local notation "G" => SpinPol d
local notation "N" => Pairs (SpinMode d)
open TensorProduct
/-- no unwrapping hypothesis or h derivatives beyond inclusive cap -/
def moment (J:Labels.Jet su) (x: Grid c → F) (h:ℝ):G:= adapter (glow H.T b h) (glow H.T b h) (x (current H b d J h))
def ActionTest (x: Grid c → F) (u:Pol d) := ∀ J:Labels.Jet su, Agrees (moment H b J x) (desired u J)
-- groom factor for Spin.Let
lemma sky_etch (t:ℝ)(i: Modes c 6)(j:SpinMode d): glow H.T b t i j=glow H.T b 1 i j*(t:ℂ)^ spinWeight j.1.1:=by
    unfold glow; dsimp only [Matrix.of_apply]; split
    next _ => simp [profile]; ring -- syntax
    next _ => rw [zero_mul]
lemma spin_step (t:ℝ): glow (c:=c) (d:=d) H.T b 1 * scaled t=glow H.T b t:=by ext i j; rw [scaled,Matrix.mul_diagonal, sky_etch H b t i j] -- check lemma
abbrev core (x:Grid c→F)(d:ℕ) (s:Ln d): SpinPol d:= adapter (glow H.T b 1) (glow H.T b 1) (x (views H b d s))
lemma splitD (J:Labels.Jet su)(x : Grid c→F)(h:ℝ): moment (d:=d) H b J x h= endor h (core H b x d (trunk (d/2) (scaleJet J (h^2)))):=by
    unfold moment endor core; rw [adapt_together,spin_step]
lemma core_smooth (x : Grid c→F)(hx:ContDiffAt ℝ (d : WithTop ℕ∞) (x∘increment 1) 0): ContDiffAt ℝ (d:WithTop ℕ∞) (core H b x d) 0:=by
    have hh : ContDiffAt ℝ (d:WithTop ℕ∞) (x ∘ views H b d) 0:=by
       apply ((show ContDiffAt ℝ d (x∘increment 1) (lamp H b (0:Ln d)) from (at_dark H b).symm ▸ hx).comp _ ((fluent H b d c).contDiffAt.of_le le_top)).congr_of_eventuallyEq
       filter_upwards [at_east (c:=c) H b (d:=d)] with y hy; exact congr_arg x hy
    let L:= (adapter (glow (c:=c) (d:=d) H.T b 1) (glow H.T b 1)).toLinearMap.restrictScalars ℝ; exact L.toContinuousLinearMap.contDiff.contDiffAt.comp _ hh
-- components use original based readout.
private theorem slot_polynomial {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (X : Labels.Jet su → E) (V : ι → E)
    (L : ι → Labels.Key su) (r : Labels.Jet su → ι → ℝ) (hr : ∀ J i, (r J i : ℂ) = Labels.coord J (L i))
    (ht : ∀ J, X J = ∑ i, r J i • V i) (m : ℕ) (A : Tensor.T E ℂ m) :
    ∃ p : UV.GPol, ∀ J : Labels.Jet su, Labels.read J p = Tensor.diagonal A (X J) := by
  classical
  induction m with
  | zero =>
    refine ⟨MvPolynomial.C (Tensor.diagonal A 0), fun J => ?_⟩
    simp only [Labels.read, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    exact congr_arg A (Subsingleton.elim ..)
  | succ m ih =>
    choose p hp using fun i : ι => ih (A.curryLeft (V i))
    refine ⟨∑ i, MvPolynomial.X (L i) * p i, fun J => ?_⟩
    have he (x : E) : Tensor.diagonal A x = Tensor.diagonal (A.curryLeft x) x := by
      apply congr_arg A
      ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hv : A.curryLeft (X J) = ∑ i, r J i • A.curryLeft (V i) := by rw [ht, map_sum]; simp
    rw [he, hv, Tensor.diagonal, _root_.map_sum, _root_.sum_apply] -- ambiguity
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, hp, Labels.read, MvPolynomial.aeval_X, smul_apply, Complex.real_smul, hr]
    rfl
private theorem snap_polynomial (m n:ℕ) (A : Tensor.T (Snap su m) ℂ n) :
    ∃ p : UV.GPol, ∀ J : Labels.Jet su, Labels.read J p = Tensor.diagonal A (trunk m J) := by
  classical
  let I := (i : Fin (m-1)) × Fin (Labels.dim su i.val)
  let V (i : I) : Snap su m := Pi.single i.1 (Labels.axes su i.1.val i.2)
  let r (J : Labels.Jet su) (k : I) := ((Labels.axes su k.1.val).repr (J k.1.val)) k.2
  refine slot_polynomial (trunk m) V (fun i => ⟨i.1.val,i.2⟩) r (fun _ _ => rfl) ?_ n A
  intro J
  symm
  funext j
  rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [Finset.sum_apply, Pi.smul_apply, V, Pi.single_eq_same]
    exact (Labels.axes su j.val).sum_repr (J j.val)
  · intro i _ hij; simp [Finset.sum_apply, V, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp
abbrev tapped (i:Finset N)(x:Grid c→F): Ln d → ℂ := coef i ∘ core H b x d
lemma stroke (x : Grid c→F) (hx:ContDiffAt ℝ (d:WithTop ℕ∞) (x∘increment 1) 0)(i:Finset N) : ∃ p : GPol, Response d (tapped H b i x) (fun z : Ln d=> Labels.read (expand _ z) p) 0 ∧ ∀ J:Labels.Jet su, Labels.read J p= Labels.read (expand _ (trunk (d/2) J)) p :=by
   let f:= tapped H b i x
   choose p hp using fun n : ℕ=> snap_polynomial _ _ (Tensor.coeff f n 0)
   let P:=∑ i∈Finset.range (d+1),p i
   have he(J: Labels.Jet su): Labels.read J P= Work.G05.blockTaylor d f (trunk (d/2) J):=by
       unfold P Work.G05.blockTaylor; rw [_root_.map_sum,Finset.sum_apply]; exact Finset.sum_congr rfl fun z _=>hp z J
   let L:= (coef i).restrictScalars ℝ
   have hF:ContDiffAt ℝ d f 0:= L.toContinuousLinearMap.contDiff.contDiffAt.comp _ (core_smooth H b x hx)
   refine ⟨P,?_,fun J=>?_⟩; swap; · rw [he J,he,trunks]
   rw [show (fun z=> Labels.read (expand (d/2) z) P)=Work.G05.blockTaylor d f from funext fun z=>by rw [he,trunks]]; exact ⟨hF,(Work.G05.blockTaylor_contDiff ..).contDiffAt,fun i hi=> (Work.G05.blockTaylor_jets hF _ hi).symm⟩
abbrev scaledD(d:ℕ)(J:Labels.Jet su)(h:ℝ):=trunk (d/2) (scaleJet J (h^2))
lemma scaled_zero (d:ℕ)(J:Labels.Jet su): scaledD d J 0=0:=by funext i; simp [scaledD,trunk,scaleJet]
lemma scaled_smooth (d:ℕ)(J:Labels.Jet su): ContDiffAt ℝ (d: ℕ∞) (scaledD d J) 0 := by
   apply contDiffAt_pi.mpr; intro i; change ContDiffAt _ _ (fun h:ℝ=> (h^2)^(i.val+2) • J i.val) _; exact glowE (i.val+2) (J i.val)
 where glowE {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](i:ℕ)(x:E): ContDiffAt ℝ (d:ℕ∞) (fun h:ℝ=> (h^2)^i • x) 0:= ((contDiffAt_id.pow 2).pow _).smul contDiffAt_const
private lemma observe_t (d:ℕ)(J:Labels.Jet su)(x:GPol)(y:SpinPol d)(t:ℝ): observation d J t (x⊗ₜ[ℂ] y)=Labels.read (scaleJet J (t^2)) x • endor t y:=by rw [observation,LinearMap.comp_apply,ready_t,map_smul]; rfl
lemma obtainsD (x : Grid c→F) (hx:ContDiffAt ℝ (d:WithTop ℕ∞) (x∘increment 1) 0) : ∃ u:Pol d, u∈ cap d ∧ ActionTest H b x u:=by
    choose p hp hh using stroke H b x hx
    let P:Pol d:= ∑ i : Finset N,p i⊗ₜ[ℂ] mono i
    refine ⟨drips d P,drips_in _, fun J=> ?_⟩
    have hu : moment (d:=d) H b J x=fun h:ℝ=> ∑ i:Finset N,tapped H b i x (scaledD d J h) • ((h:ℂ)^sky i • mono i):=by
       funext t; rw [splitD]
       conv_lhs=>arg 2; rw [← write (core H b x d _) ]
       simp_rw [map_sum,map_smul,pieces]; rfl
    have he(i:Finset N) : Response d (fun h:ℝ=>tapped H b i x (scaledD d J h) • ((h:ℂ)^sky i • mono i)) (fun h=>observation d J h (p i⊗ₜ[ℂ] mono i)) 0:=by
       have hQ:Response d (fun h:ℝ=>tapped H b i x (scaledD d J h)) (fun h=>Labels.read (expand _ (scaledD d J h)) (p i)) 0:= (Response.refl (scaled_smooth d J)).transit ((scaled_zero d J).symm ▸ hp i)
       simp_rw [observe_t,pieces, hh i (scaleJet J (_^2))]; exact hQ.smuls (Response.refl (show ContDiffAt ℝ _ (fun t:ℝ=> (t:ℂ)^sky i • mono i) _ from (Complex.ofRealCLM.contDiff.contDiffAt.pow _).smul contDiffAt_const))
    have hC : Agrees (moment (d:=d) H b J x) (fun t=>observation d J t P):=by rw [hu]; simp_rw [P,map_sum]; exact (Response.series _ _ _ _ (fun i _=> he i)).smooth_compare
    rw [← funext (observe J (drips d P))]; exact ⟨hC.1,(painted _ _ _).contDiffAt,fun k hk=> by rw [hC.2.2 k hk, order_test,order_test,drips_geom k d P hk]⟩
end Beacon
end YM.Massive.Poised
