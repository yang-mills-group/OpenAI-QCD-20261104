import YM.Massive.Filament.Algebra
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Off-axis coefficient support proof. Use only values on real line for preservation.

E.g. a slope limit on product of capsule field × Λ. Don't need joint continuity even on Real.Spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Filament
open Function Filter Complex Metric Finset MeasureTheory
open scoped BigOperators Topology ContDiff Classical
variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
variable [CompleteSpace E]
variable (n:ℕ) {p:ℂ→E}{X':ℝ→ℂ}{b:ℝ}{u:E}
-- Difference quotient along the actual real interval. `Shutter` includes products don't care about measure.
structure Shutter (P:(ι→E)→Prop) : Prop where
 sub {f g}: P f → P g → P (fun i=> f i-g i)
 real (t:ℝ) {f} : P f → P (fun i=> t • f i)
 seq (Q:ℕ→ι→E)(f:ι→E): (∀ᶠ i in atTop, P (Q i)) → (∀ i,Tendsto (fun n=> Q n i) atTop (𝓝 (f i))) → P f
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
lemma Shutter.inter {P Q : (ι→E)→Prop}(h:Shutter P)(hf:Shutter Q): Shutter (fun f=>P f ∧ Q f):=
    ⟨fun hp hg=> ⟨h.sub hp.1 hg.1,hf.sub hp.2 hg.2⟩,fun t {_} hp=>⟨h.real t hp.1,hf.real t hp.2⟩,fun f g hg ht=>⟨h.seq f g (hg.mono fun _=> And.left) ht,hf.seq f g (hg.mono fun _=> And.right) ht⟩⟩
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
lemma Shutter.all {P:X→(ι→E)→Prop}(hp:∀ x,Shutter (P x)): Shutter (fun f=>∀ x,P x f):=⟨fun h h' x=> (hp x).sub (h x) (h' x), fun t {_} h x=> (hp x).real t (h x),fun f g hg ht x=> (hp x).seq f g (hg.mono fun _ h=>h x) ht⟩
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
lemma Shutter.hasLimit {P:(ι→E)→Prop}{L:Filter F}[IsCountablyGenerated L][NeBot L] (hp:Shutter P)(Q:F→ι→E)(f:ι→E)(he:∀ᶠ i in L,P (Q i))(ht:∀ i,Tendsto (fun n=>Q n i) L (𝓝 (f i))):P f:=by obtain ⟨s,hs⟩:=L.exists_seq_tendsto; exact hp.seq (Q∘s) f (hs.eventually he) fun i=> (ht i).comp hs
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
lemma Shutter.meas [MeasurableSpace ι] [SecondCountableTopology E] [MeasurableSpace E][BorelSpace E]: Shutter (Measurable (α:=ι) (β:=E)):=by
    refine ⟨fun hf hg=>hf.sub hg,fun t {_} hf=>measurable_const.smul hf,fun f g hP h=>?_⟩ -- topology assumptions
    obtain ⟨N,hn⟩:= eventually_atTop.mp hP
    refine measurable_of_tendsto_metrizable (fun i:ℕ=>hn (N+i) (by omega)) (tendsto_pi_nhds.mpr (fun i=> (h i).comp ?_)); exact strictMono_nat_of_lt_succ (by intro n; change N+n<N+(n+1); omega)|>.tendsto_atTop
-- general `fderiv.restrictScalars`. lemma mathlib path .Real.. currently only on ℂ.
omit [CompleteSpace E] in
lemma onReal (h:HasDerivAt p u (b:ℂ)): HasDerivAt (fun x:ℝ=> p (x:ℂ)) u b:=by
   have he : HasDerivAt ((↑):ℝ→ℂ) 1 b := by convert! Complex.ofRealCLM.hasDerivAt (x:=b)
   convert! ((h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt b he) using 1; simp
lemma Shutter.circlet {P:(ι → E)→Prop} {p:ι→ℂ→E}(hp:Shutter P)(h:∀ i,Holo (p i))(he:∀ x:ℝ, ‖x‖<1 → P (fun i=>p i (x:ℂ))): P (fun i=>bead n (p i)):=by
   have hx (n):∀ x:ℝ,‖x‖<1→P (fun i=> iteratedDeriv n (p i) (x:ℂ)):=by
      induction n with
      | zero=> simpa only [iteratedDeriv_zero] using he
      | succ n ih=>
        intro x ht; simp_rw [iteratedDeriv_succ]; let G i (x:ℝ):= iteratedDeriv n (p i) (x:ℂ)
        refine hp.hasLimit (L:=𝓝[≠] x) (fun y i=>(y-x)⁻¹ • (G i y-G i x)) _ ?_ fun i=> ?_
        · exact Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht))) fun y (hy:y∈ball 0 1)=>hp.real _ (hp.sub (ih y (mem_ball_zero_iff.mp hy)) (ih x ht))
        apply (onReal (((h i).iter n).differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ((Complex.norm_real x).trans_lt ht)))).hasDerivAt).tendsto_slope -- slope defin
   have hn:P (fun i=> (n.factorial:ℝ)⁻¹ • iteratedDeriv n (p i) 0):=by
        have ht:= hx n 0 (by simp); rw [Complex.ofReal_zero] at ht; exact hp.real _ ht
   refine Eq.mp (congr_arg P (funext fun i=>show (n.factorial:ℝ)⁻¹ • iteratedDeriv n (p i) 0=bead n (p i) from ?_)) hn
   rw [bead, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]; exact (IsScalarTower.algebraMap_smul ℂ _ _).symm
section
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
lemma Shutter.constant {H:Prop} : Shutter (fun _:ι→E=>H):= ⟨fun h _=>h,fun _ {_} h=>h,fun _ _ h _=> (h.exists).choose_spec⟩
lemma Shutter.byAssume (H:Prop)(P:(ι → E)→Prop)(hp: H→Shutter P): Shutter (fun i=>H→P i):=⟨fun h h' hk=>(hp hk).sub (h hk) (h' hk), fun t {_} h hq=>(hp hq).real t (h hq), fun f g hg ht h=> (hp h).seq f g (hg.mono fun _ hp=>hp h) ht⟩
lemma Shutter.transfer {P Q:(ι→E)→Prop}(h:Shutter P)(he:∀ f,P f↔ Q f): Shutter Q:=((funext (fun f=>propext (he f))):P=Q) ▸ h
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma Shutter.comp (K:ι→X)(P:(ι→E)→Prop)(hp:Shutter P): Shutter (fun f:X→E=> P (f ∘ K)):= ⟨fun h h' => hp.sub h h',fun t {_} h=> hp.real t h, fun _ _ hg ht=>hp.seq _ _ hg (fun i=>ht (K i))⟩
lemma Shutter.fx (P:E→L[ℝ]F)(Q:E→L[ℝ]F)(i k:ι): Shutter (fun f=> P (f i) = Q (f k)):=⟨fun hp hg=>by rw [map_sub,map_sub,hp,hg],fun t {_} hp=>by rw [map_smul,map_smul,hp],fun f g hg ht=> tendsto_nhds_unique (((P.continuous.tendsto _).comp (ht i)).congr' hg) ((Q.continuous.tendsto _).comp (ht k))⟩
lemma Shutter.flat (i:ι): Shutter (fun f:ι→E=> f i=0):= (fx (ContinuousLinearMap.id ℝ E) 0 i i)
lemma Shutter.eq (i k:ι): Shutter (fun f:ι→E=>f i=f k):=fx (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) i k
lemma Shutter.land (D:Submodule ℝ E)(hp:IsClosed (D:Set E))(x:ι): Shutter (fun f=> f x ∈ D):= ⟨fun h h'=> D.sub_mem h h', fun t {_} h=> D.smul_mem t h,fun _ _ hg ht=> hp.mem_of_tendsto (ht x) hg⟩
end
end YM.Massive.Filament
#print axioms YM.Massive.Filament.Shutter.circlet
