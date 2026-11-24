import YM.MassiveQCD.Evolution.SnapK
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
/-! # Identity portions from the real interval
 Membership, Borel, analytic coefficient identities and turns (including anti or just real-linear).
 Need turn permutations may depend on every λ; adapt them here via countability, not pinning analyticity of perm supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Analysis.Shelf
open Function Filter Topology Finset MeasureTheory Complex Set Metric
open scoped BigOperators Classical
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A][NormedSpace ℂ A][IsScalarTower ℝ ℂ A][CompleteSpace A]
  [NormedAddCommGroup B][NormedSpace ℝ B][NormedSpace ℂ B][IsScalarTower ℝ ℂ B] [CompleteSpace B] {ι ξ:Type*}
variable {f:ℂ→A} {g:ℂ→B} {z: ℂ} {x:ℝ}
lemma ace : IsOpen {x:ℝ| |x| <1}:= isOpen_lt continuous_abs continuous_const
local notation "Q"=>ball (0:ℂ) 1
lemma swim (x:ℝ): ↑x∈ (Q:Set ℂ) ↔ |x|<1:=by simp only [mem_ball_zero_iff, norm_real,Real.norm_eq_abs]
omit [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A] in
private lemma sprouts (n:ℕ)(h:Roof f): Roof (iteratedDeriv n f):=by
   induction n with
   | zero=> simpa using h
   | succ n ih=> rw [iteratedDeriv_succ]; exact fun i hi=> (ih i hi).deriv
lemma weir (n:ℕ)(h:Roof f)(hx:|x|<1) : HasDerivAt (fun x:ℝ=>iteratedDeriv n f (x:ℂ)) (iteratedDeriv (n+1) f (x:ℂ)) x:=by
    let f':= iteratedDeriv n f; let v:=deriv f' (x:ℂ)
    have hp: HasFDerivAt f' (((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ) (x:ℂ):= ((sprouts n h (x:ℂ) ((swim x).mpr hx)).differentiableAt.hasDerivAt.hasFDerivAt).restrictScalars ℝ
    rw [iteratedDeriv_succ]; convert hp.comp_hasDerivAt x (ofRealCLM.hasDerivAt) using 1
    · rfl
    simp [v,f']
omit [CompleteSpace A] in
private lemma ofReal_r (r:ℝ)(x:A) : (r:ℂ) • x = r • x := IsScalarTower.algebraMap_smul ℂ r x -- order?
lemma confirms (n:ℕ)(h:Roof f)(hp:Roof g)(L:A→L[ℝ] B)(hv:∀ x:ℝ,|x|<1→L (f x)=g x) : L (ampK f n)=ampK g n:=by
   have hP n (x:ℝ)(hx:|x|<1): L (iteratedDeriv n f (x:ℂ))=iteratedDeriv n g (x:ℂ):=by
       induction n generalizing x with
       | zero=> simpa using hv x hx
       | succ n ih=> refine (((L.hasFDerivAt.comp_hasDerivAt _ (weir n h hx)).congr_of_eventuallyEq (f₁:=fun x:ℝ=> iteratedDeriv n g (x:ℂ)) ?_).unique (weir n hp hx)); exact (show ∀ᶠ z:ℝ in 𝓝 x, |z| <1 from ace.mem_nhds hx).mono (fun _ hg=> (ih _ hg).symm)
   unfold ampK; have hF: (n.factorial:ℂ)⁻¹= ((n.factorial:ℝ)⁻¹:ℝ):=by push_cast; rfl
   rw [hF, ofReal_r, ofReal_r,map_smul]; apply congr_arg; simpa using hP n 0 (by norm_num)
variable [MeasurableSpace ξ] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
-- NO continuity in the masks; pointwise real reads only
lemma stockB (f:ξ→ℂ→A)(n:ℕ)(h:∀ i,Roof (f i))(he:∀ x:ℝ,|x|<1→Measurable (fun i=> f i (x:ℂ))) : Measurable (fun i=>ampK (f i) n):=by
    let K n (x:ℝ) i:= iteratedDeriv n (f i) (x:ℂ)
    have H n (x:ℝ) (hx:|x|<1) : Measurable (K n x):=by
        induction n generalizing x with
        | zero=> simpa [K] using he x hx
        | succ n ih=>
           let F (y:ℝ)(i:ξ):= if |x+y|<1 then y⁻¹ • (K n (x+y) i-K n x i) else 0
           refine measurable_of_tendsto_metrizable' (f:=F) (𝓝[>] 0) (fun i=>?_) (tendsto_pi_nhds.mpr ?_)
           · unfold F; split; next ht=> exact measurable_const.smul ((ih _ ht).sub (ih x hx))
             next h'=> exact measurable_const
           intro i; let G(y:ℝ):= K n y i
           have hf: HasDerivAt G (K (n+1) x i) x:=weir n (h i) hx
           apply hf.tendsto_slope_zero_right.congr'; have hA : ∀ᶠ y:ℝ in 𝓝 0, |x+y|<1:= ((continuous_const.add continuous_id).tendsto (0:ℝ)).eventually (ace.mem_nhds (x:=x+0) (show |x+0|<1 from by rw [add_zero]; exact hx)); exact (hA.filter_mono nhdsWithin_le_nhds).mono fun _ h=> (if_pos h).symm
    unfold ampK; refine measurable_const.smul ?_; have hh:= H n 0 (by norm_num); simpa [K] using hh
-- also applies closed membership, no Hahn choice.
omit [SecondCountableTopology A] [MeasurableSpace A][BorelSpace A] in
lemma closed_tier (n:ℕ)(K:Submodule ℝ A)(hc:IsClosed (K:Set A))(h:Roof f)(he:∀ x:ℝ,|x|<1→ f x∈ K) : ampK f n∈K:=by
   have H n (x:ℝ) (hx:|x|<1): iteratedDeriv n f (x:ℂ) ∈ K:=by
     induction n generalizing x with
     | zero=> simpa using he x hx
     | succ n ih=>
       apply hc.mem_of_tendsto (weir n h hx |>.tendsto_slope_zero_right)
       have hA : ∀ᶠ y:ℝ in 𝓝 0, |x+y|<1:= ((continuous_const.add continuous_id).tendsto (0:ℝ)).eventually (ace.mem_nhds (x:=x+0) (show |x+0|<1 from by rw [add_zero]; exact hx)); exact (hA.filter_mono nhdsWithin_le_nhds).mono fun y hy=>K.smul_mem _ (K.sub_mem (ih _ hy) (ih _ hx))
   unfold ampK; have hF: (n.factorial:ℂ)⁻¹= ((n.factorial:ℝ)⁻¹:ℝ):=by push_cast; rfl
   rw [hF, ofReal_r]; exact K.smul_mem _ (by simpa using H n 0 (by norm_num))

-- Simultaneous: can combine (i,j) marker pairs with any countable category of labels,
-- `ξ` large uncountable poses, select a single generic real marker AFTER all volume decisions.
-- Not carrying equality on all-parameter outside disk. Compact shell is within OPEN U here.
omit [SecondCountableTopology A] [MeasurableSpace A][BorelSpace A][NormedSpace ℝ A][IsScalarTower ℝ ℂ A][MeasurableSpace ξ][CompleteSpace A] in
theorem generic [Countable ι] (f g:ι→ξ→ℂ→A)(hf:∀ i j,Roof (f i j))(hg:∀ i j,Roof (g i j)): ∃ x:ℝ, |x|<1 ∧ ∀ i:ι,(∀ j:ξ,f i j x=g i j x) → ∀ j:ξ,EqOn (f i j) (g i j) (ball 0 1):=by
   let P i:=∀ j,EqOn (f i j) (g i j) (ball 0 1)
   let F:=Icc (0:ℝ) (1/2); let e:ℝ→ℂ:= (↑); let T:=e '' F
   have hF: IsCompact T:=isCompact_Icc.image continuous_ofReal
   let K i:= if P i then ∅ else T∩{x:ℂ|∀ j,f i j x=g i j x}
   have hh (i) : (K i).Countable:=by
       unfold K; split; · exact countable_empty
       next he=>
          have hv:¬∀ j,EqOn (f i j) (g i j) (ball 0 1):=he
          obtain ⟨j,hj⟩:= not_forall.mp hv
          have ht:T ⊆ Q:=by rintro _ ⟨y,h,rfl⟩; exact (swim y).2 (lt_of_le_of_lt (abs_le.mpr ⟨by linarith only [h.1],h.2⟩) (by norm_num))
          have hz:= Or.resolve_left ((hf i j).eqOn_or_eventually_ne_of_preconnected (hg i j) ((convex_ball (0:ℂ) 1).isPreconnected)) hj
          let M:={z:ℂ|f i j z≠g i j z}
          have hK:= hF.finite_sdiff_of_mem_codiscreteWithin (s:=M) (hz.filter_mono (codiscreteWithin_mono ht)); refine Set.Countable.mono ?_ hK.countable; intro z hz
          exact  ⟨hz.1,fun h=>h (hz.2 j)⟩
   have hx := Set.countable_iUnion hh; have hy:=hx.preimage Complex.ofReal_injective -- exact
   have hz:(F \ e ⁻¹' ⋃ i,K i).Nonempty:=by
      have hμ: volume (e ⁻¹' ⋃ i,K i)=0:= hy.measure_zero _
      by_contra ht; rw [Set.not_nonempty_iff_eq_empty] at ht; have h:volume F ≤ 0:=(measure_mono (sdiff_eq_empty.mp ht)).trans_eq hμ; have h':0<volume F:=by unfold F; rw [Real.volume_Icc]; positivity
      exact not_lt_of_ge h h'
   obtain ⟨x,hx,hp⟩:= Set.nonempty_def.mp hz
   · refine ⟨x, lt_of_le_of_lt (le_of_eq (abs_of_nonneg hx.1)) (lt_of_le_of_lt hx.2 (by norm_num)),fun i hv=>?_⟩
     change P i; by_contra h; apply hp (show e x∈⋃ i,K i from mem_iUnion.mpr ⟨i,(show e x∈K i from ?_)⟩); unfold K; rw [if_neg h]; exact ⟨mem_image_of_mem _ hx,hv⟩
end YM.MassiveQCD.Analysis.Shelf
#print axioms YM.MassiveQCD.Analysis.Shelf.generic
