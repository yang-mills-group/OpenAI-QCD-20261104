import YM.Elms.Graded
import YM.Work.A07
/-! # Invariance by Haar, finite-dimensional circles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans
open MeasureTheory Filter
open scoped Topology BigOperators TensorProduct Pointwise Classical Matrix Matrix.Norms.Frobenius Stamp -- instance scope
variable {d:ℕ} {u v:su.El}
namespace LoomC
noncomputable local instance M(d:ℕ):NormedSpace ℝ (Mini d):=.restrictScalars ℝ ℂ _ -- perhaps S tower ext via instances
lemma viaTests {E V W I:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ E] (f:I→ E→ₗ[ℝ] V)(hf:∀ u, (∀ j,f j u=0)→ u=0) {l:Filter W}{Y:W→ E}{x:E}(ht: ∀ j:I,Tendsto (fun w=>f j (Y w)) l (𝓝 (f j x))): Tendsto Y l (𝓝 x):=by
      obtain ⟨s,hs⟩:= Work.A07.finite_rows f hf
      let H:= LinearMap.pi fun i:s => f i.val; let g:=H.toContinuousLinearMap
      -- homeo onto compact.Var via antiLip
      have hp:Tendsto (fun w=>g (Y w)) l (𝓝 (g x)):=tendsto_pi_nhds.mpr (fun i=> ht i.val);
      have hi :Topology.IsEmbedding g:= by
          obtain ⟨_,_,ha⟩:= LinearMap.injective_iff_antilipschitz H |>.1 hs; exact ha.isEmbedding H.continuous_of_finiteDimensional
      exact hi.isInducing.tendsto_nhds_iff.mpr hp
lemma tint_heights {W:Type*}{l:Filter W}{Y:W→Mini d}{p:Mini d} (h:∀ J:Labels.Jet su,Tendsto (fun w=>Poised.Display.ready d J (Y w).val) l (𝓝 (ready d J p.val))) : Tendsto Y l (𝓝 p):=by
      letI : FiniteDimensional ℝ (Mini d) := Module.Finite.trans ℂ _; refine viaTests (fun J:Labels.Jet su=>((ready d J).comp (cap d).subtype).restrictScalars ℝ) (fun u h=>Subtype.ext (Display.distinct _ (0:Pol _) fun J=>(h J).trans (map_zero _).symm)) h
noncomputable def tint (u:su.El)(d:ℕ): Mini d→ₗ[ℂ] Mini d:= ((colorAct u).comp (cap d).subtype).codRestrict _ fun x=>radiant_cap u x.property
lemma tin_one (p:Pol d) : colorAct 1 p=p:=by
    apply Display.distinct; intro J; rw [visual]; have h:Labels.colored 1 J=J:=by funext i; apply Labels.Taylor.value_ext; funext a x; exact su.adjoint_one _
    rw [h]; unfold luminous
    have he:colorTable (d:=d) 1=1:=by simp_rw [Lining.eye_color,show Lat.colour 1=1 from su.mat_one, touch_one,Lining.spar_refl]
    rw [he,star_one,Matrix.transpose_one]; exact adapt_one _
lemma eye_spin (u v: su.El) : colorTable (d:=d) u * colorTable v= colorTable (u*v):=by
    open Lining in simp_rw [eye_color,spar_spar,touch_mul,colour_mul]; rfl -- expand
lemma tin_mul (u v:su.El) (p:Pol d): colorAct u (colorAct v p)=colorAct (v*u) p:=by
    apply Display.distinct; intro J; rw [visual,visual,visual]; have hv:Labels.colored v (Labels.colored u J)=Labels.colored (v*u) J:=by funext i; apply Labels.Taylor.value_ext; funext a x; exact (su.adjoint_mul ..).symm
    rw [hv,luminous,luminous,luminous]; rw [adapt_together,← eye_spin v u]; rw [star_mul,Matrix.transpose_mul] -- verify
-- vary param from Spin contr
lemma continuous_spin (p:su.El→SpinPol d)(hp:Continuous p) : Continuous (fun t:su.El=> luminous d t (p t)):=by
   let g(t:su.El):= Matrix.fromBlocks (colorTable (d:=d) t) 0 0 (star (colorTable (d:=d) t)).transpose; have he(i j:SpinMode d): Continuous fun t:su.El=>colorTable t i j:=by
       unfold colorTable; simp only [Matrix.of_apply]; split_ifs
       · unfold Lat.touch; simp only [Matrix.kroneckerMap_apply]; fun_prop
       exact continuous_const
   have hg (i j:Letters d) : Continuous fun t=>g t i j:=by
       cases i <;> cases j <;> simp only [g,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.transpose_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
       exact he ..
       exact continuous_const
       exact continuous_const
       exact (he ..).star
   have hv(l:List (Letters d)): Continuous fun t=> Grass.changeVars (g t) (l.map atom).prod:=by
       induction l with
       | nil=>simp [continuous_const]
       | cons a l ih=> simp_rw [List.map_cons,List.prod_cons,map_mul,change_atom]; exact Continuous.mul (continuous_finsetSum _ fun i _=> (hg a i).smul (continuous_const (y:=atom i))) ih
   have hx(i:Finset (Letters d)): Continuous fun t=>Grass.changeVars (g t) (mono i):=by
       obtain ⟨F,-,-,h⟩:=expression i
       simpa only [h,List.map_ofFn] using hv (List.ofFn F)

   let F:su.El→SpinPol d:=fun t=>∑ i: Finset (Letters d),coef i (p t) • mono i; have hf:F=p:=funext fun _=> Grass.write _
   change Continuous fun t=>Grass.changeVars (g t) (p t); rw [←hf]; unfold F; simp_rw [map_sum,map_smul]; refine continuous_finsetSum _ (fun i _=>((coef i).continuous_of_finiteDimensional.comp hp).smul (hx i))
noncomputable def score (j:ℕ)(a:Axis)(t:E4) : Labels.Taylor su j→ₗ[ℝ]su.Color:= { toFun:=fun y=>y.value a t, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
lemma taleT (j:ℕ)(H:Labels.Jet su)(x:su.El): Tendsto (fun u=>Labels.colored u H j) (𝓝 x) (𝓝 (Labels.colored x H j)):=by
    let f:=fun u:su.El=> Labels.colored u H j; refine viaTests (fun z:Axis × E4=>score j z.1 z.2) ?_ ?_
    · intro U hu; apply Labels.Taylor.value_ext; funext b t; specialize hu (b,t); simp only [Labels.Taylor.value,Tensor.diagonal, ZeroMemClass.coe_zero,Pi.zero_apply,zero_apply]; exact hu
    rintro ⟨b,t⟩; have ht(u):score j b t (f u)=su.adjoint u ((H j).value b t):=rfl
    change Tendsto (fun w=>score j b t (f w)) _ (𝓝 _); simp_rw [ht]; rw [show score j (b,t).1 (b,t).2 (Labels.colored _ _ j)=su.adjoint x ((H j).value b t) from ht x]; exact ((Push.Mark.continuous_ad su).comp (continuous_id.prodMk (continuous_const (y:=(H j).value b t)))).tendsto x
set_option maxHeartbeats 550000 in
lemma shade (H:Labels.Jet su)(p:Pol d): Continuous (fun u:su.El=>ready d (Labels.colored u H) p):=by
    induction p using TensorProduct.induction_on with
    | zero=> simp [continuous_const]
    | add p q hp hq=>simp_rw [map_add]; exact hp.add hq
    | tmul p q=> simp_rw [ready_t]; refine Continuous.smul (f:=fun u:su.El=> Labels.read (Labels.colored u H) p) ?_ (continuous_const (y:=q))
                 induction p using MvPolynomial.induction_on with
                 | C a=>simp [Labels.read,continuous_const]
                 | add a b ha hb=>simp_rw [map_add]; exact ha.add hb
                 | mul_X a i ha=>
                    simp_rw [map_mul]; refine Continuous.mul ha ?_
                    simp_rw [Labels.read,MvPolynomial.aeval_X]; unfold Labels.coord
                    let L:=((Labels.axes su i.1).coord i.2).toContinuousLinearMap
                    refine Complex.continuous_ofReal.comp (f:=⇑L∘(fun u=> Labels.colored u H i.1)) (L.continuous.comp ?_); refine continuous_iff_continuousAt.mpr ?_
                    exact fun x=> taleT _ H x
lemma circulation (x:Mini d) : Continuous (fun u=>tint u d x) :=by
   refine continuous_iff_continuousAt.mpr (fun u=>tint_heights (Y:=fun u=>tint u d x) ?_)
   intro J; refine Continuous.tendsto (f:=fun u=>ready d J (colorAct u x.val)) ?_ u
   simp_rw [visual]; exact continuous_spin _ (shade J x.val)
lemma tax (x:Mini d) : Integrable (fun u=> tint u d x) su.probHaar:= (circulation x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
noncomputable def colorRing (d:ℕ): Mini d→ₗ[ℂ] Mini d where
     toFun x:=∫ u:su.El, tint u d x ∂su.probHaar
     map_add' x y:=by simp_rw [map_add]; exact integral_add (tax _) (tax _)
     map_smul' c x:=by simp_rw [map_smul]; exact integral_smul ..
lemma ring_law (p:Mini d)(u:su.El): tint u d (colorRing d p)=colorRing d p :=by
    let L:=(tint u d).toContinuousLinearMap; rw [show tint u d (colorRing d p) = L (∫ g:su.El,tint g d p ∂su.probHaar) from rfl, ← L.integral_comp_comm (tax _)]
    simp_rw [show ∀ g,L (tint g d p)=tint (g*u) d p from fun g=>Subtype.ext (tin_mul ..)]; exact integral_mul_right_eq_self (fun g=> tint g d p) u
noncomputable def brighten (d:ℕ) : Mini d→ₗ[ℂ] Label d:= ((cap d).subtype.comp (colorRing d)).codRestrict (labels d) fun p=> ⟨(colorRing d p).property, (Submodule.mem_iInf _).mpr fun i=> LinearMap.mem_ker.mpr (sub_eq_zero.mpr (congr_arg Subtype.val (ring_law p i)))⟩
lemma interior (p: Label d): brighten d (passport d p)=p:=by
    have h(u:su.El):tint u d (passport d p)=passport d p:= Subtype.ext (((label_law _).mp p.property).2 u)
    apply Subtype.ext; change (∫ u:su.El,tint u d (passport d p) ∂su.probHaar).val=_; simp_rw [h]; rw [integral_const]; simp; change ↑((1:ℂ) • passport d p)=p.val; rw [one_smul]; rfl
lemma lace_color (p:Mini d)(t:ℝ)(u:su.El): paceM d t (tint u d p)= tint u d (paceM d t p):=by apply Subtype.ext; rw [pace_local]; change pace d t (colorAct u p.val)=colorAct u (paceM d t p).val; rw [pace_local,pacepaint]
lemma paceRing (p:Mini d)(t:ℝ): paceM d t (colorRing d p)= colorRing d (paceM d t p):=by
    let L:=(paceM d t).toContinuousLinearMap; rw [show paceM d t (colorRing d p)=L (∫ u:su.El, tint u d p ∂su.probHaar) from rfl,← L.integral_comp_comm (tax p)]; simp_rw [show ∀ u:su.El, L (tint u d p)=_ from fun u=> lace_color p t u]; rfl
noncomputable def paceL (d:ℕ)(t:ℝ): Label d→ₗ[ℂ] Label d:= brighten d ∘ₗ paceM d t ∘ₗ passport d
lemma pace_color (p:Mini d)(t:ℝ): paceL d t (brighten d p)= brighten d (paceM d t p):=by
    have h(i:Mini d):passport d (brighten d i)=colorRing d i:=rfl; change brighten _ (paceM _ _ (passport _ _))=_; rw [h,paceRing]; rw [←h]; exact interior _
lemma pace_code (p:Label d)(t:ℝ): (paceL d t p).val=pace d t p.val:=by
    have hz:colorRing d (passport d p)=passport d p:=congr_arg (passport d) (interior p) -- defeq
    change (colorRing d (paceM d t (passport d p))).val=_; rw [← paceRing,hz,pace_local]; rfl
-- readsV
end LoomC
end YM.Massive.Elm
#print axioms YM.Massive.Elm.LoomC.pace_color
#print axioms YM.Massive.Elm.LoomC.circulation
