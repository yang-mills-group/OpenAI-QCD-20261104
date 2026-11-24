import YM.Mako.Colfax
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Module
open scoped Topology BigOperators Classical
variable {W V U:Type*}[NormedAddCommGroup W][NormedSpace ℂ W][FiniteDimensional ℂ W]
    [AddCommGroup U][Module ℂ U][AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
variable {σ:ℂ→+*ℂ}[RingHomInvPair σ σ]
lemma fluency (h:Continuous σ)(p:W≃ₛₗ[σ] W): Continuous p:=by
      let B:= finBasis ℂ W; rw [show (p:W→ W)=(fun x=>∑ i, σ (B.coord i x) • p (B i)) from ?_]; swap; · funext i; simp_rw[← map_smulₛₗ,← map_sum]; exact congr_arg p (B.sum_repr i).symm
      apply continuous_finsetSum; intro i _; exact (h.comp (B.coord i).continuous_of_finiteDimensional).smul continuous_const
variable (L:Submodule ℂ U)(u: U≃ₛₗ[σ] U)
lemma kernelS (h:L.map u.toLinearMap=L): ∃ g: L≃ₛₗ[σ]L,∀ x:L,(g x).val=u x.val:=by
     let A:= u.submoduleMap L; let hm:=h
     exact ⟨A.trans (LinearEquiv.ofEq _ _ hm), fun i=>rfl⟩
variable (X:ℕ→ W≃ₗ[ℂ]V)(P:U→ₗ[ℂ] W)(g:V≃ₛₗ[σ] V)
lemma pinW(hp:Surjective P)(he:∀ i j,g (X i (P j))=X i (P (u j))):∃ p:W≃ₛₗ[σ]W,(∀ i j,g (X i j)= X i (p j))∧(∀ i,p (P i)=P (u i)):=by
     let L:= X 0; let F:= L.trans (g.trans L.symm); have hv(v:U):F (P v)=P (u v):=by unfold F L; simp [he]
     refine ⟨F,fun i j=>?_,hv⟩; obtain ⟨v,rfl⟩:=hp j; rw[he,hv]
variable {ι:Type*} (p: ι→End ℂ W)(Fq:ι→End ℂ V)
variable (h:∀ j:ι,∀ x:W,Tendsto (fun i:ℕ=>(X i).symm (Fq j (X i x))) atTop (𝓝 (p j x)))
include h
lemma lucent(hσ:Continuous σ)(hp:Surjective P)(he:∀ i j,g (X i (P j))=X i (P (u j)))(t:ι→ι)(hb:Surjective t)(hx:∀ i v,g (Fq i v)=Fq (t i) (g v)) (J:End ℂ (W→ₗ[ℂ] V))(hz:Split J (range fun i=>power (p i) (Fq i)))(i:ℕ)(x:U): g (J (X i).toLinearMap (P x))=J (X i).toLinearMap (P (u x)):=by
     obtain ⟨f,hp',hv⟩:= pinW u X P g hp he; have ht(i:ι)(x:W) : f (p i x)= p (t i) (f x):=by
           apply tendsto_nhds_unique ((fluency hσ f).continuousAt.tendsto.comp (h i x)); apply (h (t i) (f x)).congr'; refine Eventually.of_forall fun y=>?_ ; dsimp only [Function.comp]; apply (X y).injective; rw [LinearEquiv.apply_symm_apply,←hp',←hx, ←hp',LinearEquiv.apply_symm_apply]
     rw[←hv]; exact (weft f g p Fq t hb ht hx (X i).toLinearMap J hz (fun j=>(hp' i j).symm) (P x)).symm
-- unit separately
omit h
lemma recode(A:W→ₗ[ℂ] V)(J:End ℂ (W →ₗ[ℂ] V))(x:W)(H:∀ i,p i x=0)(hx:∀ i,Fq i (A x)=0)(hz:Fet (range fun i=>power (p i) (Fq i)) (J-1)): J A x=A x:=by
     let C:= range fun i=>power (p i) (Fq i)
     have ht(y:End ℂ (W→ₗ[ℂ]V))(h:Fet C y)(a:W→ₗ[ℂ]V)(ha:∀ i,Fq i (a x)=0): y a x=0:=by
           induction h generalizing a with
           | mem i hi=> obtain ⟨v,rfl⟩:=hi; rw [power_app,H,ha,map_zero,sub_self]
           | zero=>rfl
           | times p q _ _ ih h=> exact ih (q a) (fun i=>by rw[h a ha,map_zero])
           | add p q _ _ ih h=> rw [LinearMap.add_apply,LinearMap.add_apply, ih a ha,h a ha,add_zero]
           | smul i p _ ih=> rw [LinearMap.smul_apply,LinearMap.smul_apply, ih a ha,smul_zero]
     exact sub_eq_zero.mp (ht _ hz A hx)
end YM.Mako
#print axioms YM.Mako.kernelS
#print axioms YM.Mako.lucent
#print axioms YM.Mako.recode
