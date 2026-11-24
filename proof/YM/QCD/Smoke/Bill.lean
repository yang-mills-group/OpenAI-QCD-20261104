import YM.QCD.Smoke.Proof

/-! # Ward identity per onsite score. Color normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical InnerProductSpace
variable {n N:Side}{K:ℕ}{S:SparkMesh}{B:Cnr n→ℝ}{r D:ℝ}
structure Cigar (T:Cnr n→ℝ)(r D:ℝ) : Prop where
 W : Flock (traceG n) Push.Uniform.bolt T 0 r D
 spun (k:su.El): T ∘ stain k=ᶠ[𝓝 0] T
 law : ∀ᶠ y : Swatch su n in 𝓝 0,T (moveField y)= T y.2
lemma burstG (x:Site n)(b:Sparks.Angle): ∃ L: su.Color →ₗ[ℝ] Cnr n, ∀ v,L v=hybrid v x b := by
  refine ⟨{ toFun:=fun i => hybrid i x b,map_add':=fun a b'=>?_,map_smul':=fun m c=>?_ },fun _=>rfl⟩ <;> ext i
  · unfold hybrid; simp only [Pi.add_apply]; split_ifs <;> simp
  unfold hybrid; simp only [RingHom.id_apply,Pi.smul_apply]; split_ifs <;> simp
lemma cigar_nil (h:Cigar B r D)(U:Cnr n): blade U B 0=0 :=by
  let L:= fderiv ℝ B 0
  have hp (i:Sparks.Angle)(x:Site n)(b:su.Color): L (hybrid b x i)=0:=by
    obtain ⟨M,hM⟩:=burstG x i
    let K := L.toLinearMap ∘ₗ M
    have hh (u:su.El) (v:su.Color): K (su.adjoint u v)=K v:=by
      let Z:=stain (m:=n) u
      have hV:= blade_same (hybrid v x i) (h.spun u); rw [transfuse _ _ (show ContDiffAt ℝ ω B (Z 0) from Z.map_zero.symm ▸ h.W.host),map_zero, stained_lock] at hV
      change L (M _)=L (M _); rw [hM,hM]; exact hV
    have ht:=Push.Loops.invariant_null QCD.simple K hh
    rw [← hM]; exact LinearMap.congr_fun ht _
  unfold blade; rw [bolt_add U,map_sum]; refine sum_eq_zero (fun p _ =>?_); rw [map_smul]; rcases p with ⟨i,j,k⟩
  let v: su.Color:= EuclideanSpace.single k 1 -- inspect
  rw [show Push.Uniform.bolt (i,j,k)=hybrid v i j from ?_]; rw [show fderiv ℝ B 0 _=_ from hp j i v]; rw [smul_zero]
  funext ⟨x,b,l⟩; simp only [hybrid, Push.Uniform.bolt, Pi.single_apply]; by_cases h:x=i ∧ b=j <;> by_cases he:k=l <;> simp_all [v, Ne.symm]

def scanG (B:Cnr n→ℝ)(x:Fin 2→Cnr n):ℝ:=iteratedFDeriv ℝ 2 B 0 x
lemma cargo (h:Cigar B r D)(p:Fin 2→Cnr n)(u:su.El): scanG B (stain u ∘ p)=scanG B p:=by
  let Z:= stain (m:=n) u; have he: ContDiffAt ℝ ω B (Z 0):=Z.map_zero.symm ▸ h.W.host
  have hg := DFunLike.congr_fun (((h.spun u).iteratedFDeriv ℝ 2).eq_of_nhds) p; rw [iter_lin_at (L:=Z) (he.of_le le_top),map_zero] at hg; exact hg
lemma cigar_cut (h:Cigar B r D)(c: Fin 2→Cnr n)(v:Fin 2→BaseSites su n) : scanG B (fun i=>c i-gradientA su n (v i))=scanG B c:=by
  let Z i : Swatch su n:= (v i,c i)
  let L:=ContinuousLinearMap.snd ℝ (BaseSites su n) (Cnr n)
  -- cusp moveField x=0; cigar first derivative =0. direct chain rule.
  let T:= (moveField : Swatch su n→Cnr n); have hx : ContDiffAt ℝ ω T 0:=moveField_analytic.contDiffAt
  have he:T 0=0:=moveField_zero
  have hQ:= repeated (Z 0) (Z 1) (show B ∘ T=ᶠ[𝓝 0] B ∘ L from h.law)
  rw [area_eval _ _ hx (he.symm ▸ h.W.host),he, cigar_nil h,add_zero, adapt L _ _ (by rw [map_zero]; exact h.W.host),map_zero] at hQ
  have hp i: blade (Z i) T 0=c i-gradientA su n (v i):=Sparks.move_left ..
  rw [hp,hp,iter _ _ h.W.host, iter _ _ h.W.host] at hQ
  unfold scanG; rw [show (fun i=> c i-gradientA su n (v i))=![_,_] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]; -- placeholders infer? no
  exact hQ.trans (by rw [show ![L (Z 0),L (Z 1)]=c from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)])
end YM.QCD.Smoke
