import YM.Eden.Plank
import YM.Eden.Grove
/-! # Curvature evaluation and orientation through all seams and stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius Classical
variable {G:Gauge}{d' k i m:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD
-- SU conjugation exact. ensure chart iso permitted
noncomputable def rayK : su.Mat→ₗᵢ[ℝ] su.Mat where
    toFun x:=which true x
    map_add' x y:= by ext; simp [which]; rfl
    map_smul' a x:= by change which true (a • (x: Mat))= a • which true x; ext; simp [which]
    norm_map' x:=by change ‖which true x‖=‖x‖; simp [Matrix.frobenius_norm_def,which]; rfl -- lemma name
lemma map_lie(x:su.Alg): rayK x.val∈su.lie:=by
     rw [show x.val=su.colorMat (su.colorIso.symm x) from congr_arg Subtype.val (su.colorIso.apply_symm_apply x).symm,show rayK _= _ from (reflMat _).symm]; apply Gauge.colorMat_mem -- type inference
lemma ray_two (x:su.Mat): rayK (rayK x)=x:=UV.which_double _
section F
attribute [local instance] Gauge.frobInner
lemma ray_κ (x:su.Mat) : su.projectColor (rayK x)= reflectColor (su.projectColor x):=by
    apply su.colorMat_injective; rw [su.colorMat_project, UV.reflMat,su.colorMat_project]
    change su.lie.starProjection (rayK x)=rayK (su.lie.starProjection x)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (map_lie ⟨su.lie.starProjection x,by simp⟩)
    intro y hy; -- register frob inner instance

    have he:= rayK.inner_map_map (x-su.lie.starProjection x) (rayK y); rw [map_sub,ray_two] at he; rw [he]; exact Submodule.starProjection_inner_eq_zero _ _ (map_lie ⟨_,hy⟩)
end F
lemma ray_E(u:su.El): su.curvature (Massive.conjugate u)=reflectColor (su.curvature u):=by
    unfold Gauge.curvature; rw [← ray_κ,map_smul rayK,map_sub rayK]; exact congr_arg (fun p=> su.projectColor ((1/2:ℝ) • p)) (by rw [← Papyrus.conj_rev]; rfl)
noncomputable def vision : su.Color→ₗᵢ[ℝ] su.Color where
    toLinearMap:=reflectColor
    norm_map' x :=by
        change ‖(reflectColor x)‖=‖x‖; apply mul_left_cancel₀ su.colorScale_pos.ne'; rw [← su.colorMat_norm, ← su.colorMat_norm, reflMat]; exact rayK.norm_map _
lemma antenna(u:RG.Slot)(U:CoverConfig su) : u.eval (Massive.conjugate ∘ U)= vision (u.eval U) :=by
     unfold RG.Slot.eval; rw [show Lattice.travel (Massive.conjugate ∘ U) 0 u.walk = Massive.conjugate _ from TorusPCAC.Geometry.Reflection.roadmap U 0 u.walk,show faceValue (Massive.conjugate ∘ U) _=Massive.conjugate _ from TorusPCAC.Geometry.Reflection.faces U (u.offset,u.plaq),ray_E]; exact (reflPaint ..).symm
noncomputable def Bach (G:Gauge)(d:ℕ)(x:CoverConfig G) : Ink G d:= fun i=> (paints i.1.2.1 x (chore d (stemP (G:=G) i) i.1.2.1)) i.2
lemma stat(x:CoverConfig G)(s: Signed) : Bach G k (pull s 0 x)=swingK s (Bach G k x):=by
    funext i; let z:=i.1; let p:=z.2.1; let l:=stemP i; unfold Bach swingK; dsimp only; rw[show stemP (tideK s i)=_ from stem_m s i.1, show (tideK s i).1.2.1=took s p from rfl, sights]; let Q:=petal s p (stemP i); change _=Q * (Q * _); rw[← mul_assoc, show Q*Q= _ from still ..,one_mul]; rfl
lemma tons (x:CoverConfig G) (i:Motif k) : lampK (Bach G k x) i=paints i.2.1 x (chore k (List.ofFn i.2.2) i.2.1):=by ext; rfl
lemma outer_R(x:CoverConfig su): Bach su k (Massive.conjugate ∘ x)=liftedK reflectColor (Bach su k x):=by
     funext i; unfold liftedK; rw[tons]; unfold Bach; have h (p:PlaqAxes)(Y:Rhythm): paints p (Massive.conjugate ∘ x) Y = reflectColor (paints p x Y):=by
         unfold Arise.paints hears; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; apply congr_arg; exact antenna ..
     rw [h]
lemma lantern (x:CoverConfig G)(g:Cover→G.El): Bach G k (Lattice.gauge g x) = liftedK (G.adjoint (g 0)) (Bach G k x):=by
     funext i; unfold liftedK; rw[tons]; simp only [Bach,paints,hears,Finsupp.linearCombination_apply,Finsupp.sum,Work.G06.slot_gauge,map_sum,map_smul]
@[fun_prop] lemma alley(d:ℕ): Continuous (Bach G d):=by unfold Bach paints hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum]; apply continuous_pi; intro i; fun_prop
end YM.Eden
#print axioms YM.Eden.outer_R
