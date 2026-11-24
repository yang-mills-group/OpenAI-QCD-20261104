import YM.Eden.Money
/-! # physical staked cap: linear formation via universal exact scheme.Glyph. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal
variable (U:Grid n)(p: Bard d)(x y:Cover)(η:ℝ)
noncomputable def incomeF (d:ℕ)(x:Cover)(U:Grid n)(η:ℝ): Lily su d→ₐ[ℂ]ℂ:=nestK (η • Bach su d (expandAt (wrap n x) U))
noncomputable def rateS (d:ℕ)(x:Cover)(U:Grid n): SpinPol d→ₐ[ℂ]Lat.Fields n 6:= changeVars (mood d x U)
private def liftD (f :Grid n→ Bard d→ₗ[ℂ] Lat.Fields n 6)(h:∀ x,Continuous (fun U=>f U x)): Bard d→ₗ[ℂ] Insertion n 6 where
    toFun x:= ⟨_,h x⟩
    map_add' x y:= ContinuousMap.ext (fun U=>map_add (f U) x y)
    map_smul' t x:=ContinuousMap.ext (fun U=>map_smul (f U) t x)
noncomputable def powerG (d:ℕ)(x:Cover)(U:Grid n)(η:ℝ):Bard d→ₗ[ℂ]Lat.Fields n 6:= ((TensorProduct.lid ℂ _).toLinearMap).comp (TensorProduct.map (incomeF d x U η).toLinearMap (rateS d x U).toLinearMap)
lemma power_t (P:Lily su d)(Z:SpinPol d): powerG d x U η (P⊗ₜ[ℂ]Z)=incomeF d x U η P • rateS d x U Z:=by unfold powerG; rw [LinearMap.comp_apply,TensorProduct.map_tmul,LinearEquiv.coe_coe,TensorProduct.lid_tmul]; rfl
lemma arch (X:Bard d): Continuous (fun U:Grid n => powerG d x U η X):=by
    induction X using TensorProduct.induction_on with
    | zero=> simp only [map_zero]; fun_prop
    | tmul p q=>
       have h:Continuous (fun U:Grid n=> incomeF d x U η p):=by
           unfold incomeF nestK; induction p using MvPolynomial.induction_on with
           | C z=> simp only [MvPolynomial.aeval_C]; fun_prop
           | add p q h hp=> simp only [map_add]; exact h.add hp
           | mul_X p i h=> simp only [map_mul, MvPolynomial.aeval_X]; refine h.mul ((Complex.continuous_ofReal.comp (show Continuous (fun U=> (_:Ink su d) i) from ?_))); change Continuous (fun U=> (η • Bach su d (expandAt (wrap n x) U)) i); exact (continuous_apply i).comp (((alley d).comp (show Continuous (expandAt (K:=su.El) (wrap n x)) from continuous_pi fun i=> continuous_apply _)).const_smul η) -- syntax
       simp_rw [power_t]; apply h.smul; unfold rateS; induction q using ExteriorAlgebra.induction with
       | algebraMap a=> simp_rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one]; exact continuous_const
       | ι v=> simp_rw [line_atoms (A:=Pairs (SpinMode d)),map_sum,map_smul,change_atom]; fun_prop
       | add p q h hp=> simp_rw [map_add]; exact h.add hp
       | mul p q h hp=> simp_rw [map_mul]; exact h.mul hp
    | add p q h hp=>simp_rw [map_add]; exact h.add hp
noncomputable def garth (d:ℕ)(x:Cover)(n:Side)(η:ℝ):Bard d →ₗ[ℂ] Insertion n 6:= liftD _ (arch x η)
noncomputable def wide (d:ℕ)(η:ℝ):Bard d→ₗ[ℂ] Drape:= LinearMap.pi (fun n:Side=> LinearMap.pi fun x:Cover=> garth d x n η)
lemma wow (x:Cover)(p:Bard d)(U:Grid c) : wide d η p c x U = powerG d x U η p:=rfl
-- assembled stencil at launch from label surface.D
variable (X: UV.Pol d)(pV: UV.Label d)(W:ℝ)(H:Bed)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm)
noncomputable def reelW (d:ℕ)(H:Bed)(n:Side)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm): Bard d→ₗ[ℂ] Bard d:=TensorProduct.map (milk (wager _ _ _ h)) (rosewood F n d)
noncomputable def flareR (d:ℕ)(H:Bed)(n:Side)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm)(L η:ℝ): Bard d→ₗ[ℂ] Drape:= wide d η ∘ₗ (reelW _ H n F h) ∘ₗ padU d L
noncomputable def lotus (d:ℕ)(H:Bed)(n:Side)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm)(L η:ℝ):UV.Pol d→ₗ[ℂ] Drape:= flareR d H n F h L η ∘ₗ Arise.Range.introduce _
lemma reel_at (P:Lily su d)(X:SpinPol d)(U: Grid c): flareR d H n F h W η (P ⊗ₜ[ℂ] X) c x U=incomeF d x U η (milk (wager _ _ _ h) (stemsP su d W P)) • rateS d x U (rosewood F n d (changeVars (gateP d W) X)):=by unfold flareR; rw [LinearMap.comp_apply,LinearMap.comp_apply,padU,reelW,TensorProduct.map_tmul,TensorProduct.map_tmul,wow, power_t]; rfl
lemma leafs_t (P:GPol)(X:SpinPol d)(U:Grid c): lotus d H n F h W η (P⊗ₜ[ℂ] X) c x U=incomeF d x U η (milk (wager _ _ _ h) (stemsP su d W (loCast su d P))) • rateS d x U (rosewood F n d (changeVars (gateP d W) X)):=by unfold lotus introduce; rw [LinearMap.comp_apply, TensorProduct.map_tmul]; exact reel_at ..
-- shift.A.Tag.AP
open Patria TorusPCAC.Geometry

local notation "TU"=> pull 1 (wrap n y) U
lemma sites_E (X:SpinPol d): Kit.disguise (BannerV n y) (rateS d x TU X)=rateS d (x+y) U X:=by
    unfold Kit.disguise adapter rateS; rw [multipleChange]; exact congr_arg (fun G:Matrix (Sings d) (Pairs (Modes n 6)) ℂ => changeVars G X) (roam ..)
lemma sites_G (P:Lily su d): incomeF d x TU η P=incomeF d (x+y) U η P:=by unfold incomeF; rw[pull_one]; rw [show expandAt (wrap n x) (Lattice.translate (wrap n y) U) = expandAt (wrap n (x+y)) U from (by funext j; simp only [expandAt,Lattice.translate,map_add,add_assoc])]
local notation "V0"=> flareR d H n F h W η
lemma eo (X:Bard d)(c:Side): Patria.march y ⇑(V0 X c x) =⇑(V0 X c (x+y)):=by
     funext U; induction X using TensorProduct.induction_on with
     | zero=>simp only [map_zero,Pi.zero_apply,ContinuousMap.coe_zero]; exact map_zero _
     | tmul p q=> unfold Patria.march TorusPCAC.Geometry.post crank; rw [reel_at,reel_at,map_smul]; apply congr_arg₂ (· • ·); exact sites_G ..; exact sites_E ..
     | add p q h hp=> rw[map_add]; unfold march TorusPCAC.Geometry.post; simp only [Pi.add_apply,ContinuousMap.add_apply,map_add]; exact congr_arg₂ _ h hp
end YM.Eden
#print axioms YM.Eden.leafs_t
#print axioms YM.Eden.eo
