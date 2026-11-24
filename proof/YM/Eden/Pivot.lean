import YM.Eden.Bonus
/-! # Chart Taylor certificate. Gauge stencil calibrate even far limit.W. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open YM.Source YM.Source.Drops Push.Mark
variable (i: Tube G d)
noncomputable def rayP (v:Tube G d) := chore d (stemP v) v.1.2.1
local notation "fP"=>rayP i
noncomputable def sunP (i: Tube G d)(H:Hol G)(d':ℕ) := let X:=rayP i; let u:=i.1.2.1; ∑ w∈ X.support, (X w:ℂ) • (spell d' (safeLinear H d' ⟨w,u⟩ i.2))
lemma swell (H:Hol G)(A:Labels.Jet G)(h: Peg H (d/2)) : Labels.read A (sunP i H (d/2)) = Labels.read (expand (d/2) (trunk (d/2) A)) (rollK G d (MvPolynomial.X i)) :=by
     unfold sunP; dsimp only; rw [map_sum]; simp_rw [map_smul, spell_reads]; rw [Arise.Range.gated]; let B:=trunk (d/2) A; let Y:=expand (d/2) B; let p:= i.1.2.1; let k:=i.1.1.val; let X(v:Walk):= Blurb H (d/2) ⟨v,p⟩ B; let L:= (hears X (fP)); let Z:= EuclideanSpace.proj (𝕜:=ℝ) i.2
     have hx:L i.2= (↑((stemP i).length.factorial):ℕ) • Maxwell.takeCurl (Y _) p.val.1 p.val.2 (basis ∘ (stemP i).get) i.2:=gauge_t _ _ _ _ H h (rare _) (by omega) _
     let J':=i.1.2.2; have hp(m n:ℕ)(g:m=n)(v:Labels.Jet G)(f:Fin m→Axis)(h:Fin n→Axis)(hg:∀ k:Fin m,h (Fin.cast g k)=f k): rootLeg (v m) (p,f)=rootLeg (v n) (p,h):=by
         subst g; congr; exact (funext hg).symm
     have he:L i.2= pub d G Y i:=by
         rw[hx]; change rootLeg (Y _) (p,(stemP i).get) i.2 = _; rw [hp _ k (pongs ..) Y _ J' (fun k=> by unfold J' stemP; simp; rfl)] ; rfl
     rw [show pub d G _ i=_ from he.symm]; unfold L; rw [show hears X _ i.2= hears (fun w=> Z (X w)) (rayP i) from mixH (fP) Z X]; unfold hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum,Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul]; rfl
lemma sprayV (H:Hol G)(A:Labels.Jet G)(h:Peg H (d/2)) : Labels.read A (sunP i H (d/2)) = if 2*(i.1.1.val+2) ≤ d then Labels.read A (rollK G d (MvPolynomial.X i)) else 0:=by
     rw[swell i H A h,gated,gated]; unfold pub; unfold expand; by_cases hp:i.1.1.val < d/2-1
     · rw[dif_pos hp,if_pos (by omega)]; rfl
     rw[dif_neg hp,if_neg (by omega)]; simp [rootLeg,Maxwell.takeCurl] -- ok
omit i
open Poised.Plans
variable (p:Tube su d) (H:SourceRead.TaperHol)(K:Hol su) (h:Peg K (d/2))
lemma cast_light : setas d (Elm.coarse d (rollK su d (MvPolynomial.X p))) = if 2*(p.1.1.val+2) ≤ d then setas d (Elm.coarse d (rollK su d (MvPolynomial.X p))) else 0:=by
    split; rfl
    next h=>
      apply Subtype.ext; change drips d _= 0; unfold rollK; rw [MvPolynomial.aeval_X]; obtain ⟨L,hL⟩:=coarseL (d:=d); rw [← hL]; simp_rw [map_sum]; apply Finset.sum_eq_zero; intro i _; rw [MvPolynomial.C_mul',map_smul,map_smul,hL,lampT,if_neg (show ¬2*Labels.generation _ ≤ _ from h),smul_zero]
include h
lemma pursuit : setas d (Elm.coarse d (sunP p K (d/2)))= setas d (Elm.coarse d (rollK su d (MvPolynomial.X p))):=by
    have he:= fun A=>sprayV p K A h; by_cases hp:2*(p.1.1.val+2) ≤ d; · rw [Labels.eval_ext (sunP p K (d/2)) (rollK su d (MvPolynomial.X p)) (fun i=> by rw [he,if_pos hp])]
    have ht:sunP p K (d/2)=0:=Labels.eval_ext _ _ (fun i=>by rw [he,if_neg hp,map_zero]); obtain ⟨F,hF⟩:=coarseL (d:=d); rw [cast_light p,if_neg hp,ht,← hF,map_zero,map_zero]
omit h
local notation "X"=>rayP p
lemma vision_g : wide d 1 ((MvPolynomial.X p) ⊗ₜ[ℂ]1) = ∑ i∈ (X).support,((X i:ℝ):ℂ) • tendency ⟨i,p.1.2.1⟩ p.2:=by
    funext n o; apply ContinuousMap.ext; intro U; rw [wow,power_t,map_one, Finset.sum_apply, Finset.sum_apply,ContinuousMap.sum_apply]; rw [incomeF,one_smul,nestK,MvPolynomial.aeval_X]; unfold Bach Arise.paints hears; rw [Finsupp.linearCombination_apply,Finsupp.sum]; let P:=p.1.2.1; let F(v:Walk):= (RG.Slot.eval (G:=su) ⟨v,P⟩ (expandAt (wrap n o) U)); change ((↑((∑ i ∈ (X).support,X i • F i) p.2):ℂ)) • _= _; rw [show (∑ i∈ (X).support,X i • F i) p.2= ∑ i∈ (X).support,X i*F i p.2 from map_sum (EuclideanSpace.proj (𝕜:=ℝ) p.2) (fun i=>X i • F i) _,Complex.ofReal_sum,Finset.sum_smul]; refine Finset.sum_congr rfl fun w _=>?_ ; rw[Complex.ofReal_mul,mul_smul]; rfl
include h
lemma germsG : Survey H (wide d 1 ((MvPolynomial.X p) ⊗ₜ[ℂ]1)) 1 0 (setas d (revere d (MvPolynomial.X p ⊗ₜ[ℂ]1))) :=by rw [vision_g,revere, TensorProduct.map_tmul]; change Survey _ _ _ _ (setas d (Elm.coarse d (rollK su d (MvPolynomial.X p)))); obtain ⟨F,hF⟩:=coarseL (d:=d); rw[← pursuit p K h,← hF]; unfold sunP; dsimp only; simp_rw [map_sum, map_smul, hF]; exact Survey.total _ _ _ _ _ _ _ fun i _=> (growsSlot H K _ _ h).scale _
end YM.Eden
#print axioms YM.Eden.germsG
