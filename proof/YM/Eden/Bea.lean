import YM.Eden.Pivot
/-! # parity Bough.Det precise Taylor. -/
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
open RP YM.Source YM.Source.Drops Push.Mark
variable (U:Grid n)(x:Cover)(p:Multi d)(W:Walk)(e i:Dike)(q:Bool)
lemma spots (u: Sings d):∃ (q:Bool)(p:Multi d)(i:Dike), atom u=lineT q (place p i):=by
    rcases u with ⟨⟨p,i⟩,w⟩|⟨⟨p,i⟩,w⟩; exact ⟨false,_,_,show atom _=lineT false (place p (i,w)) from rfl⟩; exact ⟨true,_,_,show atom _=lineT true (place p (i,w)) from rfl⟩ -- inference
noncomputable abbrev skimRY {K:Type}[Fintype K]{Z:Type}[Fintype Z] (q: Bool)(M:Matrix K Z ℂ): Matrix K Z ℂ:= if q then Mstar M else M
lemma flatM {K:Type}[Fintype K]{Z:Type}[Fintype Z](M:Matrix K Z ℂ)(i:K) : changeVars (QCD.Eden.slab M) (lineT q i)= ∑ j:Z, skimRY q M i j • lineT q j:=by unfold QCD.Eden.slab; cases q; exact adapt_psi ..; exact adapt_bar ..
noncomputable def stageV (q:Bool)(U:Grid n)(x:Cover)(p:Multi d): Dike→ Site n→ Dike→ℂ:= fun i v j=> skimRY q (rollsU d x U) (place p i) (place v j)
lemma sageV (u:Site n) : rollsU d x U (place p i) (place u e)= (if i.2=e.2 then bladeU x U p u i.1 e.1 else 0):=by unfold rollsU; rw [imprints]; rfl -- over? 
local notation "fₚ"=>rider p
noncomputable def sparkY (q: Bool)(x:Cover)(i e: Dike)(U:Grid n)(p:Multi d) (v: Site n)(w:Walk) := if v=landsE n x w then ((rider p w:ℝ):ℂ)* peggle q (stripe n x w U) i e else 0
lemma stage_N (u:Site n) : stageV q U x p i u e=∑ w∈(rider p).support,sparkY q x i e U p u w:=by
     have he : stageV false U x p i u e= ∑ w∈ (rider p).support, sparkY false x i e U p u w:=by
          change rollsU d x U (place p i) (place u e)=_; rw [sageV]; unfold bladeU hears sparkY; rw [Finsupp.linearCombination_apply,Finsupp.sum,Matrix.sum_apply]; by_cases hp : i.2=e.2
          · rw [if_pos hp]; apply sum_congr rfl; intro v _; unfold fadeF; rw [Matrix.smul_apply]; split_ifs with hu
            · change _= _*(stripe _ _ _ _ i e); unfold stripe; rw [Matrix.smul_apply]; rw [Matrix.smul_apply]; unfold clutch blux copies; rw [Matrix.blockDiagonal_apply,if_pos hp]; rfl
            simp
          rw [if_neg hp,Finset.sum_eq_zero]; intro w _; split; · change _* stripe _ _ _ _ i e=0; unfold stripe; rw [Matrix.smul_apply]; simp only [clutch,blux,copies,Matrix.blockDiagonal_apply, if_neg hp, smul_zero, mul_zero]
          rfl
     cases q; exact he
     change star (stageV false U x p i u e) = _; rw [he,star_sum]; apply Finset.sum_congr rfl; intro w _; unfold sparkY; split_ifs; · rw [star_mul',show ∀ i:ℝ, star (i:ℂ)=(i:ℂ) from fun i=> Complex.conj_ofReal _]; rfl
     rw [star_zero]
lemma whirly : wide d 1 ((1: Lily su d) ⊗ₜ[ℂ] lineT q (place p i)) =∑ w∈(rider p).support, (↑(fₚ w):ℂ) • burnish w q i:=by
     funext n o; apply ContinuousMap.ext; intro U; rw [wow,power_t,map_one,one_smul]; unfold rateS mood; rw[flatM, placed_sum, Finset.sum_apply,Finset.sum_apply,ContinuousMap.sum_apply]
     change (∑ x,∑ j, stageV q U o p i x j • lineT q (place x j))=∑ w∈ (rider p).support,(↑(fₚ w):ℂ) • beams q n o w U i; unfold beams; simp_rw [stage_N,Finset.sum_smul, Finset.smul_sum]; rw [Finset.sum_comm]; let V (x:Site n)(j w):=sparkY q o i j U p x w • lineT q (place x j)
     change (∑ j,∑ x:Site n,∑ w∈ (rider p).support,V x j w)=_; rw [show (∑ j,∑ x:Site n,∑ w∈ (rider p).support,V x j w)= ∑ w∈(rider p).support,∑ j,∑ x:Site n,V x j w from (by trans ∑ j,∑ w∈(rider p).support,∑ x:Site n,V x j w; exact sum_congr rfl (fun j _=> sum_comm); exact sum_comm)]
     apply sum_congr rfl; intro w _; apply sum_congr rfl; intro j _; rw [Finset.sum_eq_single (landsE n o w)]; · unfold V sparkY; rw [if_pos rfl,mul_smul]
     · intro y _ hv; unfold V sparkY; rw [if_neg hv,zero_smul]
     simp
open Purl
lemma binry : ∑ w∈(rider p).support, (↑(fₚ w):ℂ) • Grass.line (twig q i.1 i.2 (vector (stop (0: Cover) w)))=lineT q (place p i) :=by -- d infer
     simp_rw [← map_smul,← map_sum]; rw [show ∑ w∈(rider p).support,(↑(fₚ w):ℂ) • twig _ _ _ _= trow q p i.1 i.2 from ?_]; exact timely ..
     unfold twig; simp_rw [Finset.smul_sum,smul_smul]; rw[Finset.sum_comm]; simp_rw [← sum_smul, sing_cover,← Complex.ofReal_mul,← Complex.ofReal_sum]
     have he(X:Multi d):∑ w∈ (rider p).support,fₚ w *(profileL X (stop 0 w))=if p=X then 1 else 0:=by
          have hp(w:Walk) : profileL X (stop 0 w)=Gem.score X (gross (stop 0 w)):=by unfold profileL Gem.score Papyrus.Purl.ψ; rfl
          simp_rw [hp]; exact scoreR p X
     simp only [he]; simp
variable (H: SourceRead.TaperHol)(K:Hol su)
include K
lemma gemsS : Survey H (wide d 1 ((1: Lily su d) ⊗ₜ[ℂ] lineT q (place p i))) 0 1 (setas d (revere d ((1:Lily su d)⊗ₜ[ℂ] lineT q (place p i)))):=by
    rw [whirly,revere,TensorProduct.map_tmul]; change Survey _ _ _ _ (setas d ((rollK su d 1)⊗ₜ[ℂ] lineT q (place p i))); rw [map_one]; obtain ⟨F,hF⟩:=floraL (d:=d); rw [show (1:GPol)⊗ₜ[ℂ] lineT q (place p i)= F (lineT q (place p i)) from hF ▸ rfl]; rw [← binry]; simp_rw [map_sum,map_smul,hF]; exact Survey.total _ _ _ _ _ _ _ fun i h=> (growsBeams i _ K _ _ d).scale _
end YM.Eden
#print axioms YM.Eden.gemsS
