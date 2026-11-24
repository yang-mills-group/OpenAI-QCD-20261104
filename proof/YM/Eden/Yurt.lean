import YM.Eden.Crew
/-! # Normal startup word, illustrated ph. -/
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
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek
lemma couP (p:Grimo d): ∃ L:Pad d, L.1.length=(tagwt p).1.2 ∧ L.2.length=(tagwt p).2 ∧ motto L=sketch p :=by
   obtain ⟨L,hL,l⟩:= compost p.1; obtain ⟨F,-,-,hp⟩:= Grass.expression p.2; refine ⟨(L,List.ofFn F),?_,List.length_ofFn,?_⟩
   · change L.length=_; rw[hL]; unfold countL tagwt; dsimp only; rw [Finsupp.weight_apply,Finsupp.sum,Prod.snd_sum]; simp [legwt]
   unfold motto sketch; dsimp only; rw[l,hp,List.map_ofFn]
variable (C:ℝ)(hz:0 ≤ C)
include hz
lemma pledgesN (p:Bard d)(h:p∈ Rgl d i k m):∃ A:ℝ,0≤A ∧∀ (P:Symmetric (Tube su d))(V:Matrix (Sings d) (Sings d) ℂ), Farm P V C→ Quota motto (raysL k m) (vessel P V p-p) A:=by
     let W:=raysL (d:=d) k m; refine Submodule.span_induction ?_ ?_ ?_ ?_ h
     · rintro x ⟨v,h,rfl⟩; obtain ⟨L,hL,l,hp⟩:=couP v; rw [show tagwt v=((i,k),m) from h] at hL l; rw [← hp, ← show L.1.length=k from hL, ← show L.2.length=m from l]; let j:= L.1.length+L.2.length; exact ⟨stip j C j,stip_nn _ _ _ hz,fun P V h=> shapes _ _ C h j j le_rfl L le_rfl⟩
     · refine ⟨0,le_rfl,fun P V h=>by rw[map_zero,sub_self]; exact sterile _ le_rfl⟩
     · rintro p q _ _ ⟨A,ha,h⟩ ⟨B,hb,hp⟩; refine ⟨A+B,add_nonneg ha hb, fun P V hF=> ?_⟩; rw [map_add]; apply Eq.mp _ ((h P V hF).joins (hp P V hF)); congr 1; abel
     rintro c p _ ⟨A,h,H⟩; refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) h,fun P V ht=>?_⟩; rw [map_smul,← _root_.smul_sub c (vessel P V p) p]; exact (H _ _ ht).scale _
noncomputable def oink (d k m:ℕ): Finset (Pad d):= (raysR d k m).toFinset
omit hz
lemma ringlet (p:Pad d)(η:ℝ): wide d η (motto p) =(η:ℂ)^p.1.length • wide d 1 (motto p):=by
     rcases p with ⟨p,q⟩; funext n v; apply ContinuousMap.ext; intro U; simp only [Pi.smul_apply,ContinuousMap.smul_apply,wow,motto,power_t]; rw[smul_smul]; congr 1
     have h(p:Lp d): incomeF d v U η (Lχ p)=(η:ℂ)^p.length * incomeF d v U 1 (Lχ p):=by
        induction p with|nil=> simp [Lχ]|cons p i ih=> unfold Lχ; rw[List.map_cons,List.prod_cons,map_mul,map_mul]; rw[show incomeF d v _ η _= _ from ih]; rw [ List.length_cons,pow_succ',incomeF,nestK,incomeF,nestK]; simp only [MvPolynomial.aeval_X, one_smul, Pi.smul_apply,Complex.ofReal_mul,Lχ, smul_eq_mul,Complex.ofReal_one]; ring
     exact h p
lemma beamL (η:ℝ) (p:Bard d)(h:p∈Rgl d i k m): wide d η p=(η:ℂ)^k • wide d 1 p:=by
     refine Submodule.span_induction (p:=fun x _=> wide d η x=(η:ℂ)^k • wide d 1 x) ?_ (by rw[map_zero,map_zero,smul_zero]) (fun x y _ _ h hp=>by rw [map_add,map_add,h,hp,smul_add]) (fun a x _ h=>by rw [map_smul,map_smul,h,smul_comm]) h
     rintro x ⟨p,h,rfl⟩; obtain ⟨W,hw,hx,hp⟩:=couP p; rw [show tagwt p=_ from h] at hw; rw [←hp, ringlet,show W.1.length=k from hw]
lemma ages (T:SourceRead.TaperHol)(K:Hol su)(hk:Drops.Peg K (d/2))(p: Pad d): Survey T (wide d 1 (motto p)) p.1.length p.2.length (setas d (revere d (motto p))):=by
     have he:motto p=(Lχ p.1 ⊗ₜ[ℂ](1:SpinPol d))* ((1:Lily su d)⊗ₜ[ℂ]Lξ p.2):=by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,one_mul]; rfl
     have h:= resp_mul T _ _ _ _ _ _ (decor T K hk p.1) (skyline T K hk p.2); change Survey _ (wide d 1 _) (p.1.length+0) (0+p.2.length) (setas d (revere d _)) at h
     rw[← he,zero_add,add_zero] at h; exact h
include hz
lemma sunny (p:Bard d)(h:p∈ Rgl d i k m):∃ A:ℝ,0≤ A ∧∀ (W η:ℝ)(c:Side)(H:Bed)(hq: (milky 0 H c (G:=su) (d':=d)).IsSymm)(j:ℕ)(F:Train j), Farm (wager 0 H c hq) (corsage F c d 0) C→ ∃ X:Pad d→ℂ, (∑ z∈ oink d k m, ‖X z‖) ≤ A ∧
      flareR d H c F hq W η p=(W:ℂ)^i • ((η:ℂ)^k • wide d 1 p+ ∑ z∈ oink d k m, X z • (η:ℂ)^z.1.length • wide d 1 (motto z)):=by
    obtain ⟨A,hA,ha⟩:=pledgesN C hz p h; refine ⟨A,hA,?_⟩; intro W η c H hq j F hf; have he:= ha _ _ hf; obtain ⟨X,hX,hP⟩:=he.allot (Z:=oink d k m) (le_of_eq (raysR d k m|>.coe_toFinset).symm)
    refine ⟨X,hP,?_⟩; rw [flareR,LinearMap.comp_apply, LinearMap.comp_apply,rates W _ h,map_smul,map_smul]; rw [show reelW d H c F hq p= p+∑ z∈oink d k m, X z • motto z from (eq_add_of_sub_eq' hX),map_add,map_sum, beamL η p h]; simp_rw[map_smul, fun p:Pad d=>ringlet p η]
end YM.Eden
#print axioms YM.Eden.sunny
#print axioms YM.Eden.ages
