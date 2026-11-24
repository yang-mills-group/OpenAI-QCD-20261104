import YM.Eden.Spoil
/-! # preparatory uniform ABI across competing proof irrelevant Fintype.Scalar Self read budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j r B l:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b t' v ε s z:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek Next.Fluctuations Hypnos Hypnos.Fruit
-- Farm procurement ALWAYS for k≤ etc
lemma creditsG {C C':ℝ}(Dg:Eyes su k B l j a v b ε s C)(Ds:QCD.Bloom.Spar k B l r ε s C') (H:Bed)(ht:Grain a v b H n)(F:Train r)(hk:d ≤ k)(hq:(YM.Eden.milky 0 H n (G:=su) (d':=d)).IsSymm): Farm (wager 0 H n hq) (corsage F n d 0) (max C C'):=by
    refine ⟨Dg.pay.le.trans (le_max_left ..),fun i j=> ?_,fun i j=> ?_⟩
    · change ‖- YM.Eden.milky 0 H n i j‖≤ _; rw [norm_neg]; exact (Dg.youth d hk d hk i j n H ht 0 0).trans (le_max_left ..) -- edit arguments
    change ‖(-(mood d 0 (1:Grid n)* Buzz.start n F 6*(mood d 0 (1:Grid n)).transpose)) i j‖ ≤ _; let X:= mood d 0 (1:Grid n); let M:= Buzz.start n F 6; rw[Matrix.neg_apply,norm_neg]; have hh:(X*M*X.transpose) i j= (tokenS n i 0*M*(tokenS n j 0).transpose) () ():=by unfold X; simp only [Matrix.mul_apply,Matrix.transpose_apply,pinned_zero]
    rw[hh]; exact (Ds.youth d hk d hk i j n F 0 0).trans (le_max_right ..) -- use exact
variable (V:Grain a v b H n)
noncomputable def observation (X:Grid n)(κ:ℝ) : Col su n→ℝ:= fun i=>κ⁻¹*Hypnos.marrow X (bleep i) i.2.2
lemma lensP (c:Side)(p: Zinc su k)(A:Grid c)(κ:ℝ)(x:Cover): ∑ i:Col su c,voteP c p x () i*(observation A κ i:ℂ) = ((κ⁻¹:ℝ):ℂ)*(uniR su A x p:ℂ):=by
    unfold observation voteP pupil; simp only [Fintype.sum_prod_type,lavish,Matrix.of_apply];
    let y:=rayP p; let H:=p.2; let K:=p.1.2.1; let V:=κ⁻¹
    have hp (Y:Rhythm): ∑ i:Site c,∑ v:TypeFace 2, ∑ h:su.ColorIndex,(if H=h then (↑(stalk c x (plaquette K) (came Y) () (i,v)):ℂ) else 0)*((V*Hypnos.marrow A (bleep (G:=su) (i,v,h)) h :ℝ):ℂ)=(V:ℂ)*(↑(hears (fun w:Walk=> su.curvature (faceValue A (slotFace ⟨w,K⟩ (wrap c x))) p.2) Y):ℂ) :=by
         induction Y using Finsupp.induction_linear with
         | zero=> simp
         | add i j h hp=> simp_rw [map_add,Matrix.add_apply,Complex.ofReal_add, ite_add_zero, add_mul,sum_add_distrib,h,hp,mul_add] -- find ite_add
         | single z a=>
          simp only [came,Arise.hears, stalk,Finsupp.linearCombination_single,map_smul,one_smul]; -- `beep`
          simp [Matrix.of_apply,ite_mul, mul_ite,sum_add_distrib, Hypnos.marrow,H, K,bleep,slotFace, apply_ite ((↑) :ℝ→ℂ),ite_and]; rw [show plaqEquiv.symm (plaquette p.1.2.1) = _ from plaqEquiv.symm_apply_apply p.1.2.1,Slot.offset,add_comm ((wrap c) x)]; exact mul_left_comm .. 
    exact hp y
section
open QCD.Bera
noncomputable abbrev special (n:Side): Fintype (Col su n):=inferInstance
-- repacks arbitrary

noncomputable def chartD (x:Cover)(K:ℕ) : Matrix (Tube su K) (Col su n) ℂ:=Matrix.of fun i j=>voteP n i x () j
noncomputable def payD (k:ℕ)(w:ℝ): Matrix (Tube su k) (Tube su k) ℂ:= Matrix.diagonal (fun i=> (favorU w i:ℂ))
lemma lender0 (x:Cover)(A:Lily su d)(U:Grid n)(κ:ℝ): taxG d x U κ⁻¹ A = QCD.Bera.Oce.eve (observation U κ) (exchange (Bera.spool (chartD x d)) A):=by
    induction A using MvPolynomial.induction_on with
    | C c'=>simp [taxG, nestK,QCD.Bera.Oce.eve]
    | add a b h hp=> rw [map_add,map_add,map_add,h,hp]
    | mul_X a i h=>rw [map_mul,map_mul,map_mul,h]; congr 1
                   rw [QCD.Bera.wool,map_sum,taxG,nestK,MvPolynomial.aeval_X]; simp_rw [QCD.Bera.Oce.eve,map_smul,MvPolynomial.aeval_X]; exact (Complex.ofReal_mul _ _).trans (lensP n i U κ x).symm
variable [X':Fintype (Col su n)]
lemma lender (x:Cover)(A:Lily su d)(U:Grid n)(κ:ℝ): taxG d x U κ⁻¹ A = QCD.Bera.Oce.eve (observation U κ) (exchange (Bera.spool (chartD x d)) A):=by
    rw [Subsingleton.elim X' (special n)]; exact lender0 ..
-- actual motive.S under possible Binder.
lemma chores(x:Cover): chartD (n:=n) x d * heartP H su n * (chartD (n:=n) x d).transpose= YM.Eden.milky x H n :=by
    rw [Subsingleton.elim X' (special n)] -- picks self. name separate function.
    ext i j; change _=pop1 _ _ _ _ _; simp only [Matrix.mul_apply,Matrix.transpose_apply,chartD,Matrix.of_apply,pop1]
lemma boughtS (W:ℝ)(A: Lily su k): stemsP su k W A =exchange (QCD.Bera.spool (payD k W)) A:=by
    apply DFunLike.congr_fun (f:= stemsP ..) (g:=exchange _) (?_) A; ext1 j; rw [stemsP,MvPolynomial.aeval_X,wool]; simp [payD,Matrix.diagonal_apply,ite_smul] -- definitional
end
end YM.Eden
#print axioms YM.Eden.chores
#print axioms YM.Eden.creditsG
