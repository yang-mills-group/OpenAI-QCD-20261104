import YM.Helio.Odd
import YM.Pollen.Bolt
import YM.Pollen.Chonk
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
open scoped Kronecker
open Grass.Ward Massive.PCAC
set_option quotPrecheck false
variable (F:Flavor 6)(Z:ParcelZ (c:=c))
local notation "Y"=> Z.R
local notation "H"=> Z.f
local notation "ψ"=> Modes c 6
local notation "T'"=> Massive.PCAC.spot F F
noncomputable def capsΛ (f:Flavor 6) : Sheet c→L[ℂ] Sour (Modes c 6):=by -- name Sour via scoped
    exact LinearMap.toContinuousLinearMap { toFun:=fun x=>Matrix.kronecker x (Massive.PCAC.spot f f), map_add':=fun x y=>Matrix.add_kronecker .., map_smul':=fun x y=>Matrix.smul_kronecker .. }
noncomputable def cream : Sour (Modes c 6)→L[ℂ] EvenA c 6:= LinearMap.toContinuousLinearMap { toFun:=fun x=>⟨form x,form_plus _⟩,map_add':=fun x y=> Subtype.ext (form_add x y), map_smul':=fun a y=> Subtype.ext (form_smul ..) }
noncomputable def bouquet (F:Flavor 6) : Sheet c→L[ℂ] EvenA c 6:= cream.comp (capsΛ F)
local notation "V"=> bouquet F
local notation "G"=> (bouquet F ∘ Z.val)
variable {T K:ℝ}
variable (h: Z.Ticket p T K B)
include h
lemma sunup : shadeG G:=by
    intro X g; let X':= Z.val X; let W:=gauge g X; let M:=Z.val W; let s:= siteRot g; let t:= Lat.rotates 6 g
    have hx:M=s*X'*star s:=by
          apply Sway.whist; intro i j; unfold M X' ParcelZ.val s siteRot; rw [pairBl,cell_ride_right,cell_ride_left,Equiv.refl_apply,Equiv.refl_apply,pairBl]; split; next hp=> obtain ⟨rfl,rfl⟩:=hp; exact h.con g X
          next _=> rw [Matrix.mul_zero,zero_mul]
    have he : capsΛ F M=t*capsΛ F X'*star t:=by
           rw[hx]; change ((s*X'*star s) ⊗ₖ T')= t*(X' ⊗ₖ T')*star t; rw [show t=s ⊗ₖ 1 from Sway.choir_in ..,Lat.star_kr,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,star_one,one_mul,mul_one] -- star instance
    change adapter _ _ (form _)= form _; change adapter t ((star t).transpose) (form (capsΛ F M))= form (capsΛ F X'); rw [he, form_map, Matrix.transpose_transpose,mul_assoc (t*_),(Lat.rotates_law 6 g).1,mul_one,←mul_assoc,(Lat.rotates_law ..).1,one_mul]
local notation "p₀"=> Z.α
local notation "p₁"=> Z.β
local notation "L"=> blockL p₀ p₁
lemma bounded (x:Bundle) : Gated Z.R (V (L x)):=by
     change form _∈_; unfold form; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases hz:i.1.1∈Y∧j.1.1∈Y; · apply Subalgebra.smul_mem; apply Subalgebra.mul_mem <;> apply Creek.marked; exacts [mem_filter.mpr ⟨mem_univ _,hz.2⟩,mem_filter.mpr ⟨mem_univ _,hz.1⟩]
     -- disambiguate notation shape
     change capsΛ F (L x) i j • (Grass.psi j*Grass.bar i) ∈ _; rw[show capsΛ F (L x) i j=0 from ?_] -- lhs change
     · rw [zero_smul]; exact Subalgebra.zero_mem _
     change (Stew.block p₀ p₁ x ⊗ₖ T') i j=0; simp only [Matrix.kroneckerMap_apply,Stew.block,Matrix.of_apply]; rw [if_neg (fun (hp : i.1.1 = Z.α ∧ j.1.1 = Z.β) =>hz ⟨hp.1.symm ▸ h.site,hp.2.symm ▸ h.son⟩),zero_mul]
variable (hp:0 < a)
include hp
lemma milk (x:Bundle) : load (fun _=>a) (light _ (V (L x))) ≤ fingers 6^2*a^2*‖x‖:=by
    let D:= capsΛ F (L x); let w (i j:Site c):= if i=p₀∧ j=p₁ then ‖x‖ else 0
    have he i j: ‖D i j‖ ≤ w i.1.1 j.1.1:=by
       change ‖(Stew.block p₀ p₁ x ⊗ₖ T') i j‖≤ _; simp only [Matrix.kroneckerMap_apply]; change ‖Stew.block _ _ x i.1 j.1 * Massive.PCAC.spot F F _ _‖ ≤ _; unfold Stew.block Massive.PCAC.spot w; simp only [Matrix.of_apply]; split
       next h=> split; next h=>rw [mul_one]; exact Cost.north ..
                rw [mul_zero,norm_zero]; exact norm_nonneg _
       next h=> rw [zero_mul,norm_zero]
    have hx:(∑ i:ψ,∑ j:ψ,‖D i j‖) ≤ fingers 6^2*‖x‖:=(paddleB (F:=6) 0 ∅ 0 _ w he).trans_eq (by rw[sum_eq_single Z.α]; · simp [w]
                                                                                                · intro i _ hi; simp [w,hi]
                                                                                                simp)
    exact (Port.fauna D hp).trans ((mul_le_mul_of_nonneg_left hx (sq_nonneg _)).trans_eq (by ring))
lemma textile (o: Site c)(hz:o∈ Z.R) : Woven o Z.R p a G (fingers 6^2*a^2*K):=by
     have hc:0 ≤ fingers 6^2*a^2*K:=mul_nonneg (by positivity) h.nt; let T:= ((V).comp L).restrictScalars ℝ; let X j:= T (Z.f j); change Woven _ _ _ _ X _; refine ⟨fun i j hx=> congr_arg T (h.reach i j hx),fun i=> bounded F Z h _,fun X_ h_=>T.contDiff.contDiffAt.comp _ (h.chart _ _),fun X_ hg l hv hq=>?_, (T.continuous.comp h.pores).measurable,hc⟩
     let z:= leftDerivs Z.f l X_; rw [show leftDerivs X l X_= V (L z) from Push.Local.left_linear T _ (h.chart p.order _) hv]; let A:ℝ:=diameterQ B Z.R
     apply (senCamp Y (fun i hi=> show separation i o ≤ diameterQ B Z.R from (Corona.extent _ _ hi hz)) _ hp (bounded F Z h _)).trans; rw [Loom.pulse]
     exact (mul_le_mul_of_nonneg_left (milk F Z h hp z) (sq_nonneg _)).trans (le_trans (le_of_eq (show (1+A)^2*(fingers 6^2*a^2*‖z‖)= fingers 6^2*a^2*(‖z‖*(1+A)^2) by ring)) (mul_le_mul_of_nonneg_left (h.mask o hz X_ hg l hv hq) (by positivity)))
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.textile
