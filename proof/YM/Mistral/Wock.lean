import YM.Roan.Gram
import YM.Mistral.Banks
/- simple Gram complete basis even after offset discrepancy. costs reconstruction.FAN -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}{s:RawSym}(H:Vale.Laurel d)(K:Landing s H)
variable (V:Choir)
set_option quotPrecheck false
local notation "L"=> ↥(V.level d)
local notation "X"=> Stokes d
variable (g f: Stokes d → Stokes d →ℂ) (he:nearG s H K.ε f)
include he
lemma fullG : Function.Bijective (Γ f):=by
      have h:∀ x, Γ f x=0→x=0:=fun x h=>by have hp:= K.warmth he x; rw [h,norm_zero,mul_zero] at hp; exact norm_le_zero_iff.mp hp
      have hp:=LinearMap.ker_eq_bot.mp (bot_unique (a:=(Γ f).toLinearMap.ker) (fun x hx=> h x hx)) -- Type.Bot_unique named
      exact ⟨hp,(LinearMap.injective_iff_surjective).mp hp⟩
lemma portsG (j:X) : ∃ i,f j i≠0:=by
     by_contra! h; obtain ⟨y,hy⟩:= (fullG H K f he).2 (1:X→ℂ); have ht: ∑ i:X,f j i*y i=1:=congr_fun hy j; simp_rw[h,zero_mul,sum_const_zero] at ht; exact zero_ne_one ht
lemma knownG (i:X): ∃ j, f j i≠0:=by
     by_contra! h; let P:X→ℂ:=Pi.single i (1:ℂ); have ht:Γ f P=0:=by funext a; change ∑ b:X,f a b*P b= _; simp [P, Pi.single_apply, h,sum_ite_irrel]; -- check
     have hp: P=0:= (fullG H K f he).1 (ht.trans (map_zero _|>.symm)); have hh:=congr_fun hp i; simp [P] at hh
omit he
-- reconstruction price basis.Transport projection and all cuts.
variable (P:↥(V.level d) →ₗ[ℂ] (Stokes d → ℂ))(q:Stokes d→ ↥(V.level d))(B:Bool)(p':Stokes d→ Bool)(p0:↥(V.level d)→ₗ[ℂ] ↥(V.level d))
local notation "χ"=> fun i j=>P (q j) i
local notation "Hash" b:arg=> (if b=true then (-1:ℂ) else (1:ℂ))
variable (hK:nearG s H K.ε (fun i j=>P (q j) i))(hB:V.Domestic)
include hK hB
-- include removal for def.Liot.
lemma braid_r (p:L)(W:ℝ)(hv:‖P p‖≤ W)(hG:∀ i,p0 (q i)=(Hash (p' i)) • q i)(ht:p0 p=p):∃ c:X→ℂ,(∑ i:X, c i • q i)=p∧‖c‖≤ K.J*W∧∀ i,p' i=true→ c i=0:=by
      let f:X→ X→ℂ:=χ; have hp:= fullG H K f hK
      let g: (X→ℂ)→ₗ[ℂ] L:=∑ i:X, (LinearMap.proj i).smulRight (q i)
      have hg(w:X→ℂ):g w=∑ i:X,w i • q i:=by simp [g]; -- `LinearMap.sum_apply`
      have hX(w:X→ℂ): Γ f w= P (g w):=by funext j; change ∑ i:X, f j i*w i=P (g w) j; rw [hg,map_sum,Finset.sum_apply]; exact sum_congr rfl fun i _=>by rw[map_smul,Pi.smul_apply,smul_eq_mul]; unfold f; rw [mul_comm]
      have h1 : Injective g:= fun x y h=> hp.1 (by rw[hX,h,hX]); have he :Surjective g:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 h1
      swap; · exact (by rw [Module.finrank_fintype_fun_eq_card]; unfold Vale.Stokes; rw[Fintype.card_fin]; exact (hB.faith d).symm -- typo
                    )
      obtain ⟨f,hf⟩:=he p; refine ⟨f,(hg f).symm.trans hf,?_ ,?_⟩
      · exact (K.warmth hK f).trans (mul_le_mul_of_nonneg_left (by rw [show Γ _ f= P (g f) from hX f,hf]; exact hv) K.fee)
      let u:X→ℂ:= fun i=> f i * (Hash (p' i)); have hu:g u=p0 (g f):=by rw [hg,hg,map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,hG,smul_smul]
      have hz:u=f:= h1 (by rw [hu,hf,ht])
      intro i hi; have h:=congr_fun hz i; unfold u at h; rw [if_pos hi] at h; linear_combination (norm:=ring_nf) (-1/2:ℂ)*h
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.braid_r
