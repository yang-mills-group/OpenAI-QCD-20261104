import YM.QCD.Port.Path
/-! # actual mismatch estimates and packing. Hash parser. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local Cost
open Jets Sun Revolve Garden Bay Strut LeafM Paths
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{j k:ℕ}{v η A t Z q C r δ ξ a b B p h m g z:ℝ}{F:Flight j k}{e:f.val=c.val*F.L.val}{P:Plan j}{J:Plan k}{O:Offer 1 a b}{H:Offer 2 B p}{l T:ℕ}
local notation "X"=> park F e P O H ξ m
local notation "S"=> sliceL F e

def dusk (F:Flight j k)(e:f.val=c.val*F.L.val) (J: Plan k) (D:Grid f→Sheet f) := (wood J 0 F.land ∘ lowC (sliceL F e))-foam F e D -- sign later. 
lemma duskTow {D:St f}(ht:Tow S (sun S) (sun S) D):Tow S (dot S) (dot S) (dusk F e J D) := by
  refine ⟨fun i h T U H=>?_⟩; let d:= (raise S i); let Q:=chair S (sun S) i T h; let Y:=chair S (dot S) i T h
  have hQ: Q ∈ unitary _:= trail H; have hp: Y∈unitary _:= trail (mist S i H)
  let G:= (wood J 0 F.land ∘ lowC S)
  have hv := (faithful S J F.land).goes i h T U H
  have he:= table F e ht
  have hu:tied F e 0 (sky d U)=Y*tied F e 0 U*star Q:= by
    have hz:(S).embed 0=0:=map_zero (S).root
    have hi : Glare i.1 ((S).embed 0) ((S).embed 0) ((S).embed i.2) h:=by rw [hz]; exact H.1
    have hY:= Bay.table F e ht
    have hh:= Revolve.dual F e hi (show Swing i.1 T from H.2) U
    dsimp only at hh; rw [hz] at hh; exact hh
  have hk (V:Grid f): dusk F e J D V=G V-(1-tied F e 0 V*rightL F e D V):=by unfold dusk rightL; simp only [Pi.sub_apply, foam, Matrix.mul_assoc]; rfl -- sign type Rail
  change dusk F e J D (sky d U)=Y*dusk F e J D U*star Y; rw [hk,hk]; rw [show G (sky d U)=_ from hv, hu,show rightL F e D (sky d U)=Q* rightL F e D U*star Y from he.goes i h T U H]; unfold chair at *; dsimp only [Y] at *; simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hp.2,Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star Q),hQ.1,Matrix.one_mul]
lemma duskStar {D:St f}{U:Grid f}(ht:Chiral (chirality f) (D U)):foldH (dusk F e J D U)=dusk F e J D U:=by
   let Q:= tied F e 0 U; let L:= inverser D U; let J₀:=terraL (Site c); let J':=terraL (Site f)
   have he : J'* Lᴴ * J'=L:=by
       have hp: aura (chirality f) (star (D U))=(D U):=  (funds0 _).2 ht
       change chirality f* ((D U)⁻¹)ᴴ* chirality f=_
       nth_rw 2 [← chi_star (n:=f)]; rw [Matrix.conjTranspose_nonsing_inv]; change aura _ (star (D U))⁻¹=_; rw [invert_W _ _ ⟨by simp,by simp⟩,hp]; rfl
   have hJ : J₀*J₀=1:= chi_sq
   have hL : Q*J'=J₀* Q:= tiedSpin ..
   have hS : J'*Qᴴ=Qᴴ*J₀:=by have hf:=congr_arg Matrix.conjTranspose hL; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,show J₀ᴴ=J₀ from terraJ,show J'ᴴ=J' from terraJ] at hf; exact hf
   let G:=wood J 0 F.land (lowC S U)
   have hG:J₀* Gᴴ*J₀=G:=by change chirality c*_ *chirality c=_; nth_rw 2 [← chi_star (n:=c)]; exact (funds0 _).2 (show Chiral _ G from spinO ..)
   change J₀*(G-(1-Q*L*Qᴴ))ᴴ*J₀=G-(1-Q*L*Qᴴ); simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hG,hJ]; rw [← Matrix.mul_assoc J₀ Q,← hL]; simp only [Matrix.mul_assoc]; rw [← hS,← Matrix.mul_assoc Lᴴ,← Matrix.mul_assoc J',← Matrix.mul_assoc J',he] -- simplify
lemma unspent (hp: Species F e v q δ r A l X):
 ‖dusk F e J X 1‖ ≤ massL F.L* (stamp P F.L *|m| *A⁻¹)*massL F.L:=by
   let I:= X 1; let T:=father F e
   have hp0:= hp.forest; have he:=hp.calf; have hl :=hp.sole 1; have hh : ‖I⁻¹‖ ≤ A⁻¹:= (hp.terrific 1).reciprocal hp.calf
   have hs: ‖T⁻¹‖≤ stamp P F.L:=by unfold T; rw [← tree_zero P]; exact ticket_B ..
   have hM : I=T+(m:ℂ) • 1:=by
     unfold I park pesto trunkM blossomT; simp only [Pi.add_apply,Pi.smul_apply]; rw [Fork.pale (frosting O.W) (by decide),Fork.pale (frosting H.W) (by decide),tree_zero, add_zero,zero_add]; rfl
   let p:=stamp P F.L *|m| *A⁻¹
   have hz:=healthy P F.L; have hv:= mass_pos F.L
   have hr:‖I⁻¹-T⁻¹‖ ≤ p:=by
      rw [show I⁻¹-T⁻¹= -(T⁻¹*(I-T)*I⁻¹) by rw [mul_sub,sub_mul,mul_assoc T⁻¹ I I⁻¹, Matrix.mul_nonsing_inv I hl,Matrix.mul_one, Matrix.nonsing_inv_mul T (high_rank F e),Matrix.one_mul,neg_sub],show I-T=(m:ℂ) • 1 by rw [hM]; abel,norm_neg]
      refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hs ?_ (norm_nonneg _) hz.le)) hh (norm_nonneg _) (by positivity)); rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,oneNorm,mul_one]
   let W:=conn F e; have hW:‖W‖ ≤ massL F.L:=towerB _ _ _ (1:Grid f)
   unfold dusk; dsimp only [Pi.sub_apply,comp_apply]; rw [former,bare_this,← heir F e]
   change ‖1-W*T⁻¹*Wᴴ - (1-W*I⁻¹*Wᴴ)‖≤ _; rw [show 1-W*T⁻¹*Wᴴ - (1-W*I⁻¹*Wᴴ)= W*(I⁻¹-T⁻¹)*Wᴴ from by rw [Matrix.mul_sub,Matrix.sub_mul]; abel]; exact (Matrix.l2_opNorm_mul ..).trans (mul_le_mul ((Matrix.l2_opNorm_mul ..).trans (mul_le_mul hW hr (norm_nonneg _) hv.le)) ((Matrix.l2_opNorm_conjTranspose _).le.trans hW) (norm_nonneg _) (mul_nonneg hv.le ((norm_nonneg _).trans hr)))
end YM.QCD.Port
