import YM.Heron.Gunk
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open Finset
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)(u v e:Flavor 6)(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(p q:Multi d)(i j:Pinor)(a b:Hue)(t t':Bool)(m n:Fin 2)
local notation "P"=> piD m t p i a u
local notation "Q"=> piD n t' q j b v
local notation "E"=> combD x Δ
local notation "R"=> fromCenter Δ.val (x 0)
local notation "x₀"=> x 0
local notation "x₁"=> x 1
include hx hχ
lemma isolated : combD x Δ u (piD m false p i a u) (piD m true q j a u) χ=0:=by
   rw [bible x hx u Δ p q i j a χ hχ m m]; fin_cases m
   · exact two_suns gamma learn hχ.1 hχ.2.1 (lode x hx χ hχ) (helm Δ _) (by
          intro t _ i z; unfold fromCenter; rw[add_sub_cancel_left,add_sub_cancel_left]; rw [show M4.move _ (t • z)=_ from map_smul (Matrix.toEuclideanLin Δ.val) t z]; rfl) _ _ _ _
   let hF:= care gamma (deck i) learn x₁ (steps p); let G:= pose (FlipT gamma) (deck j) (steps q) x₁; have hK: Way gamma {x₁}ᶜ G:= care (FlipT gamma) _ (flips gamma learn) _ _; exact zeroFlux gamma (helm Δ _) isOpen_compl_singleton hχ.1 hχ.2.1 (cult x hx χ hχ) hF hK learn
lemma stuck (r s:letters d): combD x Δ u (m,r) (m,s) χ=0:=by
     obtain ⟨t,p,i,a,c,rfl⟩:= voicing r; obtain ⟨z,q,j,b,d,rfl⟩:=voicing s; by_cases he: t=false∧z=true∧a=b∧c=u∧d=u
     · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩:= he; exact isolated x hx χ hχ ..
     exact voidP x c d u Δ p q i j a b t z χ m m he
lemma arcRev (f g:Spins): exportFlux (brook (FlipT gamma) f g R) χ = -exportFlux (brook gamma g f R) χ :=by
     unfold exportFlux; refine congr_arg Neg.neg (?_); unfold brook; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← integral_neg]; apply integral_congr_ae; refine Eventually.of_forall fun t=>?_ ; dsimp only; simp_rw [show ∀ b:Axis,blaze gamma g f i b t= _ from fun b=>sister t i b gamma g f,smul_neg,Finset.sum_neg_distrib,smul_neg,neg_neg] -- order
local notation "V"=> pose (formT (!t)) (deck j) (steps q) (x 1)
local notation "U"=> piD (0:Fin 2) t p i a u
local notation "S"=> piD (1:Fin 2) (!t) q j a u
local notation "D"=> charm x Γ
lemma stable : Way (formT t) ({x₁}ᶜ) V:=by
     have hp: formT t=FlipT (formT (!t)):= by cases t<;>rfl
     rw [show formT t= _ from hp]; -- also changes inside V? t only, Flip
     exact care _ _ (actual (!t)) _ _
include hΓ
lemma upper : combD x Δ u U S χ- combD x Δ u S U χ=4 * charm x Γ u U S :=by
    have ht : charm x Γ u U S= -dotL (deck i) (deriveL (steps p) (twistS (formT t) R V) (x 0)):=by unfold charm; rw [if_pos (show (piD 0 _ _ _ _ _).1= (0: Fin 2) from rfl)]; exact fineK x hx u Γ Δ hΓ p q i j a t
    let F:=pose (formT t) (deck i) (steps p) x₀; have hg:= stable x hx χ hχ q j t -- order
    have h: combD x Δ u U S χ- combD x Δ u S U χ= exportFlux (brook (formT t) F V R) χ:=by
          cases t with
          | false=>
               rw [Bool.not_false]; rw [show combD x Δ u _ _ χ=exportFlux _ χ from bible x hx u Δ p q i j a χ hχ 0 1, show combD x Δ u _ _ χ=0 from voidP x u u u Δ q p j i a a true false χ 1 0 (by simp)]; exact sub_zero _
          | true=>
               rw [Bool.not_true]; rw [show combD x Δ u _ _ χ=0 from voidP x u u u Δ p q i j a a true false χ 0 1 (by simp), show combD x Δ u _ _ χ=exportFlux _ χ from bible x hx u Δ q p j i a χ hχ 1 0]; rw [zero_sub]; exact (arcRev x hx χ hχ Δ F _).symm
    rw[h,show exportFlux _ _= _ from tones (formT t) (actual t) x₀ (deck i) isOpen_compl_singleton V R χ hg (helm Δ _) (cult x hx χ hχ) hχ.1 hχ.2.1 (lode x hx χ hχ) (steps p), ht]; simp [Complex.real_smul]
lemma arcs(r s:letters d):combD x Δ u (0,r) (1,s) χ- combD x Δ u (1,s) (0,r) χ=4* charm x Γ u (0,r) (1,s):=by
   obtain ⟨t,p,i,a,c,rfl⟩:= voicing r; obtain ⟨t',q,j,b,e,rfl⟩:= voicing s; by_cases he: a=b∧c=u∧e=u∧t'=(!t)
   · obtain ⟨h1,h2,h3,h4⟩:=he; subst b c e t'; exact upper x hx χ hχ u Γ Δ hΓ p q i j a t
   let U':Dot d:=(0,code t p i a c); let S':Dot d:=(1,code t' q j b e); have ht: charm x Γ u U' S'=0:=by
         unfold charm; rw [if_pos (show U'.1=(0:Fin 2) from rfl)]; by_cases h:c=u; swap; · exact sunny x c u Γ Δ hΓ p i a t (Ne.symm h) S'
         subst u; exact hazeK x hx _ _ Γ Δ hΓ p q i j a b t t' (by intro hh; tauto)
   have hl:combD x Δ u U' S' χ=0:= voidP x c e u Δ p q i j a b t t' χ (0: Fin 2) (1:Fin 2) (by intro h; obtain ⟨h1,h2,h3,h4,h5⟩:= h; exact he ⟨h3,h4,h5,h2.trans (by rw [h1]; rfl)⟩)
   have hz:combD x Δ u S' U' χ=0:= voidP x e c u Δ q p j i b a t' t χ 1 0 (by intro h; obtain ⟨h1,h2,h3,h4,h5⟩:= h; exact he ⟨h3.symm,h5,h4,h1.trans (by rw[h2]; rfl)⟩)
   change combD x Δ u U' S' χ-combD x Δ u S' U' χ=4*charm x Γ u U' S'; rw [hl,hz,ht,sub_zero,mul_zero]
end YM.Heron
#print axioms YM.Heron.arcs
#print axioms YM.Heron.stuck
