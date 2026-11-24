import YM.QCD.Bay.High
/-! # Sun always accepts true covariant stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM Eyrie Sparks Cost
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f n: Side}
variable {j k p:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}
local notation "S"=>sliceL L H
variable {A B a b t r q δ κ y x ξ w m α:ℝ} {l:ℕ}
variable (L H) {P:Plan j}{C : Offer 1 a A}{D: Offer 2 b B}
abbrev park (L:Flight j k)(H:f.val=c.val*L.L.val)(P:Plan j)(C : Offer 1 a A)(D: Offer 2 b B)(t m:ℝ) := pesto P L H (trunkM C D t m f)
lemma paraded (hc:0<a)(hb:0<b)(ht:0<t)(hy:t≤1): Tow S (sun S) (sun S) (park L H P C D t m):=by
    refine ⟨fun v g T U hv=>?_⟩; let φ:=(raise S v).haze T g; have hp:=trail hv
    have he: vaultF P L H 0 (sky (raise S v) U)=aura φ (vaultF P L H 0 U):=by
       have hZ : (S).embed 0=0:=map_zero (S).root; have hm: Glare v.1 ((S).embed 0) ((S).embed 0) ((S).embed v.2) g:=by rw [hZ]; exact hv.1
       have ht:=spin_vault L H hm (show Swing v.1 T from hv.2) U P; dsimp only at ht; rw [hZ] at ht; exact ht
    unfold park pesto trunkM blossomT; simp only [Pi.add_apply]; change _=aura φ (vaultF P L H 0 U + (_+_+((m:ℂ) • 1))); simp only [aura_add]; rw [he, precious C t ht hy hc _ _ _ hv, precious D t ht hy hb _ _ _ hv,aura_scale,aura_one hp]; rfl

variable {T:Grid f→Sheet f}
lemma stock (hT:Tow S (sun S) (sun S) T) : Tow S (sun S) (sun S) (inverser T):=by
   refine ⟨fun i f u U hv=>?_⟩; unfold inverser; rw [hT.goes i f u U hv]; exact (invert_W _ _ (trail hv)).symm
lemma table (hT:Tow S (sun S) (sun S) T) : Tow S (sun S) (dot S) (rightL L H T):=by
   refine ⟨fun i f u U hv=>?_⟩; unfold rightL; rw [(stock L H hT).goes i f u U hv]; have hZ : (S).embed 0=0:=map_zero (S).root; have hh: Glare i.1 ((S).embed 0) ((S).embed 0) ((S).embed i.2) f:=by rw [hZ]; exact hv.1
   have hm:= dual L H hh (show Swing i.1 u from hv.2) U
   dsimp only at hm; rw [hZ] at hm; rw [show tied L H 0 (sky (raise S i) U)=chair S (dot S) i u f*tied L H 0 U *star (chair S (sun S) i u f) from hm]; -- wrong skying
   set B:=chair S (sun S) i u f; have he: B=haze (raise S i) u f:=rfl
   have ht: star B * B=1:=(trail hv).1; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul]; simp only [← Matrix.star_eq_conjTranspose (star B),star_star,Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star B),ht, Matrix.one_mul]; rfl
lemma inverse_spine (hT:Tow S (sun S) (sun S) T) (u:Sun L c f H δ r q a t l T): ∃ U: Sun L c f H δ r q a t l T,Sacred U :=by
    have he (x: Grid f): foldH (inverser T x)=inverser T x:=by
       have hp :=(funds0 (T x)).2 (u.stable.crease x); let s:=T x
       have hy : aura (chirality f) (star s)=s:=hp
       have hx: star s⁻¹=(star s)⁻¹:=Matrix.conjTranspose_nonsing_inv _
       change chirality f * star s⁻¹ *chirality f=s⁻¹; nth_rw 2 [← chi_star (n:=f)]; rw [hx,← aura,invert_W _ _ ⟨by simp,by simp⟩]; rw [hy]
    refine honoredPack u (stock L H hT) (funext he) (table L H hT) ?_
    funext x; let Z:=tied L H 0 x; let X:=inverser T x; have hp : terraL (Site f)*Xᴴ*terraL (Site f)=X:=he x
    have hh : Z*terraL (Site f)=terraL (Site c)*Z:= tiedSpin ..
    change terraL (Site c)*(X*Zᴴ)ᴴ*terraL (Site f)= Z*X; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,← hh, Matrix.mul_assoc Z, Matrix.mul_assoc Z,hp]
end YM.QCD.Bay
