import YM.QCD.Revolve.Feet

/-! # general matrix merit on an actual gauge step
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 40000
namespace YM.QCD.Orbit
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {c C f F m : Side} {U V : Sheet c}
lemma inv_detail (X:Sheet c) (h:X∈unitary _): X⁻¹=star X:= Matrix.inv_eq_left_inv h.1
lemma invert_W (X Y:Sheet c) (h:X∈unitary _): aura X (Y⁻¹)=(aura X Y)⁻¹:=by
  unfold aura; rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_detail X h,inv_detail _ (Unitary.star_mem h)]; simp [Matrix.mul_assoc]
lemma compatible (X U:Sheet c)(h:X∈unitary _): aura (star X) (aura X U)=U:= by
  have H: X=star (star X):=(star_star ..).symm
  nth_rw 1 [show aura X=aura (star (star X)) from congr_arg aura H]; rw [inverse_aura _ (Unitary.star_mem h)]
lemma momentum (X V: Sheet f)(U : Sheet c)(A: Rail c f) (he: U∈unitary _) (h:V∈unitary _):
    let B:= U*A*star V
    aura V (Aᴴ*A)=Bᴴ*B ∧ aura U (1-A*X⁻¹*Aᴴ)=1-B*(aura V X)⁻¹*Bᴴ:=by
  intro B; unfold B; simp only [Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose U, ← Matrix.star_eq_conjTranspose (star V),star_star]; constructor
  · unfold aura; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star U) U, he.1, Matrix.one_mul]
  rw [aura_sub,aura_one he,← invert_W V _ h]; unfold aura; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star V) V, h.1,Matrix.one_mul, ← Matrix.mul_assoc (star V) V,h.1, Matrix.one_mul]
lemma funds0 (A:Sheet c) : newborn c A=A ↔ Chiral (chirality c) A:=by
  have hx (U:Sheet c): star (newborn c U)=(chirality c)*U*chirality c:=by simp [newborn,aura,Matrix.mul_assoc,chi_star]
  constructor
  · intro h; have hv:=hx A; rw [h] at hv; exact hv
  intro h; apply star_injective; exact (hx A).trans h.symm

variable {j k:ℕ} (P:Flight j k) (B:Plan j) (h:f.val=c.val*P.L.val)
local notation "Q" => tied P h 0
local notation "r" => sliceL P h

def shiftH (B:Plan j)(D:Grid f→Sheet f) (U:Grid f):= vaultF B P h 0 U+D U
def shiftL (B:Plan j)(D:Grid f→Sheet f) (U:Grid f):=1-Q U*(shiftH P h B D U)⁻¹* (Q U)ᴴ
lemma chir_s (H: Sheet f) (A : Rail c f)(ht : Chiral (chirality f) H)(h : A*chirality f=chirality c*A): Chiral (chirality c) (1-A*H⁻¹*Aᴴ):=by
  let P:= chirality f; let S:= chirality c
  have hP (n:Side): (chirality n)∈unitary _:= ⟨by simp [chi_star,chi_sq],by simp [chi_star,chi_sq]⟩
  have he: star (H⁻¹)=aura P (H⁻¹):=by
    have hx : (star H)⁻¹=star (H⁻¹):=(Matrix.conjTranspose_nonsing_inv H).symm
    rw [← hx,invert_W _ _ (hP f)]; unfold aura; rw [show star P=P from chi_star]; exact congr_arg Inv.inv ht
  have hT: S*A*star P=A:=by rw [show star P=P from chi_star,← h, Matrix.mul_assoc,show P*P=1 from chi_sq,Matrix.mul_one]
  have hz:= momentum H P S A (hP _) (hP _)
  change star _= S*(1-A*_ *Aᴴ)*S
  rw [show S*_ * S=aura S (1-A*H⁻¹*Aᴴ) by unfold aura; rw [show star S=S from chi_star]]
  have hh:=hz.2; rw [hT, ← invert_W P _ (hP f),← he] at hh; rw [hh]; simp [Matrix.star_eq_conjTranspose,Matrix.mul_assoc]
variable {D:Grid f→Sheet f}
lemma newborn_s (U : Grid f)(hf : newborn f (D U)=D U): newborn c (shiftL P h B D U) = shiftL P h B D U:=by
  have ht : Chiral (chirality f) (D U):= (funds0 _).mp hf
  have hh := ticketStar B P h 0 U
  have hi : Chiral (chirality f) (shiftH P h B D U):=by unfold shiftH Chiral; rw [star_add, ht, hh,mul_add,add_mul]
  exact (funds0 _).2 (chir_s _ _ hi (tiedSpin ..))
lemma shiftK (D:Grid f→Sheet f)(hk:∀ U k,D (Lattice.gauge k U)=aura (siteRot k) (D U))(x: Grid f)(p:Frame f):
    shiftL P h B D (Lattice.gauge p x) = aura (siteRot (p∘(r).embed)) (shiftL P h B D x):=by
  set T:=siteRot (p∘(r).embed); have hp:=momentum (shiftH P h B D x) (siteRot p) T (Q x) (siteRot_u _) (siteRot_u _)
  have hm: shiftH P h B D (Lattice.gauge p x)=aura (siteRot p) (shiftH P h B D x):=by unfold shiftH vaultF; rw [orbital,gauges,hk x p,aura_add,aura_add]; rw [hp.1]; rfl
  unfold shiftL; rw [hm,gauges]; exact hp.2.symm
-- Spin orientation and translation separated
variable {t:Signed} {g:Site f→ℂ}{d: Spike}
lemma orientK (D:Grid f→Sheet f)(x: Grid f)(p:Site c)(hp:Glare t 0 0 ((r).embed p) g)(hs:Swing t d)(hu:D (pull t ((r).embed p) x)=aura (hues ((r).embed p) t g d) (D x)):
    shiftL P h B D (pull t ((r).embed p) x)=aura (hues p t (g∘(r).embed) d) (shiftL P h B D x):=by
  have he : (r).embed 0=0:= map_zero (r).root
  have hm:Glare t ((r).embed 0) ((r).embed 0) ((r).embed p) g:=by simp_rw [he]; exact hp
  have hL:=momentum (shiftH P h B D x) (hues ((r).embed p) t g d) (hues p t (g∘(r).embed) d) (Q x) (colour_wheel (shrouds r hm) hs) (colour_wheel hp hs)
  have ht:=dual P h hm hs x
  have hv:=spin_vault P h hm hs x B
  -- zeta reduce
  dsimp only at ht hv hL; rw [he] at ht hv; unfold shiftL shiftH; rw [ht,hv,hu,← aura_add]; exact hL.2.symm
end YM.QCD.Orbit
