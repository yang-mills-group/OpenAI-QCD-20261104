import YM.Massive.Lining.Oars
/-! # The cylinder insertion: sampling matrix algebra and spin/color/gauge covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining
open QCD QCD.Lat Lattice Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker
open Purl Scan Boat Cylinder
local notation "K" => starRingEnd ℂ
variable {H:Source.Hol su}{d h:ℕ}(A: Kedge H d h)(t:Finset Cover)(U:Land)(s:Signed)

def emboss (x:Multi d)(i:t) : Bundle:= (sample x i.val:ℂ) • Lat.touch (A.T i.val U)
def start : Whorl (Multi d) t:=nacre (emboss A t U)
def Parade := ∀ s:Signed,t.image s.act=t
namespace Parade
variable {t}(ht:Parade t)
include ht
def frame : ↥t ≃ ↥t where
   toFun x:=⟨s.act x.val,by have h:s.act x.val∈t.image s.act:= mem_image_of_mem _ x.property; rwa [ht s] at h⟩
   invFun x:=⟨s⁻¹.act x.val,by have h:s⁻¹.act x.val∈t.image s⁻¹.act:= mem_image_of_mem _ x.property; rwa [ht s⁻¹] at h⟩
   left_inv x:= Subtype.ext (Signed.inv_act s x.val)
   right_inv x:=Subtype.ext (Signed.act_inv s x.val)
def spinT (M:Spike): Whorl t t:= spar (⇑(frame s ht)) (fun _=> wave M)
lemma frame_unit : frame 1 ht=Equiv.refl _:=by ext1 i; exact Subtype.ext (Signed.act_one _)
lemma frame_back (i:t): (frame s⁻¹ ht) i = (frame s ht).symm i:=rfl
lemma spinT_unit (M:Spike) : spinT 1 ht M = spar id (fun _=> wave M):=by rw [spinT,frame_unit]; rfl
lemma frame_at (i:t): (ht.frame s i).val=s.act i.val:= rfl
end Parade
variable {t}
lemma ink_pin (p:EuPin)(hp:p.Lifts s)(M: Spike) : turned (d:=d) p (wave M)=spar (hem s) (fun x=> (marked s x:ℂ) • wave M):=by
    ext i j; simp only [spar_intro, UV.turned, Matrix.of_apply,readHem _ _ _ hp, Matrix.smul_apply, smul_eq_mul]; by_cases hh:i.2=j.2 <;> by_cases he:hem s i.1.1=j.1.1 <;> simp [hh,he]
lemma mark_emboss (ht:Parade t)(p:Multi d)(x:t): emboss A t U (hem s p) ((ht.frame s) x)=(marked s p:ℂ) • emboss A t (scene s U) p x:=by
   unfold emboss; rw [ht.frame_at, parcel, A.pin, Complex.ofReal_mul, mul_smul]
lemma glow (p: Multi d) (i:t)(S:Spike) : Commute (wave S) (emboss A t U p i) := (Commute.smul_right (interlace (A.T i.val U) S).symm (sample p i.val:ℂ)) -- argument order
lemma mobile (ht:Parade t)(p:EuPin)(h:p.Lifts s)(M:Spike):
    start A t (scene s U)*ht.spinT s M = UV.turned p (wave M)*start A t U:=by
    unfold start Parade.spinT; rw [spar_after,ink_pin s p h, spar_mul]; congr 1; funext i j; obtain ⟨x,rfl⟩:= (ht.frame s).surjective j; rw [mark_emboss, Matrix.mul_smul, Matrix.smul_mul,smul_smul, ← Complex.ofReal_mul, PurlM, Complex.ofReal_one, one_smul]; rw [(glow A (scene s U) i x M).eq]; simp -- symm_apply
  where PurlM (i:Multi d) : marked s i*marked s i=1:=marked_sq .. -- issue d shadow
lemma mobile_star (ht:Parade t)(p:EuPin)(hp:p.Lifts s)(M:Spike):
    Mstar (start A t (scene s U))*ht.spinT s M = UV.turned p (wave M)*Mstar (start A t U):=by
   -- easiest from charge transformation of U; define direct conj matrix.Mobile theorem duplicate using night covariance
   have he(U:Land): start A t (night U)= Mstar (start A t U):=by
       unfold start; rw [mark_star]; congr 1; funext i x; unfold emboss; rw [A.charge,mstar_smul,mstar_touch]; simp
   rw [← he,← he, night_scene,mobile A (night U) _ ht p hp]
lemma charges (t:Finset Cover): start A t (night U) = Mstar (start A t U):=by
   unfold start; rw [mark_star]; congr 1; funext i x; unfold emboss; rw [A.charge,mstar_smul,mstar_touch]; simp

variable (t) (k:Cover→su.El)
def siteWard (k:Cover→su.El): Whorl t t:=spar id (fun x=> touch (Lat.colour (k x.val)))
lemma eye_color (u:su.El): colorTable (d:=d) u= spar id (fun _=> touch (Lat.colour u)):=by ext i j; unfold colorTable; rw [spar_intro,Matrix.of_apply]; simp [and_comm]
lemma paid (p:Multi d)(x:t): emboss A t (gaugeF k U) p x * touch (Lat.colour (k x.val)) = touch (Lat.colour (k 0))* emboss A t U p x:=by
   unfold emboss; rw [A.gauge, Matrix.smul_mul,Matrix.mul_smul, Lat.touch_mul, Lat.touch_mul, Matrix.mul_assoc _ (star _), starcolour,mul_one]
lemma gauging : start A t (gaugeF k U)* siteWard t k=colorTable (k 0)* start A t U:=by
   unfold start siteWard; rw [eye_color, spar_mul]; change nacre _* spar (⇑(Equiv.refl _)) _=_; rw [spar_after]; congr 1; funext i x; exact paid A t U k i x -- order?
end YM.Massive.Lining
#print axioms YM.Massive.Lining.mobile_star
