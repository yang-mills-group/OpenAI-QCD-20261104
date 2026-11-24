import YM.Roan.Regal
import YM.Rill.Comes
import YM.Roan.Salt
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Tarn.ChargeQ
open Function Set Filter
open Lattice Wilson QCD QCD.Lat
open UV Patria Patria.Depth Patria.Hub Poised Poised.Plans Poised.Plans.Stamp
open Choir Choir.Strip Quilt Massive.Patria.Gall Massive.Patria.Gall.Onyx
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix.Norms.Frobenius InnerProductSpace
variable {C:Sequence}{P:Calibration C}{K:Choir}{φ:ℕ→ℕ}{β e:ℝ}(hp:C.Path β e)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable (F:Pollens P K)(hf:Foil P K F)(HQ:K.Harmony P φ)
variable (x y:E4)(a b:Axis)
local notation "S"=> K.total
include hp hP hφ HQ F
open Finset
variable (v w: K.W)
-- semantic equivalence of physical tensor families and pre-Candidate.
omit hp hP hφ HQ F
open LinearMap Submodule Patria.Rolls
local notation "I"=> Axis×Axis
local notation "P★"=> obσ 1 K
variable (V W': (Axis× Axis) → K.W)
local notation "Τ"=> (P★).range
local notation "P?"=> divR K
structure Tense (v:(Axis× Axis)→K.W):Prop where
       lv : ∀ i,v i∈ K.level 8
       sym : ∀ i j,v (i,j)=v (j,i)
       parity :∀ i, F.parity (v i)=v i
       charge :∀ i,F.charge (v i)=v i
       flux :∀ k i,F.flavor k (v i)=v i
       geo : ∀ p s,p.Lifts s → ∀ i j,F.spin p (v (i,j))=((signT s i *signT s j:ℝ):ℂ) • v (s.perm i,s.perm j)
variable (hD:∀ d, ∃ n:Lattice.Side,Injective (P.candidate d n 0))
include HQ hP hD
include F
lemma tense : V ∈ (P★).range ↔ Tense F V:=by
       obtain ⟨n,h⟩:= hD 8; let t:=crow 1; obtain ⟨X,hX⟩:= paddle 8 t n hP h
       let U(i:I):= shelS i.1 i.2
       let w(i):= K.focus (U i) 8; change V∈(grab 8 t w).range ↔ _; rw [portrait 8 t (calmP F t 8 U (equalT _) (fun i=>signP _ _)) _ hX]; simp_rw [HQ.h.tops]; constructor
       · rintro ⟨hR,h⟩; refine ⟨h,fun i j=>?_,fun i=>?_,fun i=>?_,fun k i=>?_,fun p s hk i j=>?_⟩
         · have ht : V (i,j)=(1:ℂ) • (V (j,i)):= congr_fun (hR (Sum.inr (.inr (2:Fin 3)))) (j,i); rwa [one_smul] at ht
         · apply Eq.trans (b:=(1:ℂ) • V i) _ (one_smul ..); exact congr_fun (hR (.inr (.inr 0))) i
         · apply Eq.trans (b:=(1:ℂ) • V i) _ (one_smul ..); exact congr_fun (hR (.inr (.inr 1))) i
         · apply Eq.trans (b:=(1:ℂ) • V i) _ (one_smul ..); exact congr_fun (hR (.inl k)) i
         have hT:= congr_fun (hR (.inr (.inl ⟨(p,s),hk⟩))) (t.Q s (i,j)); let α:ℝ:=t.c s (i,j)
         change ((t.c s ((t.Q s).symm _):ℝ):ℂ) • F.spin p (V ((t.Q s).symm _))=(1:ℂ) • V _ at hT; rw[(t.Q s).symm_apply_apply,one_smul] at hT; change _=(α:ℂ) • (V (t.Q s (i,j))); rw[←hT]; unfold α; rw [smul_smul,← Complex.ofReal_mul,t.w,Complex.ofReal_one,one_smul] -- t definition marks etc
       intro h; refine ⟨?_,h.lv⟩; intro i; funext j; rcases i with p|i
       · change F.flavor p _=(1:ℂ) • V _; rw[h.flux,one_smul]
       rcases i with ⟨⟨p,s⟩,he⟩|i
       · obtain ⟨z,rfl⟩:=(t.Q s).surjective j; change (↑(t.c s ((t.Q s).symm _)):ℂ) • F.spin p (V ((t.Q s).symm _))=(1:ℂ) • _; rw[(t.Q s).symm_apply_apply,h.geo p s he (Prod.fst z) (Prod.snd z), smul_smul]; rw [show signT s z.1*signT s z.2=t.c s z from rfl, ←Complex.ofReal_mul,t.w, Complex.ofReal_one]; rfl
       fin_cases i
       · exact (h.parity j).trans (one_smul ℂ _).symm
       · exact (h.charge j).trans (one_smul ℂ _).symm
       exact (h.sym j.2 j.1).trans (one_smul ℂ _).symm
omit HQ hP hD
local notation "τ" x:arg => (signT (Signed.mirror a) x:ℂ)
open Stair Tawny Tawny.Cast Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT
-- antilinear rotation family. act from explicit raw coefficient complex. converts to all involutions with independence.SB.
local notation "μa" i:arg=> ((signT (Signed.mirror a) (Prod.fst i)*signT (Signed.mirror a) (Prod.snd i):ℝ):ℂ)
noncomputable def roseC (a:Axis)(V:I→K.W) (i:I):K.W:= ((↑(signT (Signed.mirror a) i.1*signT (Signed.mirror a) i.2:ℝ)):ℂ) • F.adj a (V i) -- F binder
lemma tone_a (x:Values 4)(t:Fin 4→ℂ):roseC F a ((P★) (poseσ (x,t)))= (P★) (poseσ (star x, star t)):=by
       funext i; let e:= shelS i.1 i.2; change μa i • (F.adj a (K.focus e 8 ((poseσ (x,t)).val i)))= _; rw [F.a,spinTurn i.1 i.2 a, map_smul, smul_smul,Complex.ofReal_mul]; rw [show (τ i.1 *τ i.2) * (τ i.1 *τ i.2)=1 from ?_,one_smul]; rfl
       rw [show (τ i.1*τ i.2)*(τ i.1*τ i.2)= (τ i.1*τ i.1)*(τ i.2*τ i.2) from by ring,mirror_sq,mirror_sq,mul_one]
local notation "Ip"=> fun i : Axis× Axis=> if i.1=i.2 then lampU P K else 0
include hf
lemma identityR : (P★) epi=Ip:=by
        funext i; change K.focus (shelS i.1 i.2) 8 (epi.val i)= _; by_cases h:i.1=i.2; rw [if_pos h,show (epi.val i)= P.sym.unit _ from (?_ ),hf.unit]; apply Subtype.ext; rw [epi_at,if_pos h]; exact P.sym.unitActs _|>.symm -- field
        rw [if_neg h,show epi.val i=0 from ?_, map_zero]; apply Subtype.ext; rw [epi_at,if_neg h]; rfl
omit hf
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.tone_a
#print axioms YM.Massive.Tarn.ChargeQ.tense
