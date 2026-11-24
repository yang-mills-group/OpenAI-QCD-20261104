import YM.Roan.Rune
import YM.Roan.Tweed
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
local notation "I"=> Axis × Axis
open LinearMap Submodule
variable (V:I→ K.W)
local notation "B"=> (obσ 1 K)
local notation "pC"=> (B).range
local notation "T₀"=> tepid P K
include hf
open Stair Tawny Tawny.Cast TableT
variable (hD: (swingE K 1).range=(bits K).range)(hμ: Module.finrank ℂ (obσ 1 K).range=22)(hV:Module.finrank ℂ (bits K).range=20)
omit hf hp hP hφ HQ F
lemma outsideZ {V:Type}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V](U:Submodule ℂ V)(x:V)(hx:x≠0)(hz:x∈ U) (h:Module.finrank ℂ U=2): ∃ y∈U, y∉ span ℂ {x}:=by
        have he:¬U≤ span ℂ {x}:=fun H=>by have ht:= Submodule.finrank_mono H; rw [h,finrank_span_singleton hx] at ht; omega
        by_contra! ht; exact he ht -- `∀x` works?
local notation "X"=> B
include hf hp hP hφ HQ F
lemma glow2 (i j:Axis) : T₀ (i,j)=(if i=j then lampU P K else 0):=rfl
local notation "J_" p:arg => ((signT (Signed.mirror a) (Prod.fst p)*signT (Signed.mirror a) (Prod.snd p):ℝ):ℂ)
-- antilinear involution on images. 
lemma ray_add (x y:I→K.W): roseC F a (x+y)=roseC F a x+roseC F a y:=by
        ext i; cases i; simp only[roseC,map_add,Pi.add_apply,smul_add]; first|rw[map_add,smul_add]|done -- Field coercion.
lemma ray_smul (z:ℂ)(x:I→K.W): roseC F a (z • x)=star z • (roseC F a x):=by
        ext i; cases i; simp only[roseC,Pi.smul_apply,map_smulₛₗ]; exact smul_comm ..
lemma ray_pure(x:I→K.W) : roseC F a (roseC F a x)=x:=by
        funext i; let J:=(J_ i); unfold roseC; change J • F.adj a (J • F.adj a (x i))=_; rw [map_smulₛₗ,show starRingEnd ℂ J=J from Complex.conj_ofReal _,F.reflex HQ.h a,smul_smul,show J*J=1 from ?_,one_smul]; unfold J; rw [← Complex.ofReal_mul]; exact (congr_arg Complex.ofReal ((crow 1).w (Signed.mirror a) i)).trans Complex.ofReal_one
include hD hμ hV
variable (Xv: ↥((obσ 1 K).range))(hX:Xv.val= tepid P K)
local notation "Kx"=> lakes K
include hX
lemma open_ζ :∃ T: ↥((obσ 1 K).range), T∈ (bank K).ker∧ (∀ a:Axis, roseC F a T.val=T.val)∧ T ∉ span ℂ {Xv}:=by
       let p:= T₀; haveI:FiniteDimensional ℂ ((obσ 1 K).range):= Module.Finite.range _; have hk : Xv ≠0:=by intro hx; rw [hx] at hX; exact bornU hp hP hφ F hf HQ hX.symm
       obtain ⟨y,hy,hQ⟩:=unit_k hp hP hφ F hf HQ; have hz : Xv∈ (bank K).ker:=(Subtype.ext (hy.trans hX.symm): y=Xv) ▸ hQ
       have htK:= banks hp hP hφ F hf HQ hD hμ hV; obtain ⟨Yv,hY,hh⟩:=outsideZ Kx Xv hk hz htK
       let a:= (0:Axis); let Y':= roseC F a Yv.val; let X':pC:=⟨Y', lensS hp hP hφ F hf HQ Yv a⟩; have h:Y'=X'.val:=rfl; have ht : X' ∈ Kx:= lensD hp hP hφ F hf HQ a Yv hY X' rfl; let q₀:= Yv+X'; let q₁:= Complex.I • (Yv-X')
       have hR₀ : ∀ b:Axis, roseC F b q₀.val=q₀.val:=by
           intro b; rw [lensR hp hP hφ F hf HQ _ b a] -- arguments inspect
           change roseC F a (Yv.val+X'.val)=Yv.val+X'.val; rw [ray_add hp hP hφ F hf HQ, show roseC F a Yv.val=X'.val from rfl, show roseC F a X'.val=Yv.val from ray_pure hp hP hφ F hf HQ a _, add_comm]
       have hR₁ : ∀ b:Axis, roseC F b q₁.val=q₁.val:=by
           intro b; rw [lensR hp hP hφ F hf HQ _ b a]; change roseC F a ((Complex.I) • (Yv.val-X'.val))= (Complex.I) • (Yv.val-X'.val); rw [ray_smul hp hP hφ F hf HQ, show roseC F a (Yv.val-X'.val)= X'.val-Yv.val from ?_, show X'.val-Yv.val = -(Yv.val-X'.val) from (by abel),show star Complex.I= -Complex.I from Complex.conj_I,neg_smul,smul_neg,neg_neg] -- ???
           rw [sub_eq_add_neg,←neg_one_smul ℂ X'.val, ray_add hp hP hφ F hf HQ, ray_smul hp hP hφ F hf HQ, show star (-1:ℂ)= -1 from (by simp),neg_one_smul, show roseC F a _=_ from ray_pure hp hP hφ F hf HQ a Yv.val]; change _=_; exact (sub_eq_add_neg ..).symm
       let p:=span ℂ {Xv}; by_cases he:q₀∈p
       · refine ⟨q₁,(Kx).smul_mem _ ((Kx).sub_mem hY ht),hR₁,?_⟩; intro h₁; have H: (2:ℂ) • Yv=q₀+(- Complex.I) • q₁:=by
                unfold q₀ q₁; rw[smul_smul, neg_mul, Complex.I_mul_I,neg_neg,one_smul,two_smul]; abel
         refine hh ?_; have hp: (2:ℂ) • Yv∈ p:= H.symm ▸ p.add_mem he (p.smul_mem _ h₁); exact ((p.smul_mem_iff (by norm_num : (2:ℂ) ≠0)).mp hp)
       exact ⟨q₀,(Kx).add_mem hY ht,hR₀,he⟩
-- abstract result.SemiLink.
omit hD hμ hV hX
-- signatures h_e sign.c need uncurr min
structure Persona (V:I→K.W): Prop where
     tense:Tense F V
     div: divR K V=0
     real'a: ∀ a:Axis, roseC F a V=V
     non:∀ z:ℂ,V≠ z • tepid P K
#print Persona
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.open_ζ
