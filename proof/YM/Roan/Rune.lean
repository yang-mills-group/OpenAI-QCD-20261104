import YM.Roan.Watt
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
noncomputable abbrev tepid (P:Calibration C)(K:Choir) : I → K.W:= fun i => if i.1=i.2 then lampU P K else 0
noncomputable abbrev bank(C:Choir):= (divR C).domRestrict ((obσ 1 C).range)
noncomputable abbrev lakes(C:Choir):= (bank C).ker
local notation "pC"=> (B).range
local notation "T₀"=> tepid P K
include hf
open Stair Tawny Tawny.Cast TableT
variable (hD: (swingE K 1).range=(bits K).range)(hμ: Module.finrank ℂ (obσ 1 K).range=22)(hV:Module.finrank ℂ (bits K).range=20)
lemma tide (x:pC) (i:Axis): (bank K) x i =∑ a:Axis,K.arc a (x.val (a,i)):=by unfold bank divR; rw [domRestrict_apply,LinearMap.pi_apply,LinearMap.sum_apply]; rfl
lemma ownsU : T₀∈ pC:= ⟨_,identityR F hf⟩
lemma unit_k : ∃ X:pC,X.val=T₀ ∧ X∈(bank K).ker:=by
       let X:pC:=⟨_,ownsU hp hP hφ F hf HQ⟩; refine ⟨X,rfl,funext fun i=>?_⟩; rw [(tide hp hP hφ F hf HQ X i)]; change (∑ a:Axis, (K.arc a) ((if a=i then _ else _):K.W))=0; refine sum_eq_zero fun j _=>?_ ; split; exact k_zero hp hP hφ F hf HQ j; exact map_zero _
lemma lamp_h(v:Points 1): v∈conf 1:=fun i j _=> Subsingleton.elim ..
lemma readU: (K.total 1 (points (![0]))) (![lampU P K])=1:=by
       change (K.total 1 (points ![0])) (Fin.cons (lampU P K) Matrix.vecEmpty)=1 ; rw [show S 1 _ _= _ from hf.functor 0 (points (![0])) (lamp_h hp hP hφ F hf HQ _) (Matrix.vecEmpty)]; convert hf.empty using 2; · apply congrArg _ (Subsingleton.elim (Points.tail (points (![0]))) 0)
lemma bornU: T₀ ≠0:=by
       intro hx; let m:= lampU P K; have h1: m=0:=by have h:= congr_fun hx ((0:Axis),(0:Axis)); unfold tepid at h; rw [if_pos rfl] at h; exact h -- a0 fix
       have h:=readU hp hP hφ F hf HQ; change S 1 _ (![m])=1 at h; rw [h1,(S 1 _).map_coord_zero 0 (by rfl)] at h; exact zero_ne_one h
include hD hμ hV
lemma banks : Module.finrank ℂ (lakes K)=2:=by
        haveI : FiniteDimensional ℂ ↥pC :=Module.Finite.range _; have h: (bank K).range=(bits K).range:=by
            rw[← hD]; apply Submodule.ext; intro x; constructor
            · rintro ⟨⟨y,h⟩,rfl⟩; obtain ⟨t,rfl⟩:=h; exact ⟨_,(show swingE K 1 t=_ from rfl)⟩
            rintro ⟨t,rfl⟩; exact ⟨⟨B t, LinearMap.mem_range_self ..⟩,rfl⟩
        have hp:= LinearMap.finrank_range_add_finrank_ker (bank K); rw [h,hV,hμ] at hp; change Module.finrank ℂ ↥((bank K).ker)=_; omega
omit hD hμ hV
lemma lensR (x:pC) (a b:Axis): roseC F a x.val= roseC F b x.val:=by
      obtain ⟨t,h⟩:= x.property; obtain ⟨⟨u,v⟩,rfl⟩:= (bona.1).2 t; rw [←h,tone_a,tone_a]
lemma lensS (x:pC): ∀ a:Axis, roseC F a x.val∈ pC:=by intro a; obtain ⟨t,h⟩:=x.property; obtain ⟨⟨u,v⟩,rfl⟩:=bona.1.2 t; rw [←h,tone_a]; exact LinearMap.mem_range_self ..
lemma lensD (x:pC) (he:x∈ lakes K)(z:pC)(hh:z.val=roseC F a x.val): z∈ lakes K:=by
        let r(i:Axis):ℂ:=signT (Signed.mirror a) i; let y:= F.adj a; change bank K z = _; funext i; rw[tide hp hP hφ F hf HQ]; have hx: (∑ j:Axis,K.arc j (x.val (j,i)))=0:= by rw[← tide hp hP hφ F hf HQ]; exact congr_fun (show bank K x=0 from he) i
        change (∑ j:Axis,_)=0; rw [show (∑ j:Axis, _)=r i • y (∑ j:Axis,K.arc j (x.val (j,i))) from ?_,hx,map_zero,smul_zero]; rw[map_sum,smul_sum]; refine sum_congr rfl fun j _=>?_; rw[hh]; change K.arc j (((↑(signT (Signed.mirror a) j*signT (Signed.mirror a) i:ℝ)):ℂ) •F.adj a (x.val (j,i)))= _; rw [Complex.ofReal_mul,map_smul,show y _= _ from tint_deriv hp hP hφ F HQ j a (x.val (j,i)), smul_smul, mul_comm ] -- orientation comm direction
lemma lensL (x:pC)(h:x.val = roseC F a x.val)(b:Axis)(i:I):F.adj b (x.val i)= ((↑(signT (Signed.mirror b) i.1*signT (Signed.mirror b) i.2:ℝ)):ℂ) • x.val i:=by
       rw [lensR hp hP hφ F hf HQ _ a b] at h; nth_rw 2[h]; -- issue replaces x everywhere incl? use h at coordinate eq
       let z:ℝ:=signT (Signed.mirror b) i.1*signT (Signed.mirror b) i.2; change _=(z:ℂ) • ( (z:ℂ) • F.adj b (x.val i)); rw [smul_smul,← Complex.ofReal_mul, show z*z=1 from (crow 1).w (Signed.mirror b) i,Complex.ofReal_one,one_smul]
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.lensD
#print axioms YM.Massive.Tarn.ChargeQ.banks
