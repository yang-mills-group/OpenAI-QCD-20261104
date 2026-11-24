import YM.Roan.Mess
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
variable (hχ:∀ d,∃ n:Lattice.Side,Injective (P.candidate d n 0))
include hp hP hφ HQ hf F hχ hD hμ hV
lemma estateP:∃ x,Persona F x:=by
       obtain ⟨X,hX,hE⟩:=unit_k hp hP hφ F hf HQ; obtain ⟨T,hv,hK,h⟩:=open_ζ hp hP hφ F hf HQ hD hμ hV X hX
       refine ⟨T.val,(tense hP F HQ T.val hχ).mp T.property,hv,hK,fun i he=>?_⟩; exact h (mem_span_singleton.mpr ⟨i,Subtype.ext ((show (i • X).val=i • T₀ from congr_arg (fun x:I → K.W=> i • x) hX).trans he.symm)⟩)
variable (T U:(Axis× Axis) → K.W)(hT: Persona F T)
local notation "kC"=> span ℂ 
include hT
lemma chartered : Tense F U ∧ divR K U=0 ↔ ∃ x y:ℂ, U=x • T +y • T₀ :=by
         obtain ⟨X,hX,hE⟩:=unit_k hp hP hφ F hf HQ; let V':pC:=⟨T,(tense hP F HQ T hχ).2 hT.tense⟩; have hQ:V'∈ (bank K).ker:= hT.div
         letI:FiniteDimensional ℂ pC:= Module.Finite.range _; have hs: X ≠0:=by intro hx; rw[hx] at hX; exact bornU hp hP hφ F hf HQ hX.symm
         let U':=span ℂ {X}; let L:=U'⊔span ℂ {V'}; have hv:V'∉ U':=by intro h; obtain ⟨k,hk⟩:=mem_span_singleton.mp h; exact hT.non k ((congr_arg Subtype.val hk).symm.trans (congr_arg (fun i=> k • i) hX))
         have he:L=lakes K:=Submodule.eq_of_le_of_finrank_le (sup_le (span_le.mpr (by intro i h; cases (mem_singleton_iff.mp h); exact hE)) (span_le.mpr (by intro i h; cases (mem_singleton_iff.mp h); exact hQ))) ((banks hp hP hφ F hf HQ hD hμ hV).le.trans (show 2 ≤ Module.finrank ℂ L from (by unfold L; rw[finrank_sup_span_singleton hv]; unfold U'; rw [finrank_span_singleton hs]))) -- names.Module.
         constructor
         · rintro ⟨hz,hy⟩; let Z:pC:=⟨U,(tense hP F HQ U hχ).2 hz⟩; have h: Z∈ L:= he.symm ▸ (show Z∈ lakes K from hy); obtain ⟨x,hx,y,hy,h⟩:= mem_sup.mp h; obtain ⟨x,rfl⟩:= mem_span_singleton.mp hx; obtain ⟨y,rfl⟩:= mem_span_singleton.mp hy; refine ⟨y,x,?_⟩; rw[←hX]; change Z.val=_; apply Eq.trans (congr_arg Subtype.val h).symm; change x • _+ _= _; exact add_comm ..
         rintro ⟨x,y,rfl⟩; rw[←hX]; let R:= x • V'+y • X; have hv:(R).val=x • T+y • X.val:=rfl; rw[←hv]; exact ⟨(tense hP F HQ R.val hχ).mp R.property, (show R∈lakes K from (lakes K).add_mem ((lakes K).smul_mem x hQ) ((lakes K).smul_mem _ hE))⟩
omit hp hP hφ HQ hf F hχ hD hμ hV hT
-- compar Candidate once Lie constructed.
variable (L:EuPin →* (K.W ≃ₗ[ℂ] K.W))(A:Ortho.Skew→ K.W→ₗ[ℂ] K.W)
variable (hB:∀ p:EuPin,∀ s:Signed,p.Lifts s → L p= F.spin p)
include F hB
local notation "Kf"=> equip F L A
lemma EuM_w (i j:Axis)(p:EuPin)(s:Signed)(h:p.Lifts s): (∑ a: Axis,∑ b:Axis,(↑(p.coord.val a i * p.coord.val b j):ℂ) • T (a,b)) = ((signT s i*signT s j:ℝ):ℂ) • T (s.perm i,s.perm j):=by
       rw[sum_eq_single (s.perm i)]; · 
          rw[sum_eq_single (s.perm j)]; · rw [show p.coord=s.ortho from h]; unfold Signed.ortho; simp only[Signed.matrix_at,↓reduceIte]; rfl
          · intro i' _ ht; rw[show p.coord=s.ortho from h]; unfold Signed.ortho; simp only[Signed.matrix_at, if_neg (Ne.symm ht),mul_zero,Complex.ofReal_zero,zero_smul]
          simp
       · intro k _ he; apply sum_eq_zero; intro i' _; rw [show p.coord=s.ortho from h]; unfold Signed.ortho; simp [Signed.matrix_at, Ne.symm he] -- Lifts notation?
       simp
lemma constituted : Physics.Candidate Kf (fun i j=>T (i,j)) ↔ (Tense F T ∧divR K T=0):=by
         constructor
         · intro H'; refine ⟨⟨fun ⟨i,j⟩=>H'.level i j,fun i j=>H'.symmetric i j,fun ⟨i,j⟩=> H'.parity i j,fun ⟨i,j⟩=> H'.charge i j,fun k ⟨i,j⟩=> H'.neutral i j k,fun p s he i j=>?_⟩,?_⟩
           · have h : L p (T (i,j))=_:= H'.orientations p ⟨_,he⟩ i j; rw[hB p s he] at h; exact h.trans (EuM_w F T L hB i j p s he) -- instances
           · funext i; change _=0; rw[divR,LinearMap.pi_apply,LinearMap.sum_apply]; exact H'.conserved i
         rintro ⟨h,hX⟩; refine ⟨fun i j=> h.lv _,h.sym,fun a b=> h.parity _,fun i j=> h.charge _,fun i j k=> h.flux k _,?_,?_⟩
         · intro p ht; obtain ⟨s,h'⟩:= ht; intro i j; change L p (T (i,j))=_; rw [hB p s h',h.geo p s h']; exact (EuM_w F T L hB i j p s h').symm
         · intro i; have h:=congr_fun hX i; unfold divR at h; rw[LinearMap.pi_apply,LinearMap.sum_apply] at h; exact h
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.chartered
#print axioms YM.Massive.Tarn.ChargeQ.estateP
#print axioms YM.Massive.Tarn.ChargeQ.constituted
